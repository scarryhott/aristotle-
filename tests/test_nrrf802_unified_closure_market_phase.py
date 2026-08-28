import json
import shutil
import socket
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from experiments import nrrf802_unified_closure_market_phase as closure


ROOT = Path(__file__).parents[1]
SOURCE_RUN = ROOT / "runs/nrrf767_live_paper_trading_bot/bitstamp_public_20260826T0221Z"
PRICE_OVERLAY = ROOT / "runs/nrrf780_local_price_global_cost_equality/bitstamp_public_20260826T0221Z"
PHASE_OVERLAY = ROOT / "runs/nrrf801_black_mirror_market_phase/bitstamp_public_20260826T0221Z"


def read_events(root: Path) -> list[dict[str, object]]:
    return [json.loads(line) for line in (root / "events.jsonl").read_text().splitlines()]


class UnifiedClosureMarketPhaseTest(unittest.TestCase):
    def create(self, output: Path) -> dict[str, object]:
        return closure.create_overlay(PHASE_OVERLAY, PRICE_OVERLAY, SOURCE_RUN, output)

    def test_overlay_is_deterministic_and_verifies_without_network(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            first = Path(directory) / "first"
            second = Path(directory) / "second"
            self.create(first)
            self.create(second)
            for name in ("events.jsonl", "summary.json", "manifest.json"):
                self.assertEqual((first / name).read_bytes(), (second / name).read_bytes())
            with mock.patch.object(socket, "socket", side_effect=AssertionError("network forbidden")):
                verified = closure.verify_overlay(PHASE_OVERLAY, PRICE_OVERLAY, SOURCE_RUN, first)
            self.assertTrue(verified["verified"])
            self.assertEqual(verified["event_count"], 12)
            self.assertEqual(verified["closure_pairs"], 36)

    def test_generic_closure_preserves_the_black_mirror_result_exactly(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            overlay = Path(directory) / "overlay"
            result = self.create(overlay)
            summary = result["summary"]
            self.assertEqual(
                summary["closure_states"],
                {"DISTINCT_CLOSURE": 28, "OPEN": 3, "SAME_CLOSURE": 5},
            )
            self.assertTrue(summary["all_source_states_preserved"])
            self.assertFalse(summary["reinterpretation_changed_pair_results"])
            for event in read_events(overlay):
                for pair in event["closure_pairs"]:
                    self.assertTrue(pair["source_state_preserved"])
                    if pair["state"] == "OPEN":
                        self.assertIsNone(pair["actual_closure_reading"])
                    else:
                        self.assertEqual(pair["actual_closure_reading"], pair["plus_phase"] % 4)
                        self.assertEqual(
                            pair["potential_closure_reading"], (-pair["minus_phase"]) % 4
                        )

    def test_two_return_life_collapse_is_not_assumed_for_market_data(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            overlay = Path(directory) / "overlay"
            summary = self.create(overlay)["summary"]
            self.assertFalse(summary["two_return_life_collapse_admitted_for_market"])
            self.assertFalse(summary["prediction_admitted"])
            self.assertEqual(summary["orders_submitted"], 0)
            self.assertEqual(summary["authenticated_fills"], 0)

    def test_semantically_rehashed_closure_forgery_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            original = Path(directory) / "original"
            forged = Path(directory) / "forged"
            self.create(original)
            shutil.copytree(original, forged)
            manifest_path = forged / "manifest.json"
            manifest = json.loads(manifest_path.read_text())
            events = read_events(forged)
            events[0]["closure_pairs"][0]["state"] = "SAME_CLOSURE"
            previous = manifest["genesis_hash"]
            for event in events:
                event["previous_event_hash"] = previous
                event.pop("event_hash", None)
                event["event_hash"] = closure.sha256_bytes(closure.canonical_json_bytes(event))
                previous = event["event_hash"]
            ledger = b"".join(closure.canonical_json_bytes(event) + b"\n" for event in events)
            (forged / "events.jsonl").write_bytes(ledger)
            manifest["events_sha256"] = closure.sha256_bytes(ledger)
            manifest["final_event_hash"] = previous
            manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
            with self.assertRaises(ValueError):
                closure.verify_overlay(PHASE_OVERLAY, PRICE_OVERLAY, SOURCE_RUN, forged)

    def test_nonempty_output_is_never_overwritten(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "overlay"
            self.create(output)
            with self.assertRaises(FileExistsError):
                self.create(output)


if __name__ == "__main__":
    unittest.main()
