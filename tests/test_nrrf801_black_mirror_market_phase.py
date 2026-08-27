import json
import shutil
import socket
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from experiments import nrrf801_black_mirror_market_phase as phase


ROOT = Path(__file__).parents[1]
LOCKED_SOURCE_RUN = (
    ROOT / "runs" / "nrrf767_live_paper_trading_bot" / "bitstamp_public_20260826T0221Z"
)
LOCKED_PRICE_OVERLAY = (
    ROOT
    / "runs"
    / "nrrf780_local_price_global_cost_equality"
    / "bitstamp_public_20260826T0221Z"
)


def read_events(root: Path) -> list[dict[str, object]]:
    return [json.loads(line) for line in (root / "events.jsonl").read_text().splitlines()]


class BlackMirrorMarketPhaseTest(unittest.TestCase):
    def create(self, output: Path) -> dict[str, object]:
        return phase.create_overlay(LOCKED_PRICE_OVERLAY, LOCKED_SOURCE_RUN, output)

    def test_overlay_is_deterministic_and_verifies_without_network(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            first = Path(directory) / "first"
            second = Path(directory) / "second"
            self.create(first)
            self.create(second)
            for name in ("events.jsonl", "summary.json", "manifest.json"):
                self.assertEqual((first / name).read_bytes(), (second / name).read_bytes())
            with mock.patch.object(socket, "socket", side_effect=AssertionError("network forbidden")):
                verified = phase.verify_overlay(
                    LOCKED_PRICE_OVERLAY, LOCKED_SOURCE_RUN, first
                )
            self.assertTrue(verified["verified"])
            self.assertEqual(verified["event_count"], 12)
            self.assertEqual(verified["phase_pairs"], 36)

    def test_phase_is_derived_only_from_the_local_price_relation(self) -> None:
        self.assertEqual(phase.phase_from_local_ratio("1.01"), 1)
        self.assertEqual(phase.phase_from_local_ratio("1"), 0)
        self.assertEqual(phase.phase_from_local_ratio("0.99"), 3)
        with tempfile.TemporaryDirectory() as directory:
            overlay = Path(directory) / "overlay"
            self.create(overlay)
            pairs = [pair for event in read_events(overlay) for pair in event["phase_pairs"]]
            for pair in pairs:
                self.assertTrue(pair["phase_derived_from_local_price_only"])
                if pair["state"] == "OPEN":
                    self.assertIsNone(pair["plus_phase"])
                    self.assertIsNone(pair["minus_phase"])
                else:
                    self.assertEqual(
                        pair["plus_phase"],
                        phase.phase_from_local_ratio(pair["plus_local_price_ratio"]),
                    )
                    self.assertEqual(
                        pair["minus_phase"],
                        phase.phase_from_local_ratio(pair["minus_local_price_ratio"]),
                    )

    def test_locked_data_reports_gaps_instead_of_manufacturing_closure(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            overlay = Path(directory) / "overlay"
            result = self.create(overlay)
            summary = result["summary"]
            self.assertEqual(summary["phase_pairs"], 36)
            self.assertEqual(
                summary["pair_states"],
                {"CONTRADICTED": 28, "MIRROR_COHERENT": 5, "OPEN": 3},
            )
            self.assertEqual(summary["observed_phase_values"], [1, 3])
            self.assertFalse(summary["full_ball_coverage"])
            self.assertFalse(summary["all_pairs_mirror_coherent"])
            self.assertFalse(summary["one_to_one_continuity_admitted"])
            self.assertFalse(summary["prediction_admitted"])
            self.assertEqual(summary["orders_submitted"], 0)
            self.assertEqual(summary["authenticated_fills"], 0)

    def test_semantically_rehashed_phase_forgery_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            original = Path(directory) / "original"
            forged = Path(directory) / "forged"
            self.create(original)
            shutil.copytree(original, forged)
            manifest_path = forged / "manifest.json"
            manifest = json.loads(manifest_path.read_text())
            events = read_events(forged)
            events[0]["phase_pairs"][0]["plus_phase"] = 2
            previous = manifest["genesis_hash"]
            for event in events:
                event["previous_event_hash"] = previous
                event.pop("event_hash", None)
                event["event_hash"] = phase.sha256_bytes(phase.canonical_json_bytes(event))
                previous = event["event_hash"]
            ledger = b"".join(phase.canonical_json_bytes(event) + b"\n" for event in events)
            (forged / "events.jsonl").write_bytes(ledger)
            manifest["events_sha256"] = phase.sha256_bytes(ledger)
            manifest["final_event_hash"] = previous
            manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
            with self.assertRaises(ValueError):
                phase.verify_overlay(LOCKED_PRICE_OVERLAY, LOCKED_SOURCE_RUN, forged)

    def test_nonempty_output_is_never_overwritten(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "overlay"
            self.create(output)
            with self.assertRaises(FileExistsError):
                self.create(output)


if __name__ == "__main__":
    unittest.main()
