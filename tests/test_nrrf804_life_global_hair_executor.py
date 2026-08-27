import json
import shutil
import socket
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from experiments import nrrf804_life_global_hair_executor as executor


ROOT = Path(__file__).parents[1]
SOURCE_RUN = ROOT / "runs/nrrf767_live_paper_trading_bot/bitstamp_public_20260826T0221Z"
COST_OVERLAY = ROOT / "runs/nrrf780_local_price_global_cost_equality/bitstamp_public_20260826T0221Z"
PHASE_OVERLAY = ROOT / "runs/nrrf801_black_mirror_market_phase/bitstamp_public_20260826T0221Z"


def read_events(root: Path) -> list[dict[str, object]]:
    return [json.loads(line) for line in (root / "events.jsonl").read_text().splitlines()]


class LifeGlobalHairExecutorTest(unittest.TestCase):
    def create(self, output: Path) -> dict[str, object]:
        return executor.create_overlay(COST_OVERLAY, PHASE_OVERLAY, SOURCE_RUN, output)

    def test_deterministic_and_verifies_without_network(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            first = Path(directory) / "first"
            second = Path(directory) / "second"
            self.create(first)
            self.create(second)
            for name in ("events.jsonl", "summary.json", "manifest.json"):
                self.assertEqual((first / name).read_bytes(), (second / name).read_bytes())
            with mock.patch.object(socket, "socket", side_effect=AssertionError("network forbidden")):
                result = executor.verify_overlay(COST_OVERLAY, PHASE_OVERLAY, SOURCE_RUN, first)
            self.assertTrue(result["verified"])

    def test_global_hair_identity_and_locked_verdicts(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "run"
            summary = self.create(output)["summary"]
            self.assertEqual(summary["rounds"], 12)
            self.assertEqual(summary["records"], 72)
            self.assertEqual(
                summary["verdicts"],
                {"HOLD_GLOBAL_HAIR": 10, "HOLD_LIFE_OPEN": 56, "OPEN": 6},
            )
            self.assertEqual(summary["paper_actions_selected"], 0)
            self.assertTrue(summary["all_numeric_records_close"])
            self.assertEqual(summary["orders_submitted"], 0)
            for event in read_events(output):
                for record in event["records"]:
                    self.assertFalse(record["live_order_authorized"])

    def test_only_closed_life_can_reach_the_hair_comparison(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "run"
            self.create(output)
            for event in read_events(output):
                for record in event["records"]:
                    if record["verdict"] == "HOLD_GLOBAL_HAIR":
                        self.assertEqual(record["life_phase_state"], "MIRROR_COHERENT")
                    if record["life_phase_state"] == "CONTRADICTED":
                        self.assertEqual(record["verdict"], "HOLD_LIFE_OPEN")

    def test_semantically_rehashed_forgery_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            original = Path(directory) / "original"
            forged = Path(directory) / "forged"
            self.create(original)
            shutil.copytree(original, forged)
            manifest_path = forged / "manifest.json"
            manifest = json.loads(manifest_path.read_text())
            events = read_events(forged)
            events[0]["records"][0]["verdict"] = "ACT"
            previous = manifest["genesis_hash"]
            for event in events:
                event["previous_event_hash"] = previous
                event.pop("event_hash", None)
                event["event_hash"] = executor.sha256_bytes(executor.canonical_json_bytes(event))
                previous = event["event_hash"]
            ledger = b"".join(executor.canonical_json_bytes(event) + b"\n" for event in events)
            (forged / "events.jsonl").write_bytes(ledger)
            manifest["events_sha256"] = executor.sha256_bytes(ledger)
            manifest["final_event_hash"] = previous
            manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
            with self.assertRaises(ValueError):
                executor.verify_overlay(COST_OVERLAY, PHASE_OVERLAY, SOURCE_RUN, forged)


if __name__ == "__main__":
    unittest.main()
