import json
import shutil
import socket
import tempfile
import unittest
from decimal import Decimal, localcontext
from pathlib import Path
from unittest import mock

from experiments import nrrf780_local_price_global_cost_equality as completion


ROOT = Path(__file__).parents[1]
LOCKED_SOURCE_RUN = (
    ROOT
    / "runs"
    / "nrrf767_live_paper_trading_bot"
    / "bitstamp_public_20260826T0221Z"
)


def read_events(root: Path) -> list[dict[str, object]]:
    return [json.loads(line) for line in (root / "events.jsonl").read_text().splitlines()]


class LocalPriceGlobalCostEqualityTest(unittest.TestCase):
    def create(self, output: Path) -> dict[str, object]:
        return completion.create_overlay(LOCKED_SOURCE_RUN, output)

    def test_overlay_is_deterministic_and_verifies_without_network(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            first = Path(directory) / "first"
            second = Path(directory) / "second"
            self.create(first)
            self.create(second)
            for name in ("events.jsonl", "summary.json", "manifest.json"):
                self.assertEqual((first / name).read_bytes(), (second / name).read_bytes())
            with mock.patch.object(socket, "socket", side_effect=AssertionError("network forbidden")):
                verified = completion.verify_overlay(first, LOCKED_SOURCE_RUN)
            self.assertTrue(verified["verified"])
            self.assertEqual(verified["event_count"], 12)
            self.assertEqual(verified["numeric_records"], 66)
            self.assertEqual(verified["numeric_signs"], {"NEGATIVE": 66})

    def test_price_is_local_and_cost_is_its_global_completion_equality(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            overlay = Path(directory) / "overlay"
            self.create(overlay)
            records = [item for event in read_events(overlay) for item in event["completions"]]
            numeric = [item for item in records if item["state"] == "COMPLETED_COUNTERFACTUAL"]
            opened = [item for item in records if item["state"] == "OPEN"]
            self.assertEqual(len(records), 72)
            self.assertEqual(len(numeric), 66)
            self.assertEqual(len(opened), 6)
            for item in numeric:
                with localcontext() as context:
                    context.prec = 110
                    local_price = Decimal(item["exit_local_price_ratio"])
                    global_cost_equal = Decimal(item["exit_global_cost_equal_ratio"])
                    completed = Decimal(item["exit_completed_ratio"])
                    self.assertLessEqual(
                        abs(local_price / global_cost_equal - completed),
                        completion.NUMERIC_TOLERANCE,
                    )
                self.assertGreaterEqual(global_cost_equal, 1)
                self.assertEqual(item["entry_local_price_ratio"], "1")
                self.assertEqual(item["entry_global_cost_equal_ratio"], "1")
                self.assertEqual(item["entry_completed_ratio"], "1")
                self.assertTrue(item["numeric_sign_matches_source"])
            for item in opened:
                self.assertIsNone(item["exit_local_price_ratio"])
                self.assertIsNone(item["exit_global_cost_equal_ratio"])
                self.assertIsNone(item["exit_completed_ratio"])
                self.assertIsNone(item["completed_residual_bps"])

    def test_refactor_does_not_relabel_counterfactual_as_profit_or_execution(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            overlay = Path(directory) / "overlay"
            result = self.create(overlay)
            summary = result["summary"]
            self.assertFalse(summary["reinterpretation_changed_numeric_results"])
            self.assertTrue(summary["all_numeric_signs_match_source"])
            self.assertFalse(summary["settled_profit_claimed"])
            self.assertEqual(summary["orders_submitted"], 0)
            self.assertEqual(summary["authenticated_fills"], 0)
            self.assertIsNone(summary["authenticated_settled_pnl_usd"])
            for event in read_events(overlay):
                self.assertEqual(event["boundary"], completion.NO_EXECUTION_BOUNDARY)
                for item in event["completions"]:
                    self.assertEqual(item["boundary"], completion.NO_EXECUTION_BOUNDARY)

    def test_semantically_rehashed_price_cost_forgery_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            original = Path(directory) / "original"
            forged = Path(directory) / "forged"
            self.create(original)
            shutil.copytree(original, forged)
            manifest_path = forged / "manifest.json"
            manifest = json.loads(manifest_path.read_text())
            events = read_events(forged)
            events[0]["completions"][0]["exit_global_cost_equal_ratio"] = "1"
            previous = manifest["genesis_hash"]
            for event in events:
                event["previous_event_hash"] = previous
                event.pop("event_hash", None)
                event["event_hash"] = completion.sha256_bytes(
                    completion.canonical_json_bytes(event)
                )
                previous = event["event_hash"]
            ledger = b"".join(
                completion.canonical_json_bytes(event) + b"\n" for event in events
            )
            (forged / "events.jsonl").write_bytes(ledger)
            manifest["events_sha256"] = completion.sha256_bytes(ledger)
            manifest["final_event_hash"] = previous
            manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
            with self.assertRaises(ValueError):
                completion.verify_overlay(forged, LOCKED_SOURCE_RUN)

    def test_nonempty_output_is_never_overwritten(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "overlay"
            self.create(output)
            with self.assertRaises(FileExistsError):
                self.create(output)


if __name__ == "__main__":
    unittest.main()
