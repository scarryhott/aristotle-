import json
import shutil
import socket
import tempfile
import unittest
from decimal import Decimal, localcontext
from pathlib import Path
from unittest import mock

from experiments import nrrf805_relativistic_signal_open_command as closure


ROOT = Path(__file__).parents[1]
SOURCE_RUN = ROOT / "runs/nrrf767_live_paper_trading_bot/bitstamp_public_20260826T0221Z"


def read_events(root: Path) -> list[dict[str, object]]:
    return [json.loads(line) for line in (root / "events.jsonl").read_text().splitlines()]


class RelativisticSignalOpenCommandTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.temporary = tempfile.TemporaryDirectory()
        cls.output = Path(cls.temporary.name) / "derived"
        cls.result = closure.create_overlay(SOURCE_RUN, cls.output)

    @classmethod
    def tearDownClass(cls) -> None:
        cls.temporary.cleanup()

    def test_exact_locked_results_and_relative_identity(self) -> None:
        summary = self.result["summary"]
        self.assertEqual(summary["rounds"], 12)
        self.assertEqual(summary["rounds_with_identified_observations"], 11)
        self.assertEqual(summary["derived_candidates"], 143)
        self.assertEqual(summary["positive_candidates"], 0)
        self.assertEqual(summary["unique_positive_relational_signals"], 0)
        self.assertEqual(summary["best_route_id"], "BTC>USD>BTC")
        self.assertEqual(
            summary["best_completed_return_bps"],
            "-49.93876056045305905061517497",
        )
        self.assertTrue(summary["all_relative_identities_close"])
        self.assertEqual(summary["orders_submitted"], 0)

    def test_routes_partitions_and_signals_are_derived_not_supplied_phase(self) -> None:
        fixed_old_notionals = {"100", "1000", "10000"}
        for event in read_events(self.output):
            candidates = event["candidates"]
            if event["command"]["observation_closure"] == "CLOSED":
                self.assertEqual(event["asset_graph"]["simple_closed_routes"], 12)
                self.assertEqual(
                    len({candidate["route_class_id"] for candidate in candidates}),
                    5,
                )
                self.assertEqual(event["command"]["topology_closure"], "RECIPROCAL_CLOSED")
            for candidate in candidates:
                self.assertEqual(candidate["partition_derivation"], closure.PARTITION_DERIVATION)
                self.assertNotIn(candidate["start_amount"], fixed_old_notionals)
                self.assertNotIn("phase", candidate)
                action = Decimal(candidate["action_potential_return"])
                hair = Decimal(candidate["global_hair_return"])
                completed = Decimal(candidate["completed_return"])
                with localcontext() as context:
                    context.prec = closure.ARITHMETIC_PRECISION
                    error = abs(completed - (action - hair))
                self.assertLessEqual(error, closure.IDENTITY_TOLERANCE)

    def test_every_command_stays_open_without_private_authority(self) -> None:
        for event in read_events(self.output):
            command = event["command"]
            self.assertEqual(command["state"], "OPEN")
            self.assertEqual(command["execution_authority_closure"], "OPEN")
            self.assertIn(
                "AUTHENTICATED_PRESENTATION_AND_EXECUTION_AUTHORITY",
                command["missing_closures"],
            )
            self.assertEqual(command["orders_submitted"], 0)

    def test_replay_is_offline_and_rejects_semantically_rehashed_closure(self) -> None:
        with mock.patch.object(socket, "socket", side_effect=AssertionError("network forbidden")):
            verified = closure.verify_overlay(SOURCE_RUN, self.output)
        self.assertTrue(verified["verified"])

        forged = Path(self.temporary.name) / "forged"
        shutil.copytree(self.output, forged)
        manifest_path = forged / "manifest.json"
        manifest = json.loads(manifest_path.read_text())
        events = read_events(forged)
        events[0]["command"]["state"] = "CLOSED"
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
            closure.verify_overlay(SOURCE_RUN, forged)


if __name__ == "__main__":
    unittest.main()
