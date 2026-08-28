import inspect
import json
import shutil
import socket
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from experiments import nrrf808_executor_reactor_reunification as reunified


ROOT = Path(__file__).parents[1]
OBSERVATION_RUN = ROOT / "runs/nrrf767_live_paper_trading_bot/bitstamp_public_20260826T0221Z"
RELATIVE_RUN = ROOT / "runs/nrrf805_relativistic_signal_open_command/bitstamp_public_20260826T0221Z"
LIFE_RUN = ROOT / "runs/nrrf806_translation_first_life_reactor/bitstamp_public_20260826T0221Z"
INTERACTIVE_RUN = ROOT / "runs/nrrf807_derived_interactive_signal_relations/bitstamp_public_20260826T0221Z"


def read_events(root: Path) -> list[dict[str, object]]:
    return [json.loads(line) for line in (root / "events.jsonl").read_text().splitlines()]


class ExecutorReactorReunificationTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.temporary = tempfile.TemporaryDirectory()
        cls.output = Path(cls.temporary.name) / "reunified"
        cls.result = reunified.create_overlay(
            OBSERVATION_RUN, RELATIVE_RUN, LIFE_RUN, INTERACTIVE_RUN, cls.output
        )

    @classmethod
    def tearDownClass(cls) -> None:
        cls.temporary.cleanup()

    def test_exact_reactor_without_authored_action_result(self) -> None:
        summary = self.result["summary"]
        self.assertEqual(summary["rounds"], 12)
        self.assertEqual(summary["rounds_with_reactor_geometry"], 11)
        self.assertEqual(summary["reciprocal_reactor_fibres"], 33)
        self.assertEqual(summary["reciprocal_presentations"], 66)
        self.assertEqual(summary["universal_executer_zero_readings"], 33)
        self.assertEqual(summary["authored_transactional_actions"], 0)
        self.assertEqual(summary["identified_natural_signal_forms"], 0)
        self.assertEqual(summary["profit_assessments"], 0)
        self.assertEqual(summary["open_reactor_commands"], 12)

    def test_every_fibre_retains_both_presentations_and_selects_neither(self) -> None:
        for event in read_events(self.output):
            self.assertEqual(event["command"]["state"], "OPEN_REACTOR")
            self.assertEqual(event["command"]["authored_turns"], 0)
            self.assertIn(
                "AUTHORED_TRANSACTIONAL_ACTION", event["command"]["missing_translations"]
            )
            for fibre in event["reactor_fibres"]:
                self.assertEqual(len(fibre["presentations"]), 2)
                forward, reverse = fibre["presentations"]
                self.assertEqual(forward["input_asset"], reverse["output_asset"])
                self.assertEqual(forward["output_asset"], reverse["input_asset"])
                self.assertEqual(fibre["global_hair_executer"], "ZERO_UNIVERSAL_NOT_SIGNAL")
                self.assertIsNone(fibre["authored_turn"])
                self.assertIsNone(fibre["identified_natural_form"])
                self.assertIsNone(fibre["profit_assessment"])

    def test_runtime_contains_no_resource_selector(self) -> None:
        source = inspect.getsource(reunified)
        self.assertNotIn("derive_candidates(", source)
        self.assertNotIn("integrate_relative_field(", source)
        self.assertNotIn("completed_return", source)
        self.assertNotIn("max(", source)
        self.assertFalse(reunified.DERIVATION["resource_metric_authors_form"])

    def test_offline_replay_rejects_forged_authored_action(self) -> None:
        with mock.patch.object(socket, "socket", side_effect=AssertionError("network forbidden")):
            verified = reunified.verify_overlay(
                OBSERVATION_RUN,
                RELATIVE_RUN,
                LIFE_RUN,
                INTERACTIVE_RUN,
                self.output,
            )
        self.assertTrue(verified["verified"])

        forged = Path(self.temporary.name) / "forged"
        shutil.copytree(self.output, forged)
        manifest_path = forged / "manifest.json"
        manifest = json.loads(manifest_path.read_text())
        events = read_events(forged)
        fibre = next(fibre for event in events for fibre in event["reactor_fibres"])
        fibre["authored_turn"] = "action"
        fibre["identified_natural_form"] = "forged"
        previous = manifest["genesis_hash"]
        for event in events:
            event["previous_event_hash"] = previous
            event.pop("event_hash", None)
            event["event_hash"] = reunified.sha256_bytes(reunified.canonical_json_bytes(event))
            previous = event["event_hash"]
        ledger = b"".join(reunified.canonical_json_bytes(event) + b"\n" for event in events)
        (forged / "events.jsonl").write_bytes(ledger)
        manifest["events_sha256"] = reunified.sha256_bytes(ledger)
        manifest["final_event_hash"] = previous
        manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
        with self.assertRaises(ValueError):
            reunified.verify_overlay(
                OBSERVATION_RUN, RELATIVE_RUN, LIFE_RUN, INTERACTIVE_RUN, forged
            )


if __name__ == "__main__":
    unittest.main()
