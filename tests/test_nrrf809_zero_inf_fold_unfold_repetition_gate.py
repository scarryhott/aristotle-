import inspect
import json
import shutil
import socket
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from experiments import nrrf809_zero_inf_fold_unfold_repetition_gate as zero_inf


ROOT = Path(__file__).parents[1]
OBSERVATION_RUN = ROOT / "runs/nrrf767_live_paper_trading_bot/bitstamp_public_20260826T0221Z"
RELATIVE_RUN = ROOT / "runs/nrrf805_relativistic_signal_open_command/bitstamp_public_20260826T0221Z"
LIFE_RUN = ROOT / "runs/nrrf806_translation_first_life_reactor/bitstamp_public_20260826T0221Z"
INTERACTIVE_RUN = ROOT / "runs/nrrf807_derived_interactive_signal_relations/bitstamp_public_20260826T0221Z"
REUNIFIED_RUN = ROOT / "runs/nrrf808_executor_reactor_reunification/bitstamp_public_20260826T0221Z"


def read_events(root: Path) -> list[dict[str, object]]:
    return [json.loads(line) for line in (root / "events.jsonl").read_text().splitlines()]


class ZeroInfFoldUnfoldRepetitionGateTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.temporary = tempfile.TemporaryDirectory()
        cls.output = Path(cls.temporary.name) / "zero_inf"
        cls.result = zero_inf.create_overlay(
            OBSERVATION_RUN,
            RELATIVE_RUN,
            LIFE_RUN,
            INTERACTIVE_RUN,
            REUNIFIED_RUN,
            cls.output,
        )

    @classmethod
    def tearDownClass(cls) -> None:
        cls.temporary.cleanup()

    def test_exact_zero_inf_open_result(self) -> None:
        summary = self.result["summary"]
        self.assertEqual(summary["rounds"], 12)
        self.assertEqual(summary["rounds_with_inf_reactor_geometry"], 11)
        self.assertEqual(summary["inf_reactor_fibres"], 33)
        self.assertEqual(summary["inf_reciprocal_presentations"], 66)
        self.assertEqual(summary["zero_pole_universal_readings"], 12)
        self.assertEqual(summary["authored_translation_steps"], 0)
        self.assertEqual(summary["fold_readings"], 0)
        self.assertEqual(summary["unfold_readings"], 0)
        self.assertEqual(summary["repetition_readings"], 0)
        self.assertEqual(summary["second_level_readings"], 0)
        self.assertEqual(summary["profit_assessments"], 0)
        self.assertEqual(summary["open_zero_inf_commands"], 12)

    def test_poles_are_present_but_repetition_is_not_manufactured(self) -> None:
        for event in read_events(self.output):
            poles = event["zero_inf"]
            self.assertEqual(poles["zero"]["form"], "GREATEST_INTERNAL_FORM")
            self.assertEqual(poles["zero"]["fold"], "IMMEDIATE_UNCONDITIONAL")
            self.assertEqual(poles["inf"]["form"], "LEAST_INTERNAL_FORM")
            self.assertIsNone(poles["authored_translation_step"])
            self.assertIsNone(poles["inf"]["fold"])
            self.assertIsNone(poles["inf"]["unfold"])
            self.assertIsNone(poles["inf"]["repetition"])
            self.assertIsNone(poles["second_level"])
            self.assertEqual(event["command"]["state"], "OPEN_ZERO_INF_TRANSLATION")

    def test_runtime_has_no_resource_or_time_selected_translation(self) -> None:
        source = inspect.getsource(zero_inf)
        self.assertNotIn("max(", source)
        self.assertNotIn("completed_return", source)
        self.assertNotIn("float(", source)
        self.assertNotIn("Decimal(", source)
        self.assertFalse(zero_inf.DERIVATION["resource_metric_authors_step"])
        self.assertFalse(zero_inf.DERIVATION["market_time_authors_step"])

    def test_offline_replay_rejects_forged_authored_step(self) -> None:
        with mock.patch.object(socket, "socket", side_effect=AssertionError("network forbidden")):
            verified = zero_inf.verify_overlay(
                OBSERVATION_RUN,
                RELATIVE_RUN,
                LIFE_RUN,
                INTERACTIVE_RUN,
                REUNIFIED_RUN,
                self.output,
            )
        self.assertTrue(verified["verified"])

        forged = Path(self.temporary.name) / "forged"
        shutil.copytree(self.output, forged)
        manifest_path = forged / "manifest.json"
        manifest = json.loads(manifest_path.read_text())
        events = read_events(forged)
        events[0]["zero_inf"]["authored_translation_step"] = "market_time"
        events[0]["zero_inf"]["inf"]["repetition"] = True
        previous = manifest["genesis_hash"]
        for event in events:
            event["previous_event_hash"] = previous
            event.pop("event_hash", None)
            event["event_hash"] = zero_inf.sha256_bytes(zero_inf.canonical_json_bytes(event))
            previous = event["event_hash"]
        ledger = b"".join(zero_inf.canonical_json_bytes(event) + b"\n" for event in events)
        (forged / "events.jsonl").write_bytes(ledger)
        manifest["events_sha256"] = zero_inf.sha256_bytes(ledger)
        manifest["final_event_hash"] = previous
        manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
        with self.assertRaises(ValueError):
            zero_inf.verify_overlay(
                OBSERVATION_RUN,
                RELATIVE_RUN,
                LIFE_RUN,
                INTERACTIVE_RUN,
                REUNIFIED_RUN,
                forged,
            )


if __name__ == "__main__":
    unittest.main()
