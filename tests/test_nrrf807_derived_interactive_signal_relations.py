import json
import shutil
import socket
import tempfile
import unittest
from decimal import Decimal, localcontext
from pathlib import Path
from unittest import mock

from experiments import nrrf807_derived_interactive_signal_relations as interactive


ROOT = Path(__file__).parents[1]
OBSERVATION_RUN = ROOT / "runs/nrrf767_live_paper_trading_bot/bitstamp_public_20260826T0221Z"
RELATIVE_RUN = ROOT / "runs/nrrf805_relativistic_signal_open_command/bitstamp_public_20260826T0221Z"
LIFE_RUN = ROOT / "runs/nrrf806_translation_first_life_reactor/bitstamp_public_20260826T0221Z"


def read_events(root: Path) -> list[dict[str, object]]:
    return [json.loads(line) for line in (root / "events.jsonl").read_text().splitlines()]


class DerivedInteractiveSignalRelationsTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.temporary = tempfile.TemporaryDirectory()
        cls.output = Path(cls.temporary.name) / "interactive"
        cls.result = interactive.create_overlay(
            OBSERVATION_RUN, RELATIVE_RUN, LIFE_RUN, cls.output
        )

    @classmethod
    def tearDownClass(cls) -> None:
        cls.temporary.cleanup()

    def test_exact_cross_stage_results(self) -> None:
        summary = self.result["summary"]
        self.assertEqual(summary["adjacent_interactions"], 11)
        self.assertEqual(summary["interactions_with_numeric_relations"], 9)
        self.assertEqual(summary["derived_interactive_relations"], 117)
        self.assertEqual(summary["local_accounting_closures"], 117)
        self.assertEqual(summary["global_hair_zero_closures"], 74)
        self.assertEqual(summary["global_hair_open_changes"], 43)
        self.assertEqual(summary["positive_completed_presentations"], 0)
        self.assertEqual(summary["open_commands"], 11)
        self.assertEqual(summary["orders_submitted"], 0)

    def test_global_hair_is_the_interactive_potential_gap(self) -> None:
        relations = []
        for event in read_events(self.output):
            for record in event["records"]:
                if record["completed"] is None:
                    continue
                prior = Decimal(record["prior_action_potential"])
                realized = Decimal(record["realized_zero_hair_potential"])
                local_hair = Decimal(record["local_hair"])
                completed = Decimal(record["completed"])
                local_residual = Decimal(record["local_accounting_residual"])
                global_hair = Decimal(record["global_hair"])
                with localcontext() as context:
                    context.prec = interactive.PRECISION
                    accounting = completed - (realized - local_hair)
                    interaction_gap = realized - prior
                self.assertEqual(local_residual, accounting)
                self.assertLessEqual(abs(local_residual), interactive.TOLERANCE)
                self.assertLessEqual(abs(global_hair - interaction_gap), interactive.TOLERANCE)
                relations.append(record["interactive_signal_relation"])
        self.assertIn("CLOSED", relations)
        self.assertIn("OPEN_CHANGED", relations)

    def test_action_precedes_potential_without_execution_authority(self) -> None:
        manifest = self.result["manifest"]
        self.assertFalse(manifest["interaction"]["lookahead_used_for_prior_selection"])
        self.assertFalse(manifest["interaction"]["orders_enabled"])
        self.assertEqual(manifest["translation_state"]["authority_presentation"], "UNPRESENTED")
        for event in read_events(self.output):
            self.assertEqual(event["later_round_index"], event["prior_round_index"] + 1)
            self.assertNotEqual(
                event["prior_observation_event_hash"], event["later_observation_event_hash"]
            )
            self.assertEqual(event["command"]["state"], "OPEN")
            self.assertEqual(event["command"]["orders_submitted"], 0)
            for record in event["records"]:
                self.assertEqual(record["action_source_round"], event["prior_round_index"])
                self.assertEqual(record["potential_source_round"], event["later_round_index"])
                self.assertEqual(record["exchange_action"], "OPEN")

    def test_offline_replay_rejects_forged_admission(self) -> None:
        with mock.patch.object(socket, "socket", side_effect=AssertionError("network forbidden")):
            verified = interactive.verify_overlay(
                OBSERVATION_RUN, RELATIVE_RUN, LIFE_RUN, self.output
            )
        self.assertTrue(verified["verified"])

        forged = Path(self.temporary.name) / "forged"
        shutil.copytree(self.output, forged)
        manifest_path = forged / "manifest.json"
        manifest = json.loads(manifest_path.read_text())
        events = read_events(forged)
        changed = next(
            record
            for event in events
            for record in event["records"]
            if record["interactive_signal_relation"] == "OPEN_CHANGED"
        )
        changed["zero_hair_executor"] = "ADMIT_INTERACTION"
        previous = manifest["genesis_hash"]
        for event in events:
            event["previous_event_hash"] = previous
            event.pop("event_hash", None)
            event["event_hash"] = interactive.sha256_bytes(
                interactive.canonical_json_bytes(event)
            )
            previous = event["event_hash"]
        ledger = b"".join(
            interactive.canonical_json_bytes(event) + b"\n" for event in events
        )
        (forged / "events.jsonl").write_bytes(ledger)
        manifest["events_sha256"] = interactive.sha256_bytes(ledger)
        manifest["final_event_hash"] = previous
        manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
        with self.assertRaises(ValueError):
            interactive.verify_overlay(OBSERVATION_RUN, RELATIVE_RUN, LIFE_RUN, forged)


if __name__ == "__main__":
    unittest.main()
