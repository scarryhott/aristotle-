import json
import shutil
import socket
import tempfile
import unittest
from decimal import Decimal, localcontext
from pathlib import Path
from unittest import mock

from experiments import nrrf806_translation_first_life_reactor as life


ROOT = Path(__file__).parents[1]
OBSERVATION_RUN = ROOT / "runs/nrrf767_live_paper_trading_bot/bitstamp_public_20260826T0221Z"
RELATIVE_RUN = ROOT / "runs/nrrf805_relativistic_signal_open_command/bitstamp_public_20260826T0221Z"


def read_events(root: Path) -> list[dict[str, object]]:
    return [json.loads(line) for line in (root / "events.jsonl").read_text().splitlines()]


class TranslationFirstLifeReactorTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.temporary = tempfile.TemporaryDirectory()
        cls.output = Path(cls.temporary.name) / "life"
        cls.result = life.create_overlay(OBSERVATION_RUN, RELATIVE_RUN, cls.output)

    @classmethod
    def tearDownClass(cls) -> None:
        cls.temporary.cleanup()

    def test_exact_local_ball_and_zero_hair_results(self) -> None:
        summary = self.result["summary"]
        self.assertEqual(summary["rounds"], 12)
        self.assertEqual(summary["rooted_life_reactors"], 132)
        self.assertEqual(summary["observed_local_ball_reactions"], 365203)
        self.assertEqual(summary["open_infinity_continuations"], 132)
        self.assertEqual(summary["selected_natural_form_presentations"], 143)
        self.assertEqual(summary["zero_hair_executor_admissions"], 143)
        self.assertTrue(summary["all_global_hair_zero"])
        self.assertEqual(summary["positive_completed_presentations"], 0)
        self.assertEqual(summary["open_commands"], 12)

    def test_global_hair_is_residual_and_local_hair_retains_cost(self) -> None:
        for event in read_events(self.output):
            for record in event["records"]:
                action = Decimal(record["action_potential_return"])
                local_hair = Decimal(record["local_hair_return"])
                completed = Decimal(record["completed_return"])
                residual = Decimal(record["global_hair_zero"])
                with localcontext() as context:
                    context.prec = life.PRECISION
                    recomputed = completed - (action - local_hair)
                self.assertEqual(residual, recomputed)
                self.assertLessEqual(abs(residual), life.TOLERANCE)
                self.assertEqual(record["zero_hair_executor"], "ADMIT_TRANSLATION")
                self.assertFalse(record["positive_completed_potential"])
                self.assertEqual(record["exchange_action"], "OPEN")

    def test_roles_follow_truth_and_command_remains_open(self) -> None:
        for event in read_events(self.output):
            command = event["command"]
            self.assertTrue(command["roles_derived_after_translational_truth"])
            self.assertEqual(command["state"], "OPEN")
            self.assertEqual(command["authority_presentation"], "UNPRESENTED")
            self.assertIn("AUTHORITY_PRESENTATION", command["missing_translations"])
            self.assertEqual(command["orders_submitted"], 0)
            for reactor in event["reactors"]:
                self.assertEqual(reactor["action_return"], "ballReturn")
                self.assertEqual(reactor["potential_return"], "hairReturn")
                self.assertEqual(reactor["continuation"], "OPEN_BEYOND_FINITE_OBSERVATION")

    def test_offline_replay_rejects_forged_exchange_action(self) -> None:
        with mock.patch.object(socket, "socket", side_effect=AssertionError("network forbidden")):
            verified = life.verify_overlay(OBSERVATION_RUN, RELATIVE_RUN, self.output)
        self.assertTrue(verified["verified"])

        forged = Path(self.temporary.name) / "forged"
        shutil.copytree(self.output, forged)
        manifest_path = forged / "manifest.json"
        manifest = json.loads(manifest_path.read_text())
        events = read_events(forged)
        events[0]["records"][0]["exchange_action"] = "ACT"
        previous = manifest["genesis_hash"]
        for event in events:
            event["previous_event_hash"] = previous
            event.pop("event_hash", None)
            event["event_hash"] = life.sha256_bytes(life.canonical_json_bytes(event))
            previous = event["event_hash"]
        ledger = b"".join(life.canonical_json_bytes(event) + b"\n" for event in events)
        (forged / "events.jsonl").write_bytes(ledger)
        manifest["events_sha256"] = life.sha256_bytes(ledger)
        manifest["final_event_hash"] = previous
        manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
        with self.assertRaises(ValueError):
            life.verify_overlay(OBSERVATION_RUN, RELATIVE_RUN, forged)


if __name__ == "__main__":
    unittest.main()
