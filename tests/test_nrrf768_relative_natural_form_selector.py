import ast
import hashlib
import inspect
import json
import shutil
import socket
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from experiments import nrrf767_live_paper_trading_bot as source_bot
from experiments import nrrf768_relative_natural_form_selector as selector


ROOT = Path(__file__).parents[1]
MODULE = ROOT / "experiments" / "nrrf768_relative_natural_form_selector.py"
SOURCE_MODULE = ROOT / "experiments" / "nrrf767_live_paper_trading_bot.py"
LOCKED_SOURCE_RUN = (
    ROOT
    / "runs"
    / "nrrf767_live_paper_trading_bot"
    / "bitstamp_public_20260826T0221Z"
)


def read_events(overlay_dir: Path) -> list[dict[str, object]]:
    return [
        json.loads(line)
        for line in (overlay_dir / "events.jsonl").read_text().splitlines()
    ]


def rechain_semantic_forgery(
    overlay_dir: Path,
    mutation,
) -> None:
    """Make an internally rehashed forgery so replay, not a cheap hash check, rejects it."""

    manifest_path = overlay_dir / "manifest.json"
    manifest = json.loads(manifest_path.read_text())
    events = read_events(overlay_dir)
    mutation(events)
    previous = manifest["genesis_hash"]
    for event in events:
        event["previous_event_hash"] = previous
        event.pop("event_hash", None)
        event["event_hash"] = selector.sha256_bytes(selector.canonical_json_bytes(event))
        previous = event["event_hash"]
    ledger = b"".join(
        selector.canonical_json_bytes(event) + b"\n" for event in events
    )
    (overlay_dir / "events.jsonl").write_bytes(ledger)
    manifest["events_sha256"] = selector.sha256_bytes(ledger)
    manifest["final_event_hash"] = previous
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")


class LockedSourceAndOverlayTest(unittest.TestCase):
    def create(self, output: Path, orientation: str = "PLUS") -> dict[str, object]:
        return selector.create_overlay(
            LOCKED_SOURCE_RUN,
            output,
            selector.SelectorConfig(orientation),
        )

    def test_locked_nrrf767_v1_verification_is_unchanged(self) -> None:
        verification = source_bot.verify_run(LOCKED_SOURCE_RUN)
        self.assertTrue(verification["verified"])
        self.assertEqual(verification["event_count"], 12)
        self.assertEqual(
            verification["configuration_sha256"],
            "544070bca366ea0c0dbc0d48e4e085ab88cd7cf90a391760d0dffa3a00689b33",
        )
        self.assertEqual(
            verification["final_event_hash"],
            "50755b3a49a0e40f33780792fd8c92456f298ca8b4d9eb689297e0d4e529a373",
        )
        self.assertEqual(
            verification["events_sha256"],
            "0669ec688688a4810ee61b4f6b18b5dee720eaa0e1a6ac5f140cd51128e4ac81",
        )
        self.assertEqual(
            hashlib.sha256(SOURCE_MODULE.read_bytes()).hexdigest(),
            selector.PINNED_NRRF767_PROGRAM_SHA256,
        )

    def test_overlay_is_byte_deterministic_and_verifies_without_network(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            first = Path(directory) / "first"
            second = Path(directory) / "second"
            self.create(first)
            self.create(second)
            for name in ("events.jsonl", "summary.json", "manifest.json"):
                self.assertEqual((first / name).read_bytes(), (second / name).read_bytes())
            with mock.patch.object(socket, "socket", side_effect=AssertionError("network forbidden")):
                verification = selector.verify_overlay(first, LOCKED_SOURCE_RUN)
            self.assertTrue(verification["verified"])
            self.assertEqual(verification["event_count"], 12)
            self.assertEqual(
                verification["source_final_event_hash"],
                "50755b3a49a0e40f33780792fd8c92456f298ca8b4d9eb689297e0d4e529a373",
            )
            self.assertEqual(
                verification["source_program_sha256"],
                selector.PINNED_NRRF767_PROGRAM_SHA256,
            )
            self.assertEqual(
                verification["manifest_sha256"],
                hashlib.sha256((first / "manifest.json").read_bytes()).hexdigest(),
            )

    def test_direct_file_cli_build_and_verify(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            overlay = Path(directory) / "overlay"
            build = subprocess.run(
                [
                    sys.executable,
                    str(MODULE),
                    "build",
                    "--source-run",
                    str(LOCKED_SOURCE_RUN),
                    "--output-dir",
                    str(overlay),
                    "--initial-orientation",
                    "MINUS",
                ],
                check=True,
                capture_output=True,
                text=True,
            )
            verify = subprocess.run(
                [
                    sys.executable,
                    str(MODULE),
                    "verify",
                    "--source-run",
                    str(LOCKED_SOURCE_RUN),
                    "--overlay-dir",
                    str(overlay),
                ],
                check=True,
                capture_output=True,
                text=True,
            )
            self.assertTrue(json.loads(build.stdout)["created"])
            self.assertTrue(json.loads(verify.stdout)["verified"])

    def test_every_section_is_exactly_one_choice_per_polar_radius_fibre(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            overlay = Path(directory) / "overlay"
            self.create(overlay)
            events = read_events(overlay)
            expected_radii = ["100", "1000", "10000"]
            for event in events:
                context = event["context"]
                self.assertEqual(context["relative_identity"], "SAME_START_USD_RADIUS")
                self.assertEqual(
                    [fibre["start_usd"] for fibre in context["fibres"]],
                    expected_radii,
                )
                self.assertEqual(
                    [choice["start_usd"] for choice in event["section"]],
                    expected_radii,
                )
                self.assertEqual(len({choice["fibre_id"] for choice in event["section"]}), 3)
                self.assertEqual(len(event["selected_empirical_assessments"]), 3)
                for fibre in context["fibres"]:
                    self.assertEqual(fibre["member_orientations"], ["PLUS", "MINUS"])
                    self.assertEqual(
                        [item["orientation"] for item in fibre["presentations"]],
                        ["PLUS", "MINUS"],
                    )
                    self.assertEqual(
                        set(fibre["polar_reversal"]), {"PLUS", "MINUS"}
                    )

    def test_negative_assessment_is_retained_and_changes_only_the_next_form(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            overlay = Path(directory) / "overlay"
            self.create(overlay, "PLUS")
            events = read_events(overlay)
            first_assessments = events[0]["selected_empirical_assessments"]
            self.assertTrue(
                all(float(item["candidate_return_bps"]) < 0 for item in first_assessments)
            )
            self.assertTrue(all(item["decision"] == "HOLD" for item in first_assessments))
            self.assertTrue(
                all(item["orientation"] == "PLUS" for item in first_assessments)
            )
            self.assertTrue(
                all(
                    choice["chosen_orientation"] == "MINUS"
                    for choice in events[1]["section"]
                )
            )
            self.assertTrue(
                all(
                    witness["translation"] == "POLAR_REVERSAL"
                    and witness["feedback_trigger"]
                    == "PRECEDING_NUMERIC_HOLD_REVERSES"
                    for witness in events[1]["translation_witnesses"]
                )
            )
            # Round 6 is OPEN.  Its chosen form is retained into round 7.
            self.assertEqual(events[6]["context"]["source_observation_state"], "OPEN_PUBLIC_BOOKS")
            self.assertEqual(events[6]["section"], events[7]["section"])
            self.assertTrue(
                all(
                    witness["translation"] == "IDENTITY"
                    and witness["feedback_trigger"] == "PRECEDING_OPEN_RETAINS"
                    for witness in events[7]["translation_witnesses"]
                )
            )
            summary = json.loads((overlay / "summary.json").read_text())
            self.assertEqual(summary["numeric_assessments"], 33)
            self.assertEqual(summary["negative_numeric_assessments"], 33)
            self.assertEqual(summary["positive_numeric_assessments"], 0)
            self.assertEqual(
                summary["translation_counts"],
                {"AUTHORED_INITIAL": 3, "IDENTITY": 3, "POLAR_REVERSAL": 30},
            )

    def test_plus_and_minus_are_both_valid_free_authored_sections(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            plus = Path(directory) / "plus"
            minus = Path(directory) / "minus"
            self.create(plus, "PLUS")
            self.create(minus, "MINUS")
            plus_verification = selector.verify_overlay(plus, LOCKED_SOURCE_RUN)
            minus_verification = selector.verify_overlay(minus, LOCKED_SOURCE_RUN)
            self.assertTrue(plus_verification["verified"])
            self.assertTrue(minus_verification["verified"])
            plus_first = read_events(plus)[0]
            minus_first = read_events(minus)[0]
            self.assertEqual(
                [choice["fibre_id"] for choice in plus_first["section"]],
                [choice["fibre_id"] for choice in minus_first["section"]],
            )
            self.assertEqual(
                {choice["chosen_orientation"] for choice in plus_first["section"]},
                {"PLUS"},
            )
            self.assertEqual(
                {choice["chosen_orientation"] for choice in minus_first["section"]},
                {"MINUS"},
            )
            self.assertNotEqual(
                plus_verification["selector_configuration_sha256"],
                minus_verification["selector_configuration_sha256"],
            )

    def test_selection_is_never_action_execution_or_profit_selection(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            overlay = Path(directory) / "overlay"
            manifest = self.create(overlay)
            self.assertEqual(manifest["boundary"], selector.NO_ORDER_BOUNDARY)
            for event in read_events(overlay):
                self.assertEqual(event["boundary"], selector.NO_ORDER_BOUNDARY)
                for assessment in event["selected_empirical_assessments"]:
                    self.assertFalse(assessment["action_selected"])
                    self.assertFalse(assessment["execution_authorized"])
                    self.assertFalse(assessment["profit_claimed"])
            summary = json.loads((overlay / "summary.json").read_text())
            self.assertEqual(summary["action_selections"], 0)
            self.assertEqual(summary["profit_selections"], 0)
            self.assertEqual(summary["orders_submitted"], 0)
            self.assertEqual(summary["no_order_account_delta_usd"], "0")
            self.assertIsNone(summary["authenticated_settled_pnl_usd"])

    def test_feedback_contains_no_argmax_or_comparison_of_alternatives(self) -> None:
        for function in (selector.feedback_translation, selector.translated_section):
            tree = ast.parse(inspect.getsource(function))
            called_names = {
                node.func.id
                for node in ast.walk(tree)
                if isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            }
            self.assertTrue(called_names.isdisjoint({"max", "min"}))
        source = MODULE.read_text()
        self.assertNotIn("selected_paper_signal", source)
        self.assertNotIn("candidate_delta_usd']) >", source)
        self.assertNotIn("candidate_return_bps']) >", source)

    def test_manifest_binds_program_source_manifest_and_source_events(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            overlay = Path(directory) / "overlay"
            manifest = self.create(overlay)
            binding = manifest["source_binding"]
            self.assertEqual(
                manifest["program_sha256"], hashlib.sha256(MODULE.read_bytes()).hexdigest()
            )
            self.assertEqual(
                binding["program_sha256"], selector.PINNED_NRRF767_PROGRAM_SHA256
            )
            self.assertEqual(
                binding["manifest_sha256"],
                hashlib.sha256((LOCKED_SOURCE_RUN / "manifest.json").read_bytes()).hexdigest(),
            )
            self.assertEqual(
                binding["events_sha256"],
                hashlib.sha256((LOCKED_SOURCE_RUN / "events.jsonl").read_bytes()).hexdigest(),
            )
            source_hashes = [
                json.loads(line)["event_hash"]
                for line in (LOCKED_SOURCE_RUN / "events.jsonl").read_text().splitlines()
            ]
            self.assertEqual(
                [event["source_event_hash"] for event in read_events(overlay)],
                source_hashes,
            )

    def test_source_event_swap_after_binding_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source_copy = root / "source"
            output = root / "overlay"
            shutil.copytree(LOCKED_SOURCE_RUN, source_copy)
            original_source_binding = selector.source_binding

            def bind_then_swap(source_run: Path):
                binding = original_source_binding(source_run)
                events_path = source_run / "events.jsonl"
                raw = events_path.read_bytes()
                events_path.write_bytes(raw.replace(b"\n", b" \n", 1))
                return binding

            with mock.patch.object(
                selector, "source_binding", side_effect=bind_then_swap
            ):
                with self.assertRaisesRegex(
                    ValueError, "source events changed after their verified binding"
                ):
                    selector.create_overlay(source_copy, output)

    def test_nonempty_output_is_not_overwritten(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "overlay"
            output.mkdir()
            (output / "keep.txt").write_text("mine")
            with self.assertRaises(FileExistsError):
                self.create(output)
            self.assertEqual((output / "keep.txt").read_text(), "mine")


class SemanticForgeryTest(unittest.TestCase):
    def forged_overlay(self, root: Path, mutation) -> Path:
        overlay = root / "overlay"
        selector.create_overlay(LOCKED_SOURCE_RUN, overlay)
        rechain_semantic_forgery(overlay, mutation)
        return overlay

    def test_rehashed_missing_duplicated_cross_radius_and_invented_choices_fail(self) -> None:
        def missing(events):
            events[0]["section"].pop()

        def duplicated(events):
            events[0]["section"].append(dict(events[0]["section"][0]))

        def cross_radius(events):
            events[0]["section"][0]["fibre_id"] = events[0]["section"][1]["fibre_id"]

        def invented(events):
            events[0]["section"][0]["chosen_orientation"] = "INVENTED"

        for name, mutation in (
            ("missing", missing),
            ("duplicated", duplicated),
            ("cross_radius", cross_radius),
            ("invented", invented),
        ):
            with self.subTest(name=name), tempfile.TemporaryDirectory() as directory:
                overlay = self.forged_overlay(Path(directory), mutation)
                with self.assertRaises(ValueError):
                    selector.verify_overlay(overlay, LOCKED_SOURCE_RUN)

    def test_rehashed_invented_assessment_and_noncausal_translation_fail(self) -> None:
        def invented_assessment(events):
            events[0]["selected_empirical_assessments"][0][
                "source_evaluation_sha256"
            ] = "0" * 64

        def noncausal_translation(events):
            events[1]["section"][0] = dict(events[0]["section"][0])
            events[1]["translation_witnesses"][0]["translation"] = "IDENTITY"
            events[1]["translation_witnesses"][0]["feedback_trigger"] = (
                "PRECEDING_SELECTED_ASSESSMENT_RETAINS"
            )
            events[1]["translation_witnesses"][0]["to_orientation"] = "PLUS"
            events[1]["translation_witnesses"][0]["to_presentation_id"] = (
                events[0]["section"][0]["chosen_presentation_id"]
            )

        for name, mutation in (
            ("invented_assessment", invented_assessment),
            ("noncausal_translation", noncausal_translation),
        ):
            with self.subTest(name=name), tempfile.TemporaryDirectory() as directory:
                overlay = self.forged_overlay(Path(directory), mutation)
                with self.assertRaisesRegex(ValueError, "semantic replay mismatch"):
                    selector.verify_overlay(overlay, LOCKED_SOURCE_RUN)

    def test_plain_event_summary_manifest_and_extra_file_tampering_fail(self) -> None:
        for name, mutation in (
            (
                "event",
                lambda overlay: (overlay / "events.jsonl").write_bytes(
                    (overlay / "events.jsonl").read_bytes().replace(b'"PLUS"', b'"MINUS"', 1)
                ),
            ),
            ("summary", lambda overlay: (overlay / "summary.json").write_text("{}\n")),
            (
                "manifest",
                lambda overlay: (overlay / "manifest.json").write_text("{}\n"),
            ),
            ("extra", lambda overlay: (overlay / "extra.txt").write_text("not immutable")),
        ):
            with self.subTest(name=name), tempfile.TemporaryDirectory() as directory:
                overlay = Path(directory) / "overlay"
                selector.create_overlay(LOCKED_SOURCE_RUN, overlay)
                mutation(overlay)
                with self.assertRaises(ValueError):
                    selector.verify_overlay(overlay, LOCKED_SOURCE_RUN)

    def test_overlay_cannot_be_rebound_to_a_changed_source_manifest(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            overlay = root / "overlay"
            source_copy = root / "source"
            selector.create_overlay(LOCKED_SOURCE_RUN, overlay)
            shutil.copytree(LOCKED_SOURCE_RUN, source_copy)
            manifest_path = source_copy / "manifest.json"
            manifest = json.loads(manifest_path.read_text())
            manifest["source"]["venue"] = "invented"
            manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
            with self.assertRaises(ValueError):
                selector.verify_overlay(overlay, source_copy)


if __name__ == "__main__":
    unittest.main()
