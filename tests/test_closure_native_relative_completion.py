import tempfile
import unittest
from pathlib import Path

from experiments.closure_native_relative_completion import freeze, native_cases, run, verify_frozen


class ClosureNativeRelativeCompletionTest(unittest.TestCase):
    def test_freeze_is_a_receipt_not_an_identity_axiom(self) -> None:
        receipt = freeze({"name": "local", "overlap_values": {"u": 0}})
        self.assertTrue(verify_frozen(receipt))
        self.assertNotIn("identity", receipt)
        receipt["presentation"]["overlap_values"]["u"] = 1
        self.assertFalse(verify_frozen(receipt))

    def test_unglued_pair_completes_only_relatively(self) -> None:
        result = native_cases()["relative_gluing_of_literally_unglued_pair"]
        self.assertEqual(result["status"], "RELATIVE_COMPLETION_WITH_OPENING")
        self.assertTrue(result["translation_preserves_relative_relation"])
        self.assertTrue(result["return_recovers_admitted_overlap"])
        self.assertTrue(result["round_moves_an_admitted_presentation"])
        self.assertFalse(result["residue_is_neutral"])
        self.assertFalse(result["absolute_full_presentation_identity_claimed"])

    def test_glued_pair_can_have_a_relative_obstruction(self) -> None:
        result = native_cases()["relative_obstruction_of_literally_glued_pair"]
        self.assertEqual(result["status"], "RELATIVE_OBSTRUCTION")
        self.assertFalse(result["return_recovers_admitted_overlap"])
        self.assertTrue(result["translation_preserves_relative_relation"])

    def test_freezing_and_translation_are_distinguished_by_movement(self) -> None:
        frozen = native_cases()["frozen_identity_control"]
        self.assertEqual(frozen["status"], "FROZEN_AXIOMETRY")
        self.assertFalse(frozen["round_moves_an_admitted_presentation"])
        self.assertTrue(frozen["return_recovers_admitted_overlap"])

    def test_runtime_materializes_reproducible_receipt(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            result = run(Path(directory))
            self.assertEqual(result["protocol"], "closure_native_relative_translation_v1")
            self.assertTrue((Path(directory) / "closure_native_relative_completion.json").is_file())
