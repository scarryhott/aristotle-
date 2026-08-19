import tempfile
import unittest
from pathlib import Path

from experiments.closure_native_derived_verifier_asi import run


class ClosureNativeDerivedVerifierAsiTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory()
        cls.result = run(Path(cls.temp.name))

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def test_method_itself_completes_a_derived_cycle(self):
        closure = self.result["closure"]
        self.assertTrue(closure["M1_derived_from_seed_completion"])
        self.assertTrue(closure["M1_tested_on_distinct_heldout_relation"])
        self.assertTrue(closure["M2_derived_from_heldout_completion"])
        self.assertTrue(closure["independent_external_consequences"])
        self.assertEqual(closure["method_closure_status"], "DERIVED_METHOD_CYCLE_COMPLETE")

    def test_controls_prevent_a_method_from_asserting_its_own_closure(self):
        controls = self.result["controls"]
        self.assertEqual(controls["preauthored_successor"], "INVALID_PREAUTHORED_METHOD")
        self.assertEqual(controls["self_certified_heldout"]["status"], "INVALID_SELF_CERTIFICATION")
        self.assertEqual(controls["missing_heldout"]["status"], "OPEN_NO_EXTERNAL_CONSEQUENCE")
        self.assertEqual(controls["counterexample_heldout"]["status"], "METHOD_OBSTRUCTION")
