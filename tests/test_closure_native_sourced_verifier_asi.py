import tempfile
import unittest
from pathlib import Path

from experiments.closure_native_sourced_verifier_asi import run


class ClosureNativeSourcedVerifierAsiTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory()
        cls.result = run(Path(cls.temp.name))

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def test_method_closure_uses_prior_committed_closure_records(self):
        closure = self.result["closure"]
        self.assertTrue(closure["SM1_derived_from_closure_data"])
        self.assertTrue(closure["SM1_used_distinct_closure_source"])
        self.assertTrue(closure["SM2_derived_from_heldout_closure_data"])
        self.assertTrue(closure["all_facts_have_content_hashes"])
        self.assertEqual(closure["method_closure_status"], "SOURCED_DERIVED_METHOD_CYCLE_COMPLETE")

    def test_existing_audit_controls_remain_effective_when_reused(self):
        controls = self.result["controls"]
        self.assertEqual(controls["self_certified_verification"]["status"], "INVALID_SELF_CERTIFICATION")
        self.assertEqual(controls["missing_verification"]["status"], "OPEN_NO_EXTERNAL_CONSEQUENCE")
        self.assertEqual(controls["counterexample_verification"]["status"], "METHOD_OBSTRUCTION")
