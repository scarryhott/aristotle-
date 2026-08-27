import tempfile
import unittest
from pathlib import Path

from experiments.full_bounded_closure_derived_verifier import run


class FullBoundedClosureDerivedVerifierTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory()
        cls.result = run(Path(cls.temp.name))

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def test_full_two_episode_causal_lineage(self):
        closure = self.result["closure"]
        self.assertEqual(closure["status"], "FULL_BOUNDED_CLOSURE_DERIVED_VERIFIER")
        self.assertTrue(closure["source_path_preserved"])
        self.assertTrue(closure["c0_completed"])
        self.assertTrue(closure["c0_admits_axiom_geometry_truth_relation"])
        self.assertTrue(closure["M1_derived"])
        self.assertTrue(closure["F1_derived_from_truth_relation_and_residue"])
        self.assertTrue(closure["M0_cannot_evaluate_R1"])
        self.assertTrue(closure["M1_evaluates_R1"])
        self.assertTrue(closure["c1_completed"])
        self.assertTrue(closure["F2_M2_derived"])
        self.assertTrue(self.result["frozen_inputs"]["R1_frozen_before_M1"])

    def test_nonpromotion_and_burden_controls(self):
        controls = self.result["controls"]
        for name in ("INVALID_PREAUTHORED_SUCCESSOR", "INVALID_SELF_CERTIFICATION", "OPEN_NO_INTERACTION", "OPEN_NO_REVIEW", "OPEN_NO_RETURN", "OPEN_NO_EXTERNAL_CONSEQUENCE", "INVALID_OUTCOME_LEAKAGE", "EXTERNAL_COUNTEREXAMPLE", "FROZEN_RECOVERY", "ASSERTED_AXIOM_NOT_TRANSLATION"):
            self.assertEqual(controls[name], name)
        self.assertTrue(self.result["basis_change_control"]["burdens_agree"])
        self.assertEqual(self.result["episode0"]["completion"]["translation_audit"]["bridge_status"], "NOT_A_BRIDGE_QUOTIENT_LIKE_MAP")
        equality = self.result["episode0"]["completion"]["axiom_geometry_truth_relation"]
        self.assertFalse(equality["literal_identity_claimed"])
        self.assertFalse(equality["numeric_identity_claimed"])
