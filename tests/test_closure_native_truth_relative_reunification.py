import tempfile
import unittest
from pathlib import Path

from experiments.closure_native_truth_relative_reunification import run


class ClosureNativeTruthRelativeReunificationTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory()
        cls.result = run(Path(cls.temp.name))

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def test_contraction_is_not_closure_and_return_is_relational(self):
        ball = self.result["ball_hair_round"]
        self.assertTrue(self.result["contraction_control"]["different_routes"])
        self.assertTrue(self.result["contraction_control"]["same_contracted_whole"])
        self.assertTrue(ball["relation"]["contextual_relation_continues"])
        self.assertFalse(ball["Ka"]["literal_route_identity"])
        self.assertEqual(ball["Omega"], 6)
        self.assertEqual(ball["verdict"], "CLOSED_TO_NEW_OPENING")

    def test_parent_can_close_without_erasing_children(self):
        parent = self.result["mirror_parent"]
        self.assertTrue(parent["children_distinct"])
        self.assertEqual(parent["parent_signed_residue"], 0)
        self.assertFalse(parent["child_final_completion_claimed"])

    def test_inverse_limit_and_interactive_proof_boundaries(self):
        inverse = self.result["inverse_limit_proxy"]
        proof = self.result["interactive_proof"]
        self.assertTrue(inverse["positive_at_every_observed_finite_level"])
        self.assertFalse(inverse["finite_level_literal_identity_claimed"])
        self.assertEqual(proof["returned_obligations"]["status"], "CLOSED_TO_NEW_OPENING")
        self.assertEqual(proof["contradictory_obligations"]["status"], "FALSE_OR_COLLAPSE")
        self.assertEqual(proof["missing_obligations"]["status"], "OPEN_NO_RETURNED_OBLIGATIONS")
