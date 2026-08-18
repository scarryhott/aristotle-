import tempfile
import unittest
from pathlib import Path
from experiments.closure_native_axiometric_evolution import run

class ClosureNativeAxiometricEvolutionTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(); cls.result = run(Path(cls.temp.name))
    @classmethod
    def tearDownClass(cls): cls.temp.cleanup()
    def test_successors_are_derived_and_used(self):
        self.assertTrue(self.result["lineage"]["F1_from_completion"])
        self.assertTrue(self.result["lineage"]["F2_from_completion"])
        self.assertTrue(self.result["lineage"]["next_episode_uses_changed_axiometry"])
        self.assertFalse(self.result["F1"]["preauthored"])
    def test_many_one_many_and_external_boundary(self):
        self.assertTrue(self.result["lineage"]["many_one_many"])
        self.assertFalse(self.result["lineage"]["absolute_frame_identity_claimed"])
        self.assertTrue(all(x["classification"] == "EXTERNALLY_CALIBRATED" for x in self.result["level2"]))
        self.assertEqual(self.result["controls"]["missing_outcome"]["status"], "OPEN_NO_EXTERNAL_CONSEQUENCE")
        self.assertEqual(self.result["controls"]["leaked_outcome"]["status"], "INVALID_OUTCOME_LEAKAGE")
