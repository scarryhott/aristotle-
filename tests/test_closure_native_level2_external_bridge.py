import tempfile
import unittest
from pathlib import Path

from experiments.closure_native_level2_external_bridge import run


class ClosureNativeLevel2ExternalBridgeTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.temporary = tempfile.TemporaryDirectory()
        cls.result = run(Path(cls.temporary.name))

    @classmethod
    def tearDownClass(cls) -> None:
        cls.temporary.cleanup()

    def test_heldout_outcomes_can_support_calibration(self) -> None:
        report = self.result["calibrated_external_bridge"]
        self.assertEqual(report["classification"], "EXTERNALLY_CALIBRATED")
        self.assertTrue(report["supports_level1_calibration"])
        self.assertEqual(report["external_calibration_error_rate"], 0)

    def test_counterexample_is_retained_not_repaired(self) -> None:
        report = self.result["external_counterexample_control"]
        self.assertEqual(report["classification"], "EXTERNAL_COUNTEREXAMPLE")
        self.assertEqual(report["false_accept_count"], 1)

    def test_missing_or_leaked_outcome_is_not_evidence(self) -> None:
        self.assertEqual(self.result["missing_external_bridge_control"]["status"], "OPEN_NO_EXTERNAL_CONSEQUENCE")
        self.assertEqual(self.result["outcome_leakage_control"]["status"], "INVALID_OUTCOME_LEAKAGE")
