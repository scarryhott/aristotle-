import tempfile
import unittest
from pathlib import Path

from experiments.closure_native_level1_genuineness import run


class ClosureNativeLevel1GenuinenessTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.temporary = tempfile.TemporaryDirectory()
        cls.result = run(Path(cls.temporary.name))

    @classmethod
    def tearDownClass(cls) -> None:
        cls.temporary.cleanup()

    def test_independent_bridge_calibrates_the_gate(self) -> None:
        report = self.result["calibrated_gate"]
        self.assertEqual(report["status"], "LEVEL1_AUDITED")
        self.assertEqual(report["calibration_error_rate"], 0)
        self.assertTrue(report["refused_le_sorting_cost"])
        self.assertEqual(report["cost_per_admitted_genuine_attempt"], 2)

    def test_rubber_stamp_is_detected_by_the_same_bridge(self) -> None:
        report = self.result["rubber_stamp_control"]
        self.assertEqual(report["status"], "LEVEL1_AUDITED")
        self.assertGreater(report["false_accept_count"], 0)
        self.assertGreater(report["calibration_error_rate"], 0)

    def test_missing_or_self_referential_bridge_cannot_certify_genuineness(self) -> None:
        self.assertEqual(self.result["missing_bridge_control"]["status"], "OPEN_NO_LEVEL1_BRIDGE")
        self.assertEqual(self.result["self_certification_control"]["status"], "INVALID_SELF_CERTIFICATION")
