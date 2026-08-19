import tempfile
import unittest
from pathlib import Path

from experiments.closure_native_depth_reclosure import run


class ClosureNativeDepthReclosureTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.temporary = tempfile.TemporaryDirectory()
        cls.result = run(Path(cls.temporary.name))

    @classmethod
    def tearDownClass(cls) -> None:
        cls.temporary.cleanup()

    def test_coarse_equality_can_precede_registered_separation(self) -> None:
        self.assertEqual(self.result["invariant_equality"]["classification"], "EQUAL_THROUGH_REGISTERED_DEPTH")
        separation = self.result["perspectival_separation"]
        self.assertEqual(separation["classification"], "SEPARATED_AT_REGISTERED_DEPTH")
        self.assertEqual(separation["first_separation_depth"], 2)

    def test_missing_bridge_is_open_not_agreement(self) -> None:
        self.assertEqual(
            self.result["missing_contact_bridge_control"]["classification"],
            "OPEN_BRIDGE_BOUNDARY",
        )

    def test_new_question_after_freeze_is_invalid(self) -> None:
        self.assertEqual(
            self.result["posthoc_question_control"]["classification"],
            "INVALID_POSTHOC_QUESTION_STREAM",
        )
