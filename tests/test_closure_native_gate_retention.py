import tempfile
import unittest
from pathlib import Path

from experiments.closure_native_gate_retention import run


class ClosureNativeGateRetentionTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.temporary = tempfile.TemporaryDirectory()
        cls.result = run(Path(cls.temporary.name))

    @classmethod
    def tearDownClass(cls) -> None:
        cls.temporary.cleanup()

    def test_price_gate_conflates_holding_and_attempt(self) -> None:
        gate = self.result["gate_comparison"]
        self.assertTrue(gate["price_is_capital_determined"])
        self.assertTrue(gate["price_conflates_genuine_refusal_and_nongenuine_admission"])
        self.assertTrue(gate["receipt_borne_equals_reciprocal"])
        self.assertTrue(gate["receipt_waives_price_for_genuine_attempt"])

    def test_compounding_does_not_reopen_exclusion(self) -> None:
        report = self.result["compounding_control"]
        self.assertTrue(report["excluded_absorbing_for_bounded_newcomer"])
        self.assertEqual(report["price_retention"], 0)
        self.assertEqual(report["reciprocal_retention"], 6)
        self.assertEqual(report["retention_gap"], 6)

    def test_paired_seed_control_is_explicitly_ordered(self) -> None:
        report = self.result["paired_seed_control"]
        self.assertEqual(report["seed_count"], 12)
        self.assertTrue(report["price_strictly_below_reciprocal_every_seed"])
        self.assertTrue(report["price_never_exceeds_central"])
        self.assertTrue(report["price_at_most_two"])
