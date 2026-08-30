import importlib.util
import json
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MOD_PATH = ROOT / "experiments" / "nrrf847_realistic_cost_slippage_closure_learning.py"
spec = importlib.util.spec_from_file_location("nrrf847_costs", MOD_PATH)
mod = importlib.util.module_from_spec(spec)
assert spec and spec.loader
spec.loader.exec_module(mod)


class TestNRRF847RealisticCosts(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.empirical = json.loads((ROOT / "reports" / "nrrf846_empirical_alpaca_sense_loop_20260830.json").read_text())
        cls.result = mod.run(cls.empirical)

    def test_30bps_all_hold(self):
        self.assertTrue(self.result["all_in_30bps_all_hold"])

    def test_no_cost_adjusted_unsafe_admissions(self):
        self.assertEqual(self.result["closure_adjusted_unsafe_admissions"], 0)

    def test_gross_only_selector_is_unsafe(self):
        self.assertGreater(self.result["naive_gross_positive_unsafe_admissions"], 0)

    def test_tight_liquid_keeps_only_observed_positive_classes(self):
        self.assertEqual(self.result["learned_actions"]["A"]["TIGHT_LIQUID"], "TRADE")
        self.assertEqual(self.result["learned_actions"]["B"]["TIGHT_LIQUID"], "HOLD")
        self.assertEqual(self.result["learned_actions"]["C"]["TIGHT_LIQUID"], "TRADE")

    def test_normal_cost_erases_A_but_not_marginal_C(self):
        self.assertEqual(self.result["learned_actions"]["A"]["NORMAL"], "HOLD")
        self.assertEqual(self.result["learned_actions"]["C"]["NORMAL"], "TRADE")

    def test_stressed_all_hold(self):
        for cycle in ("A", "B", "C"):
            self.assertEqual(self.result["learned_actions"][cycle]["STRESSED"], "HOLD")


if __name__ == "__main__":
    unittest.main()
