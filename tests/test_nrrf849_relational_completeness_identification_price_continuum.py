import importlib.util
import pathlib
import unittest
from fractions import Fraction

ROOT = pathlib.Path(__file__).resolve().parents[1]
PATH = ROOT / "experiments" / "nrrf849_relational_completeness_identification_price_continuum.py"
spec = importlib.util.spec_from_file_location("nrrf849", PATH)
n = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(n)


class NRRF849Tests(unittest.TestCase):
    def scenario(self):
        vertices = ("o", "a", "b")
        costs = {
            ("o","o"): Fraction(0), ("o","a"): Fraction(2), ("o","b"): Fraction(4),
            ("a","o"): Fraction(3), ("a","a"): Fraction(0), ("a","b"): Fraction(5),
            ("b","o"): Fraction(1), ("b","a"): Fraction(-2), ("b","b"): Fraction(0),
        }
        social = {"o": Fraction(0), "a": Fraction(7), "b": Fraction(-3)}
        return n.RelationalScenario(vertices, "o", costs, social)

    def test_relation_complete(self):
        self.assertTrue(n.relation_complete(self.scenario()))

    def test_translation_changes_coordinates_not_identification(self):
        s = self.scenario()
        phi = {"o": Fraction(0), "a": Fraction(100), "b": Fraction(-50)}
        t = n.translate_scenario(s, phi)
        self.assertNotEqual(s.costs, t.costs)
        self.assertNotEqual(s.social, t.social)
        self.assertEqual(n.completed_roundtrip_observations(s), n.completed_roundtrip_observations(t))
        self.assertTrue(n.relationally_identified(s, t))
        self.assertEqual(n.price_chart(s), n.price_chart(t))
        self.assertEqual(n.descended_social_relation(s), n.descended_social_relation(t))

    def test_genuine_relational_change_breaks_identification(self):
        s = self.scenario()
        costs = dict(s.costs)
        costs[("a", "b")] += Fraction(3)
        t = n.RelationalScenario(s.vertices, s.base, costs, s.social)
        self.assertFalse(n.relationally_identified(s, t))

    def test_unauthenticated_receipt_does_not_author_knowledge(self):
        l = n.ContinuumLearner(["MAKE"])
        r = n.EconomicReceipt(False, "MAKE", 10.0, {"fees": 1.0}, True)
        self.assertFalse(l.observe(self.scenario(), r))
        self.assertEqual(l.evidence_count, 0)

    def test_learning_transfers_across_translated_presentations(self):
        l = n.ContinuumLearner(["MAKE"])
        s = self.scenario()
        for i in range(20):
            phi = {"o": Fraction(0), "a": Fraction(i), "b": Fraction(-2*i)}
            t = n.translate_scenario(s, phi)
            l.observe(t, n.EconomicReceipt(True, "MAKE", 4.0, {"fees": 1.0}, True))
        phi = {"o": Fraction(0), "a": Fraction(999), "b": Fraction(-777)}
        self.assertEqual(l.choose(n.translate_scenario(s, phi)), "MAKE")

    def test_new_cost_can_turn_same_identification_class_to_hold(self):
        l = n.ContinuumLearner(["MAKE"])
        s = self.scenario()
        for _ in range(20):
            l.observe(s, n.EconomicReceipt(True, "MAKE", 5.0, {"fees": 1.0}, True))
        self.assertEqual(l.choose(s), "MAKE")
        for _ in range(80):
            l.observe(s, n.EconomicReceipt(True, "MAKE", 5.0, {"fees": 1.0, "new_tax": 8.0}, True))
        self.assertEqual(l.choose(s), "HOLD")
        self.assertIn("new_tax", l.cost_names)

    def test_closed_identity_is_not_profitability(self):
        r = n.EconomicReceipt(True, "MAKE", 2.0, {"fees": 3.0}, True)
        self.assertLess(r.realized_pnl_bps, 0)


if __name__ == "__main__":
    unittest.main()
