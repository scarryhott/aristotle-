from __future__ import annotations

import unittest
from fractions import Fraction

from experiments.nrrf849_relational_completeness_identification_price_continuum import (
    RelationalScenario,
    edges,
)
from experiments.nrrf850_higher_closure_profit_history_unification import (
    HistoryMorphism,
    add_costs,
    apply_history,
    contextual_history_distortion,
    critical_uniform_fee,
    higher_flat,
    higher_loop_curvature,
    history,
    max_mean_roundtrip_profit,
    profit_natural_form,
    roundtrip_profit,
    translate_preserves_higher_state,
    uniform_fee,
)


class NRRF850HigherClosureTests(unittest.TestCase):
    def setUp(self) -> None:
        vertices = ("o", "a", "b")
        costs = {e: Fraction(0) for e in edges(vertices)}
        costs[("o", "a")] = Fraction(2)
        costs[("a", "b")] = Fraction(-5)
        costs[("b", "o")] = Fraction(1)
        costs[("o", "b")] = Fraction(1)
        costs[("b", "a")] = Fraction(1)
        costs[("a", "o")] = Fraction(1)
        social = {"o": Fraction(0), "a": Fraction(2), "b": Fraction(-1)}
        self.s = RelationalScenario(vertices, "o", costs, social)
        self.walks = (
            ("o", "a", "o"),
            ("o", "b", "o"),
            ("o", "a", "b", "o"),
            ("o", "b", "a", "o"),
        )

    def test_roundtrip_only(self) -> None:
        with self.assertRaises(ValueError):
            roundtrip_profit(self.s, ("o", "a"))

    def test_pure_translation_preserves_complete_profit_natural_form(self) -> None:
        phi = {"o": Fraction(0), "a": Fraction(100), "b": Fraction(-77)}
        self.assertTrue(translate_preserves_higher_state(self.s, phi, self.walks))

    def test_history_composition_and_inverse(self) -> None:
        a = profit_natural_form(self.s, self.walks)
        b = profit_natural_form(uniform_fee(self.s, Fraction(1, 2)), self.walks)
        c = profit_natural_form(uniform_fee(self.s, Fraction(3, 2)), self.walks)
        hab = history(a, b)
        hbc = history(b, c)
        hac = history(a, c)
        self.assertEqual(hab.compose(hbc), hac)
        self.assertEqual(hab.compose(hab.inverse()), HistoryMorphism.identity(self.walks))
        self.assertEqual(apply_history(a, hab), b)

    def test_exact_closed_history_loop_has_zero_higher_curvature(self) -> None:
        a = profit_natural_form(self.s, self.walks)
        b = profit_natural_form(uniform_fee(self.s, Fraction(1, 3)), self.walks)
        c = profit_natural_form(uniform_fee(self.s, Fraction(2, 3)), self.walks)
        loop = (history(a, b), history(b, c), history(c, a))
        self.assertTrue(higher_flat(loop))
        self.assertTrue(all(x == 0 for x in higher_loop_curvature(loop)))

    def test_contextual_second_order_adversary_creates_higher_curvature(self) -> None:
        a = profit_natural_form(self.s, self.walks)
        b = profit_natural_form(uniform_fee(self.s, Fraction(1, 3)), self.walks)
        c = profit_natural_form(uniform_fee(self.s, Fraction(2, 3)), self.walks)
        hca = history(c, a)
        distorted = contextual_history_distortion(hca, self.walks[2], Fraction(5, 2))
        loop = (history(a, b), history(b, c), distorted)
        self.assertFalse(higher_flat(loop))
        self.assertEqual(higher_loop_curvature(loop)[2], Fraction(5, 2))

    def test_curved_first_order_adversary_changes_profit_form(self) -> None:
        adversary = {e: Fraction(0) for e in edges(self.s.vertices)}
        adversary[("a", "b")] = Fraction(3)
        before = profit_natural_form(self.s, self.walks)
        after = profit_natural_form(add_costs(self.s, adversary), self.walks)
        self.assertNotEqual(before, after)

    def test_critical_uniform_fee_is_exact_positive_negative_boundary(self) -> None:
        form = profit_natural_form(self.s, self.walks)
        f = critical_uniform_fee(form)
        below = profit_natural_form(uniform_fee(self.s, f - Fraction(1, 10)), self.walks)
        at = profit_natural_form(uniform_fee(self.s, f), self.walks)
        above = profit_natural_form(uniform_fee(self.s, f + Fraction(1, 10)), self.walks)
        self.assertGreater(max_mean_roundtrip_profit(below)[0], 0)
        self.assertEqual(max_mean_roundtrip_profit(at)[0], 0)
        self.assertLess(max_mean_roundtrip_profit(above)[0], 0)


if __name__ == "__main__":
    unittest.main()
