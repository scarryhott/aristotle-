from __future__ import annotations

import sys
import unittest
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "experiments"))

from nrrf851_finite_interaction_unitary_curvature_gate import (  # noqa: E402
    CYCLE_RANK,
    EDGES,
    UnitaryCurvatureLearner,
    combine_flow,
    exact_regression,
    finite_rank_reach,
    natural_form,
    predict_closed_flow_profit,
    roundtrip_profit,
    translate_cost,
)


class NRRF851Tests(unittest.TestCase):
    def test_cycle_rank_is_twelve(self) -> None:
        self.assertEqual(CYCLE_RANK, 12)

    def test_pure_translation_preserves_natural_form(self) -> None:
        cost = tuple(Fraction(3 * i - 17, 11) for i in range(len(EDGES)))
        phi = {"USD": Fraction(0), "BTC": Fraction(19, 3), "ETH": Fraction(-7, 5),
               "SOL": Fraction(101, 13), "HEDGE": Fraction(-31, 7)}
        shifted = translate_cost(cost, phi)
        self.assertNotEqual(cost, shifted)
        self.assertEqual(natural_form(cost), natural_form(shifted))

    def test_full_basis_predicts_every_generated_closed_flow(self) -> None:
        cost = tuple(Fraction(5 * i - 21, 17) for i in range(len(EDGES)))
        coeff = (2, -1, 3, 0, -2, 1, 4, -1, 0, 2, -3, 1)
        flow = combine_flow(coeff)
        self.assertEqual(
            roundtrip_profit(cost, flow),
            predict_closed_flow_profit(natural_form(cost), coeff),
        )

    def test_exact_regression_has_no_failures(self) -> None:
        result = exact_regression(environments=25, flows_per_environment=10)
        self.assertEqual(result["translation_failures"], 0)
        self.assertEqual(result["prediction_failures"], 0)
        self.assertEqual(result["pointwise_changed"], 25)

    def test_full_rank_resolves_all_generated_flows(self) -> None:
        reach = finite_rank_reach(trials=1000)
        self.assertEqual(reach[0]["resolved_share"], 0.0)
        self.assertEqual(reach[-1]["resolved_share"], 1.0)
        self.assertEqual(reach[-1]["resolved_prediction_error"], 0.0)

    def test_unauthenticated_receipt_does_not_author_knowledge(self) -> None:
        learner = UnitaryCurvatureLearner()
        self.assertFalse(learner.observe(0, 3.0, True, authenticated=False))
        self.assertEqual(learner.evidence, 0)
        self.assertEqual(learner.hairs[0].n, 0)

    def test_unitary_gate_requires_certified_positive_closed_hair(self) -> None:
        learner = UnitaryCurvatureLearner()
        coeff = (1,) + (0,) * (CYCLE_RANK - 1)
        self.assertFalse(learner.admit(coeff))
        for i in range(40):
            learner.observe(0, 2.0 + (0.02 if i % 2 else -0.02), True)
        self.assertTrue(learner.certified(0))
        self.assertTrue(learner.admit(coeff))
        self.assertFalse(learner.admit((-1,) + (0,) * (CYCLE_RANK - 1)))

    def test_curvature_contradiction_reopens_only_affected_hair(self) -> None:
        learner = UnitaryCurvatureLearner()
        for i in range(40):
            learner.observe(0, 2.0 + (0.02 if i % 2 else -0.02), True)
            learner.observe(1, 1.5 + (0.02 if i % 2 else -0.02), True)
        self.assertTrue(learner.certified(0))
        self.assertTrue(learner.certified(1))
        learner.observe(0, -5.0, True)
        self.assertFalse(learner.certified(0))
        self.assertEqual(learner.hairs[0].n, 1)
        self.assertTrue(learner.certified(1))


if __name__ == "__main__":
    unittest.main()
