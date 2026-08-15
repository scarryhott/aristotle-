from pathlib import Path
import unittest

from experiments.aristotle_d4_closure import (
    ClosureVerdict,
    correct_translator,
    d4_elements,
    evaluate_translator,
    normal_action,
    normal_multiply,
    permutation_compose,
    rotations_only_translator,
    wrong_sign_translator,
)


class D4ClosureTest(unittest.TestCase):
    def test_normal_action_is_a_homomorphism_exhaustively(self) -> None:
        elements = d4_elements()
        self.assertEqual(len(elements), 8)
        self.assertEqual(len({normal_action(value) for value in elements}), 8)
        for left in elements:
            for right in elements:
                self.assertEqual(
                    normal_action(normal_multiply(left, right)),
                    permutation_compose(normal_action(left), normal_action(right)),
                )

    def test_correct_candidate_closes(self) -> None:
        result = evaluate_translator("candidate", correct_translator)
        self.assertEqual(result["delta_C"], ClosureVerdict.TRUE.value)
        self.assertEqual(result["contradiction_count"], 0)
        self.assertEqual(result["unresolved_count"], 0)
        self.assertEqual(result["coverage"]["completed_ordered_products"], 64)

    def test_wrong_sign_has_counterexample(self) -> None:
        result = evaluate_translator("wrong", wrong_sign_translator)
        self.assertEqual(result["delta_C"], ClosureVerdict.FALSE.value)
        self.assertIsNotNone(result["first_contradiction"])

    def test_partial_candidate_stays_open(self) -> None:
        result = evaluate_translator("partial", rotations_only_translator)
        self.assertEqual(result["delta_C"], ClosureVerdict.OPEN.value)
        self.assertEqual(result["contradiction_count"], 0)
        self.assertGreater(result["unresolved_count"], 0)

    def test_false_precedes_open(self) -> None:
        def mixed(value):
            rotation, flip = value
            if flip:
                return None
            if rotation == 1:
                return normal_action((2, 0))
            return normal_action(value)

        result = evaluate_translator("mixed", mixed)
        self.assertEqual(result["delta_C"], ClosureVerdict.FALSE.value)
        self.assertGreater(result["unresolved_count"], 0)


if __name__ == "__main__":
    unittest.main()

