import json
from pathlib import Path
import tempfile
import unittest

from experiments.full_stack_math_asi import (
    BENCHMARK,
    ClosureVerdict,
    evaluate_closure,
    load_json,
    run_full_stack,
    write_json,
)


class FullStackMathematicalAgentTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.temporary = tempfile.TemporaryDirectory(prefix="test-full-stack-d4-")
        cls.output = Path(cls.temporary.name)
        cls.result = run_full_stack(cls.output)
        cls.artifact_a = load_json(cls.output / "perspective_a_frozen.json")
        cls.artifact_b = load_json(cls.output / "perspective_b_frozen.json")

    @classmethod
    def tearDownClass(cls) -> None:
        cls.temporary.cleanup()

    def test_both_isolated_agents_learn_then_execute(self) -> None:
        for artifact in (self.artifact_a, self.artifact_b):
            self.assertEqual(artifact["execution"]["status"], "PASS")
            self.assertEqual(artifact["model"]["minimum_training_error"], 0)
            self.assertEqual(len(artifact["model"]["minimum_error_survivors"]), 1)
            self.assertGreater(artifact["execution"]["held_out_count"], 0)
            self.assertEqual(artifact["execution"]["held_out_error_count"], 0)
            self.assertEqual(artifact["execution"]["group_certificate"]["associativity_cases"], 512)
            self.assertTrue(artifact["execution"]["group_certificate"]["passed"])

    def test_post_hoc_translation_does_not_receive_complete_return(self) -> None:
        translator = load_json(self.output / "translator_relational_contact.json")
        self.assertFalse(translator["complete_return_W_visible"])
        self.assertEqual(translator["structural_isomorphism_count"], 8)
        self.assertEqual(translator["post_contact_candidate_count"], 1)
        self.assertIsNotNone(translator["selected_mapping"])

    def test_closure_gate_separates_true_false_and_open(self) -> None:
        observed = {case["case"]: case["delta_C"] for case in self.result["cases"]}
        self.assertEqual(
            observed,
            {
                "relational_contact": ClosureVerdict.TRUE.value,
                "structural_only": ClosureVerdict.OPEN.value,
                "adversarial_reverse_contact": ClosureVerdict.FALSE.value,
                "self_certification_only": ClosureVerdict.OPEN.value,
            },
        )

    def test_complete_return_is_withheld_until_external_gate(self) -> None:
        main = self.result["main_case"]
        self.assertEqual(main["coverage"]["completed_element_returns"], 8)
        self.assertEqual(main["coverage"]["completed_ordered_product_returns"], 64)
        self.assertIsNotNone(main["disclosure_after_return"])
        open_case = next(case for case in self.result["cases"] if case["case"] == "structural_only")
        self.assertIsNone(open_case["disclosure_after_return"])

    def test_token_and_next_basis_follow_independent_return(self) -> None:
        self.assertEqual(self.result["tokens_issued"], 1)
        self.assertTrue(self.result["token_bound_respected"])
        self.assertEqual(self.result["next_basis"]["status"], "PASS")
        self.assertEqual(
            self.result["next_basis"]["new_execution"]["observed_target_result"],
            self.result["next_basis"]["new_execution"]["expected_target_result"],
        )
        self.assertEqual(
            set(self.result["open_branches_retained"]),
            {"structural_only", "self_certification_only"},
        )

    def test_frozen_artifact_tampering_is_false(self) -> None:
        tampered_path = self.output / "tampered_a.json"
        tampered = json.loads(json.dumps(self.artifact_a))
        tampered["tamper_probe"] = True
        write_json(tampered_path, tampered)
        result = evaluate_closure(
            BENCHMARK / "precommit_return.json",
            tampered_path,
            self.output / "perspective_b_frozen.json",
            self.output / "translator_relational_contact.json",
        )
        self.assertEqual(result["delta_C"], ClosureVerdict.FALSE.value)
        self.assertEqual(result["first_contradiction"]["check"], "frozen_hash")

    def test_receipt_chain_is_closed(self) -> None:
        self.assertTrue(self.result["receipt_chain"]["ok"])
        self.assertEqual(self.result["receipt_chain"]["count"], 13)


if __name__ == "__main__":
    unittest.main()
