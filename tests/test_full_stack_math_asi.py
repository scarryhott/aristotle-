import json
from pathlib import Path
import tempfile
import unittest

from experiments.full_stack_math_asi import (
    BENCHMARK,
    evaluate_relative_equality,
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
        self.assertEqual(translator["relative_frame_form_count"], 1)
        self.assertIsNotNone(translator["selected_mapping"])

    def test_relative_equality_replaces_fixed_axiom_ambiguity(self) -> None:
        by_case = {case["case"]: case for case in self.result["cases"]}
        main = by_case["relational_contact"]["relative_equality"]
        reversal = by_case["relative_reversal"]["relative_equality"]
        family = by_case["structural_family"]["relative_equality"]
        deformation = by_case["non_natural_deformation"]["relative_equality"]
        self_claim = by_case["self_certification_only"]["relative_equality"]

        self.assertTrue(main["relative_equality_witnessed"])
        self.assertTrue(reversal["relative_equality_witnessed"])
        self.assertTrue(family["structural_family_realized"])
        self.assertEqual(family["coherent_frame_form_count"], 8)
        self.assertTrue(family["reference_question_open"])
        self.assertTrue(deformation["candidate_counterexample_witnessed"])
        self.assertTrue(self_claim["reference_question_open"])

    def test_all_translational_closure_operations_are_executed(self) -> None:
        main = self.result["main_case"]
        operations = main["selected_frame_operations"]
        laws = operations["laws"]
        self.assertTrue(operations["relative_equality_form_holds"])
        self.assertEqual(laws["T_ret_cases"], 16)
        self.assertEqual(laws["T_ext_cases"], 16)
        self.assertEqual(laws["T_J_cases"], 16)
        self.assertEqual(laws["T_C_cases"], 16)
        self.assertEqual(laws["ceq_iff_cases"], 256)
        self.assertEqual(laws["phi_operation_cases"], 64)
        self.assertTrue(all(value == 0 for key, value in laws.items() if key.endswith("failure_count")))
        self.assertTrue(operations["quotient_basis"]["quotient_equivalent_to_basis"])
        self.assertEqual(
            operations["universal_factorization"]["unique_factorizations_through_W"], 256
        )
        self.assertIsNotNone(main["relational_disclosure"])

    def test_relative_reversal_is_natural_not_contradictory(self) -> None:
        reversal = next(case for case in self.result["cases"] if case["case"] == "relative_reversal")
        operations = reversal["selected_frame_operations"]
        self.assertEqual(operations["orientation_translation_pi"], "reversed")
        self.assertTrue(operations["relative_equality_form_holds"])
        self.assertEqual(reversal["contradiction_count"], 0)

    def test_structural_family_is_relative_equality_not_internal_ambiguity(self) -> None:
        family = next(case for case in self.result["cases"] if case["case"] == "structural_family")
        self.assertEqual(len(family["structural_frame_forms"]), 8)
        self.assertTrue(all(form["relative_equality_form_holds"] for form in family["structural_frame_forms"]))
        self.assertFalse(family["basis_admission"]["admitted"])

    def test_token_and_next_basis_follow_independent_return(self) -> None:
        self.assertEqual(self.result["tokens_issued"], 1)
        self.assertTrue(self.result["token_bound_respected"])
        self.assertTrue(self.result["next_basis"]["relative_equality_basis_admitted"])
        self.assertEqual(
            self.result["next_basis"]["new_execution"]["observed_target_result"],
            self.result["next_basis"]["new_execution"]["expected_target_result"],
        )
        self.assertEqual(
            set(self.result["open_reference_forms_retained"]),
            {"structural_family", "non_natural_deformation", "self_certification_only"},
        )

    def test_frozen_artifact_tampering_has_counterexample_witness(self) -> None:
        tampered_path = self.output / "tampered_a.json"
        tampered = json.loads(json.dumps(self.artifact_a))
        tampered["tamper_probe"] = True
        write_json(tampered_path, tampered)
        result = evaluate_relative_equality(
            BENCHMARK / "precommit_return.json",
            tampered_path,
            self.output / "perspective_b_frozen.json",
            self.output / "translator_relational_contact.json",
        )
        self.assertTrue(result["relative_equality"]["candidate_counterexample_witnessed"])
        self.assertEqual(result["first_contradiction"]["check"], "frozen_hash")

    def test_receipt_chain_is_closed(self) -> None:
        self.assertTrue(self.result["receipt_chain"]["ok"])
        self.assertEqual(self.result["receipt_chain"]["count"], 15)


if __name__ == "__main__":
    unittest.main()
