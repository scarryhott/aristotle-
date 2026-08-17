import json
from pathlib import Path
import tempfile
import unittest

from experiments.full_stack_math_asi import (
    BENCHMARK,
    evaluate_axiom_geometry,
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
        self.assertEqual(translator["axiom_geometry_equivalence_count"], 1)
        self.assertIsNotNone(translator["selected_mapping"])

    def test_axiom_geometry_equivalence_precedes_question_classification(self) -> None:
        by_case = {case["case"]: case for case in self.result["cases"]}
        main = by_case["relational_contact"]["axiom_geometry_relation"]
        reversal = by_case["relative_reversal"]["axiom_geometry_relation"]
        family = by_case["structural_family"]["axiom_geometry_relation"]
        deformation = by_case["non_natural_deformation"]["axiom_geometry_relation"]
        self_claim = by_case["self_certification_only"]["axiom_geometry_relation"]

        self.assertTrue(main["selected_by_independent_contact"])
        self.assertTrue(main["selected_comparison_is_geom_equiv"])
        self.assertTrue(main["selected_comparison_is_natural"])
        self.assertTrue(reversal["selected_by_independent_contact"])
        self.assertTrue(family["axiom_geometry_groupoid_realized"])
        self.assertTrue(family["translational_closure_family_realized"])
        self.assertEqual(family["coherent_geom_equiv_count"], 8)
        self.assertFalse(family["selected_by_independent_contact"])
        self.assertTrue(deformation["candidate_counterexample_witnessed"])
        self.assertFalse(self_claim["selected_by_independent_contact"])
        self.assertNotIn("reference_question_open", main)

    def test_all_translational_closure_operations_are_executed(self) -> None:
        main = self.result["main_case"]
        operations = main["selected_geom_equiv"]
        laws = operations["laws"]
        self.assertTrue(operations["axiom_geometry_equivalence_holds"])
        self.assertTrue(operations["translational_naturality_holds"])
        self.assertEqual(laws["T_ret_cases"], 16)
        self.assertEqual(laws["T_ext_cases"], 16)
        self.assertEqual(laws["T_J_cases"], 16)
        self.assertEqual(laws["T_C_cases"], 16)
        self.assertEqual(laws["geom_equiv_preservation_cases"], 256)
        self.assertEqual(laws["geom_equiv_reflection_cases"], 256)
        self.assertEqual(laws["phi_operation_cases"], 64)
        self.assertTrue(all(value == 0 for key, value in laws.items() if key.endswith("failure_count")))
        self.assertTrue(operations["quotient_basis"]["quotient_equivalent_to_basis"])
        self.assertEqual(
            operations["universal_factorization"]["unique_factorizations_through_W"], 256
        )
        self.assertIsNotNone(main["relational_disclosure"])

    def test_relative_reversal_is_natural_not_contradictory(self) -> None:
        reversal = next(case for case in self.result["cases"] if case["case"] == "relative_reversal")
        operations = reversal["selected_geom_equiv"]
        self.assertEqual(operations["orientation_translation_pi"], "reversed")
        self.assertTrue(operations["axiom_geometry_equivalence_holds"])
        self.assertTrue(operations["translational_naturality_holds"])
        self.assertEqual(reversal["contradiction_count"], 0)

    def test_structural_family_is_a_geom_equiv_groupoid_not_internal_ambiguity(self) -> None:
        family = next(case for case in self.result["cases"] if case["case"] == "structural_family")
        self.assertEqual(len(family["structural_geom_equivs"]), 8)
        self.assertTrue(
            all(form["axiom_geometry_equivalence_holds"] for form in family["structural_geom_equivs"])
        )
        self.assertTrue(
            all(form["translational_naturality_holds"] for form in family["structural_geom_equivs"])
        )
        self.assertTrue(
            all(form["question_transport"]["language_independent"] for form in family["structural_geom_equivs"])
        )
        self.assertFalse(family["basis_admission"]["admitted"])

    def test_resolution_and_openness_are_frame_question_relations(self) -> None:
        relations = self.result["main_case"]["frame_conditional_questions"]
        returned = next(
            relation for relation in relations if relation["question_id"] == "returned_identity"
        )
        pole_closure = next(
            relation
            for relation in relations
            if relation["question_id"] == "literal_pole_presentation"
            and relation["frame_equality"].startswith("closure")
        )
        pole_discrete = next(
            relation
            for relation in relations
            if relation["question_id"] == "literal_pole_presentation"
            and relation["frame_equality"].startswith("discrete")
        )

        self.assertTrue(returned["resolved_in_frame"])
        self.assertTrue(returned["factorization"]["unique"])
        self.assertTrue(pole_closure["open_in_frame"])
        self.assertTrue(pole_closure["open_witness"]["frame_equal"])
        self.assertTrue(pole_discrete["resolved_in_frame"])
        self.assertEqual(returned["equality_comparisons"], 256)
        self.assertEqual(pole_closure["equality_comparisons"], 256)

        def walk(value):
            if isinstance(value, dict):
                self.assertNotIn("reference_question_open", value)
                if "open_in_frame" in value:
                    self.assertIn("frame_id", value)
                    self.assertIn("frame_equality", value)
                    self.assertIn("question_id", value)
                for nested in value.values():
                    walk(nested)
            elif isinstance(value, list):
                for nested in value:
                    walk(nested)

        walk(self.result)

    def test_token_and_next_basis_follow_independent_return(self) -> None:
        self.assertEqual(self.result["tokens_issued"], 1)
        self.assertTrue(self.result["token_bound_respected"])
        self.assertTrue(self.result["next_basis"]["axiom_geometry_basis_admitted"])
        self.assertEqual(
            self.result["next_basis"]["new_execution"]["observed_target_result"],
            self.result["next_basis"]["new_execution"]["expected_target_result"],
        )
        self.assertEqual(
            set(self.result["unselected_or_rejected_comparisons"]),
            {"structural_family", "non_natural_deformation", "self_certification_only"},
        )

    def test_frozen_artifact_tampering_has_counterexample_witness(self) -> None:
        tampered_path = self.output / "tampered_a.json"
        tampered = json.loads(json.dumps(self.artifact_a))
        tampered["tamper_probe"] = True
        write_json(tampered_path, tampered)
        result = evaluate_axiom_geometry(
            BENCHMARK / "precommit_return.json",
            tampered_path,
            self.output / "perspective_b_frozen.json",
            self.output / "translator_relational_contact.json",
        )
        self.assertTrue(result["axiom_geometry_relation"]["candidate_counterexample_witnessed"])
        self.assertEqual(result["first_contradiction"]["check"], "frozen_hash")

    def test_receipt_chain_is_closed(self) -> None:
        self.assertTrue(self.result["receipt_chain"]["ok"])
        self.assertEqual(self.result["receipt_chain"]["count"], 15)


if __name__ == "__main__":
    unittest.main()
