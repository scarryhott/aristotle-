import json
from pathlib import Path
import tempfile
import unittest

from experiments.classical_vs_closure_asi import (
    instantiate_assumed_axiom_geometry,
    load_json,
    run_comparison,
)


class ClassicalVersusClosureASITest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.temporary = tempfile.TemporaryDirectory(prefix="test-classical-vs-closure-")
        cls.output = Path(cls.temporary.name)
        cls.result = run_comparison(cls.output)
        cls.fixed = load_json(cls.output / "fixed_frame_arm.json")
        cls.closure = load_json(cls.output / "closure_arm.json")
        cls.frame_a = load_json(cls.output / "frame_a_frozen.json")
        cls.frame_b = load_json(cls.output / "frame_b_frozen.json")
        cls.artifact_a = load_json(cls.output / "presentation_a_frozen.json")

    @classmethod
    def tearDownClass(cls) -> None:
        cls.temporary.cleanup()

    def test_frame_equality_is_frozen_before_candidate_search(self) -> None:
        receipts = [
            json.loads(line)
            for line in (self.output / "receipts.jsonl").read_text(encoding="utf-8").splitlines()
        ]
        stages = [item["stage"] for item in receipts]
        candidate_index = stages.index("CANDIDATE_FAMILY_FROZEN")
        self.assertLess(
            stages.index("FRAME_A_ASSUMPTION_INSTANTIATED_AND_FROZEN"),
            candidate_index,
        )
        self.assertLess(
            stages.index("FRAME_B_ASSUMPTION_INSTANTIATED_AND_FROZEN"),
            candidate_index,
        )
        self.assertEqual(stages[0], "COMPARISON_PRECOMMIT")
        self.assertTrue(
            receipts[0]["payload"]["geometry_assumptions_frozen_before_learning"]
        )

    def test_reference_frames_instantiate_and_audit_local_assumptions(self) -> None:
        for frame in (self.frame_a, self.frame_b):
            equality = frame["admitted_equality"]
            setoid = equality["setoid_certificate"]
            audit = frame["internal_unified_evaluation"]
            self.assertEqual(
                frame["assumption_status"], "ASSUMED_FOR_INTERNAL_EVALUATION"
            )
            self.assertEqual(
                frame["axiom_geometry_assumption"]["relation_kind"],
                "local_right_action_signature_equivalence",
            )
            self.assertTrue(frame["axiom_geometry_assumption_id"])
            self.assertEqual(
                equality["source"], "precommitted local axiom-geometry assumption"
            )
            self.assertFalse(frame["return_used_to_define_equality"])
            self.assertFalse(frame["candidate_translation_visible"])
            self.assertEqual(len(frame["occurrences"]), 16)
            self.assertEqual(len(equality["equivalence_classes"]), 8)
            self.assertTrue(all(len(item["members"]) == 2 for item in equality["equivalence_classes"]))
            self.assertEqual(setoid["reflexivity_cases"], 16)
            self.assertEqual(setoid["symmetry_cases"], 256)
            self.assertEqual(setoid["transitivity_cases"], 4096)
            self.assertEqual(setoid["failure_count"], 0)
            self.assertTrue(audit["evaluated_only_in_declared_local_geometry"])
            self.assertFalse(audit["external_normal_form_substituted"])
            self.assertEqual(audit["returning"]["cases"], 16)
            self.assertEqual(audit["grounded"]["cases"], 64)
            self.assertEqual(audit["operation_congruence"]["cases"], 1024)
            self.assertEqual(audit["presentation_reversal"]["cases"], 16)
            self.assertTrue(audit["passed"])

    def test_fixed_frame_baseline_is_strong_not_a_strawman(self) -> None:
        self.assertEqual(self.fixed["status"], "PASS")
        self.assertTrue(self.fixed["baseline_is_not_discrete_frame"])
        self.assertTrue(self.fixed["accepts_noncanonical_and_reversing_isomorphisms"])
        self.assertEqual(self.fixed["ordinary_structural_isomorphism_count"], 8)
        self.assertEqual(
            self.fixed["frame_relative_question_interface"]["status"],
            "NOT_MEASURED_BY_ARM",
        )
        self.assertFalse(
            self.fixed["frame_relative_question_interface"]["bare_open_label_emitted"]
        )

    def test_both_arms_receive_the_same_content_addressed_inputs(self) -> None:
        self.assertEqual(
            self.fixed["shared_manifest_sha256"], self.closure["shared_manifest_sha256"]
        )
        self.assertTrue(self.result["differential"]["same_frozen_inputs"])
        self.assertEqual(self.result["comparison_target"], "verification architecture over identical frozen artifacts")

    def test_geom_equiv_and_naturality_are_separate_gates(self) -> None:
        by_case = {case["case"]: case for case in self.closure["cases"]}
        collapse = by_case["equality_collapse"]["certificates"][0]
        twist = by_case["operation_twist"]["certificates"][0]

        self.assertEqual(collapse["geom_equiv"]["preservation_failure_count"], 0)
        self.assertGreater(collapse["geom_equiv"]["reflection_failure_count"], 0)
        self.assertFalse(collapse["geom_equiv"]["holds"])

        self.assertTrue(twist["geom_equiv"]["holds"])
        self.assertFalse(twist["naturality"]["holds"])
        self.assertGreater(twist["naturality"]["operation_failure_count"], 0)
        self.assertFalse(twist["admitted_translation"])
        self.assertEqual(
            twist["explicit_translational_form"]["geom_equiv_admission"]["status"],
            "ADMITTED",
        )
        self.assertEqual(
            twist["explicit_translational_form"]["closure_derivations"]
            ["operation_naturality"]["status"],
            "COUNTEREXAMPLE",
        )
        self.assertEqual(
            twist["explicit_translational_form"]["trans_frame_admission"],
            "REJECTED",
        )

    def test_all_coherent_forms_and_reversal_are_retained(self) -> None:
        by_case = {case["case"]: case for case in self.closure["cases"]}
        self.assertEqual(self.closure["structural_admitted_translation_count"], 8)
        self.assertEqual(by_case["natural_reversal"]["status"], "ADMITTED_TRANSLATION")
        self.assertFalse(by_case["natural_reversal"]["selected_for_episode"])
        self.assertTrue(
            all(
                certificate["geom_equiv"]["preservation_cases"] == 256
                and certificate["geom_equiv"]["reflection_cases"] == 256
                for certificate in by_case["structural_family"]["certificates"]
            )
        )

    def test_resolved_and_open_are_total_frame_question_relations(self) -> None:
        relations = self.closure["question_relations"]
        quotient = [item for item in relations if item["question_id"] == "quotient_identity"]
        order = [item for item in relations if item["question_id"] == "element_order"]
        constructor_closure = [
            item
            for item in relations
            if item["question_id"] == "presentation_constructor"
            and not item["frame_equality"].startswith("discrete")
        ]
        constructor_discrete = next(
            item
            for item in relations
            if item["question_id"] == "presentation_constructor"
            and item["frame_equality"].startswith("discrete")
        )

        self.assertTrue(all(item["resolved_in_frame"] for item in quotient + order))
        self.assertTrue(all(item["factorization"]["unique"] for item in quotient + order))
        self.assertTrue(all(item["open_in_frame"] for item in constructor_closure))
        self.assertTrue(
            all(
                item["open_witness"] is not None
                and item["open_witness"]["frame_equal"]
                and item["open_witness"]["left_value"] != item["open_witness"]["right_value"]
                for item in constructor_closure
            )
        )
        self.assertTrue(constructor_discrete["resolved_in_frame"])
        self.assertTrue(self.closure["all_open_records_have_separating_witnesses"])

    def test_pending_and_unselected_are_never_open(self) -> None:
        by_case = {case["case"]: case for case in self.closure["cases"]}
        self.assertEqual(by_case["partial_comparison"]["status"], "PENDING_COMPARISON")
        self.assertEqual(
            by_case["self_certification_only"]["status"], "UNSELECTED_COMPARISON"
        )
        self.assertEqual(
            by_case["partial_comparison"]["translation_lineage"]["candidate_T"][
                "state"
            ],
            "PARTIAL_PROPOSAL",
        )
        self.assertEqual(
            by_case["self_certification_only"]["translation_lineage"]["candidate_T"][
                "state"
            ],
            "ABSENT_SELF_CLAIM_ONLY",
        )

        def walk(value):
            if isinstance(value, dict):
                self.assertNotIn("reference_question_open", value)
                for nested in value.values():
                    walk(nested)
            elif isinstance(value, list):
                for nested in value:
                    walk(nested)

        walk(by_case["partial_comparison"])
        walk(by_case["self_certification_only"])

    def test_closure_is_explicitly_translational_through_every_derivation(self) -> None:
        source_id = self.frame_b["axiom_geometry_assumption_id"]
        target_id = self.frame_a["axiom_geometry_assumption_id"]
        for case in self.closure["cases"]:
            lineage = case["translation_lineage"]
            self.assertEqual(lineage["source_axiom_geometry_assumption_id"], source_id)
            self.assertEqual(lineage["target_axiom_geometry_assumption_id"], target_id)
            for certificate in case["certificates"]:
                form = certificate["explicit_translational_form"]
                self.assertEqual(form["source_axiom_geometry"]["assumption_id"], source_id)
                self.assertEqual(form["target_axiom_geometry"]["assumption_id"], target_id)
                self.assertIn("candidate_T", form)
                self.assertIn("geom_equiv_admission", form)
                self.assertIn("translation_tuple_T_phi_pi", form)
                self.assertEqual(
                    set(form["closure_derivations"]),
                    {
                        "W_quotient_return",
                        "E_extension_naturality",
                        "J_reversal_naturality",
                        "C_curvature_naturality",
                        "operation_naturality",
                        "quotient_resolution_and_openness",
                        "next_basis_transfer",
                    },
                )
        for relation in self.closure["question_relations"]:
            form = relation["explicit_relational_closure_form"]
            self.assertEqual(form["frame_id"], relation["frame_id"])
            self.assertFalse(form["bare_open_label"])
        self.assertTrue(self.closure["every_candidate_has_explicit_translational_form"])
        self.assertTrue(self.closure["every_question_has_explicit_relational_closure_form"])
        self.assertTrue(
            self.closure["next_basis"]["explicit_translation_lineage"][
                "admission_observed"
            ]
        )

    def test_selected_relation_transfers_one_next_basis_without_meta_token(self) -> None:
        self.assertTrue(self.closure["next_basis"]["axiom_geometry_basis_admitted"])
        self.assertEqual(self.closure["tokens_issued"], 1)
        self.assertEqual(self.result["comparison_layer_additional_tokens"], 0)
        self.assertTrue(self.result["comparative_hypothesis_supported_for_bounded_fixture"])
        self.assertEqual(self.result["frontier_agent_comparative_hypothesis"], "OPEN_AND_FALSIFIABLE")
        self.assertFalse(self.result["actual_asi_or_aristotle_run"])

    def test_frame_tampering_is_recomputed_not_trusted(self) -> None:
        tampered = json.loads(json.dumps(self.artifact_a))
        tampered["execution"]["operation_table"]["a0"]["a0"] = "a1"
        with self.assertRaises(ValueError):
            instantiate_assumed_axiom_geometry(
                tampered,
                load_json(Path(__file__).parents[1] / "benchmarks" / "classical_vs_closure" / "frame_a_protocol.json"),
            )

    def test_unknown_geometry_is_not_silently_normalized(self) -> None:
        protocol = load_json(
            Path(__file__).parents[1]
            / "benchmarks"
            / "classical_vs_closure"
            / "frame_a_protocol.json"
        )
        protocol["axiom_geometry_assumption"]["relation_kind"] = (
            "external_canonical_normal_form"
        )
        with self.assertRaisesRegex(ValueError, "not normalized or replaced"):
            instantiate_assumed_axiom_geometry(self.artifact_a, protocol)

    def test_replay_is_byte_identical(self) -> None:
        with tempfile.TemporaryDirectory(prefix="test-classical-vs-closure-replay-") as name:
            replay = Path(name)
            run_comparison(replay)
            expected = sorted(path.name for path in self.output.iterdir())
            observed = sorted(path.name for path in replay.iterdir())
            self.assertEqual(observed, expected)
            for name in expected:
                self.assertEqual((replay / name).read_bytes(), (self.output / name).read_bytes())


if __name__ == "__main__":
    unittest.main()
