import json
from pathlib import Path
import tempfile
import unittest

from experiments.full_stack_math_asi import file_digest, load_json
from experiments.three_part_assumption_interaction_asi import (
    BENCHMARK,
    _external_exact_certificate,
    instantiate_external_geometry,
    reveal_external_candidate_packet,
    reveal_external_packet,
    run_three_part_simulation,
    validate_external_candidate_packet,
    validate_external_packet,
)


class ThreePartAssumptionInteractionTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.temporary = tempfile.TemporaryDirectory(prefix="test-three-part-")
        cls.output = Path(cls.temporary.name)
        cls.result = run_three_part_simulation(cls.output)
        cls.part_1 = load_json(cls.output / "part_1_classical_stack.json")
        cls.part_2 = load_json(cls.output / "part_2_closure_native.json")
        cls.part_3 = load_json(cls.output / "part_3_external_interaction.json")
        cls.frames = load_json(cls.output / "external_frames_frozen.json")

    @classmethod
    def tearDownClass(cls) -> None:
        cls.temporary.cleanup()

    def test_three_parts_are_distinct_and_pass_the_bounded_fixture(self) -> None:
        self.assertEqual(self.result["overall_status"], "PASS")
        self.assertEqual(
            self.result["parts"],
            {
                "classical_full_stack": "PASS",
                "closure_native_translation": "PASS",
                "external_assumption_interaction": "PASS",
            },
        )
        self.assertFalse(self.result["actual_asi_or_aristotle_run"])
        self.assertEqual(
            self.result["arbitrary_external_assumption_preservation"], "NOT_CLAIMED"
        )

    def test_external_packet_is_committed_before_parts_and_revealed_after(self) -> None:
        receipts = [
            json.loads(line)
            for line in (self.output / "receipts.jsonl")
            .read_text(encoding="utf-8")
            .splitlines()
        ]
        stages = [receipt["stage"] for receipt in receipts]
        self.assertEqual(stages[0], "THREE_PART_PRECOMMIT")
        self.assertFalse(receipts[0]["payload"]["external_geometry_packet_parsed"])
        self.assertFalse(receipts[0]["payload"]["external_candidate_packet_parsed"])
        reveal = stages.index("EXTERNAL_GEOMETRY_PACKET_REVEALED")
        self.assertLess(stages.index("PART_1_CLASSICAL_STACK_FROZEN"), reveal)
        self.assertLess(stages.index("PART_2_CLOSURE_NATIVE_FROZEN"), reveal)
        self.assertTrue(receipts[reveal]["payload"]["registered_precommit_verified"])
        frame_freeze = stages.index("EXTERNAL_GEOMETRIES_INSTANTIATED_AND_FROZEN")
        candidate_reveal = stages.index("EXTERNAL_CANDIDATE_PACKET_REVEALED")
        candidate_freeze = stages.index("EXTERNAL_INTERACTION_CANDIDATES_FROZEN")
        self.assertLess(reveal, frame_freeze)
        self.assertLess(frame_freeze, candidate_reveal)
        self.assertLess(candidate_reveal, candidate_freeze)
        self.assertLess(candidate_freeze, stages.index("PART_3_EXTERNAL_INTERACTION_FROZEN"))
        self.assertFalse(receipts[candidate_freeze]["payload"]["verdicts_present"])
        self.assertTrue(
            self.part_1["external_geometry_or_candidate_packet_was_not_an_input"]
        )
        self.assertTrue(
            self.part_2["external_geometry_or_candidate_packet_was_not_an_input"]
        )

    def test_every_external_geometry_is_assumed_and_audited_in_its_own_terms(self) -> None:
        all_frames = [
            *self.frames["exact_frames"],
            self.frames["central_isolation_frame"],
        ]
        self.assertEqual(len(all_frames), 6)
        self.assertTrue(self.frames["all_frames_evaluated_in_own_declared_geometry"])
        self.assertFalse(self.frames["candidate_interactions_visible_during_instantiation"])
        for frame in all_frames:
            self.assertEqual(
                frame["assumption_status"], "ASSUMED_FOR_OWN_UNIFIED_EVALUATION"
            )
            audit = frame["internal_unified_evaluation"]
            self.assertTrue(audit["evaluated_only_in_declared_external_geometry"])
            self.assertFalse(audit["source_equality_substituted"])
            self.assertTrue(audit["declared_obligations_passed"])
            self.assertEqual(audit["checks"]["setoid"]["failure_count"], 0)
        by_name = {frame["assumption_name"]: frame for frame in all_frames}
        self.assertFalse(
            by_name["literal_isolation_split"]["internal_unified_evaluation"][
                "full_returning_grounded_closure_obligations_passed"
            ]
        )
        self.assertFalse(
            by_name["normal_subgroup_parity_collapse"][
                "internal_unified_evaluation"
            ]["full_returning_grounded_closure_obligations_passed"]
        )

    def test_exact_external_translation_has_full_closure_followthrough(self) -> None:
        cases = {case["case"]: case for case in self.part_3["exact_interactions"]}
        exact = cases["external_coordinate_reexpression"]
        self.assertEqual(exact["status"], "TRACE_PRESERVED")
        self.assertTrue(exact["geom_equiv"]["holds"])
        self.assertEqual(exact["geom_equiv"]["preservation_cases"], 256)
        self.assertEqual(exact["geom_equiv"]["reflection_cases"], 256)
        self.assertTrue(exact["naturality"]["holds"])
        form = exact["explicit_translational_form"]
        self.assertEqual(form["geom_equiv_admission"], "ADMITTED")
        self.assertEqual(form["translation_tuple_T_phi_pi"]["pi"], "reversed")
        self.assertEqual(
            set(form["closure_derivations"]),
            {"W", "E", "J", "C", "operation", "quotient_questions", "next_basis"},
        )
        self.assertTrue(form["closure_chain_complete"])

    def test_controls_separate_equality_naturality_and_missing_data(self) -> None:
        cases = {case["case"]: case for case in self.part_3["exact_interactions"]}
        split = cases["literal_isolation_split"]
        collapse = cases["normal_subgroup_parity_collapse"]
        twist = cases["external_basis_twist"]
        partial = cases["partial_external_interaction"]

        self.assertEqual(split["status"], "EQUALITY_OBSTRUCTION")
        self.assertGreater(split["geom_equiv"]["preservation_failure_count"], 0)
        self.assertEqual(collapse["status"], "EQUALITY_OBSTRUCTION")
        self.assertEqual(collapse["geom_equiv"]["preservation_failure_count"], 0)
        self.assertGreater(collapse["geom_equiv"]["reflection_failure_count"], 0)
        self.assertEqual(twist["status"], "NATURALITY_OBSTRUCTION")
        self.assertTrue(twist["geom_equiv"]["holds"])
        self.assertGreater(twist["naturality"]["operation_failure_count"], 0)
        self.assertEqual(partial["status"], "PENDING_COMPARISON")
        self.assertFalse(partial["geom_equiv"]["total"])
        for case in (split, collapse, twist, partial):
            self.assertTrue(case["non_admission_is_not_openness"])
            self.assertFalse(case["open_in_emitted"])

    def test_central_isolation_is_genuinely_larger_and_not_called_geom_equiv(self) -> None:
        central = self.frames["central_isolation_frame"]
        self.assertEqual(len(central["identity_basis"]), 16)
        self.assertEqual(len(central["occurrences"]), 32)
        self.assertEqual(len(central["admitted_equality"]["equivalence_classes"]), 16)
        trace = self.part_3["continuous_relational_identification"]
        self.assertEqual(len(trace["adjacent_relations"]), 4)
        native, coordinate, split, quotient = trace["adjacent_relations"]
        self.assertEqual(native["relation_kind"], "GEOM_EQUIV")
        self.assertEqual(coordinate["relation_kind"], "GEOM_EQUIV")
        self.assertEqual(split["relation_kind"], "SPLIT_EXTENSION")
        self.assertEqual(quotient["relation_kind"], "CLOSURE_QUOTIENT")
        self.assertTrue(split["typed_not_geom_equiv"])
        self.assertTrue(quotient["typed_not_geom_equiv"])
        self.assertTrue(split["coverage"]["source_total"])
        self.assertTrue(split["coverage"]["target_total"])
        self.assertEqual(split["coverage"]["unrelated_target_residues"], [])
        self.assertGreater(quotient["equality_law"]["collapsed_fibre_pair_count"], 0)
        self.assertEqual(quotient["equality_law"]["preservation_failure_count"], 0)
        self.assertEqual(split["orientation_translation_pi"], "preserved_on_embedding")
        self.assertEqual(quotient["orientation_translation_pi"], "reversed")
        for transition in (split, quotient):
            self.assertTrue(transition["closure_lineage_complete"])
            failure_counts = [
                value
                for key, value in transition["naturality"].items()
                if key.endswith("failure_count")
            ]
            self.assertTrue(failure_counts)
            self.assertTrue(all(value == 0 for value in failure_counts))

    def test_continuous_identification_has_no_isolation_gap(self) -> None:
        trace = self.part_3["continuous_relational_identification"]
        self.assertEqual(trace["status"], "TRACE_PRESERVED")
        self.assertEqual(trace["lineage_count"], 16)
        self.assertEqual(trace["split_relation_pair_count"], 64)
        self.assertTrue(trace["all_new_isolation_residues_relationally_identified"])
        self.assertEqual(trace["composite_coherence"]["failure_count"], 0)
        self.assertEqual(trace["composite_coherence"]["equality_cases"], 256)
        self.assertEqual(trace["composite_coherence"]["equality_failure_count"], 0)
        self.assertTrue(trace["composite_coherence"]["direct_recomputation_agrees"])
        self.assertEqual(
            trace["composite_coherence"]["full_relational_endpoint_pair_count"], 32
        )
        self.assertTrue(
            trace["composite_coherence"][
                "full_relational_composite_is_native_closure_relation"
            ]
        )
        self.assertTrue(trace["held_out_next_basis_replay"]["passed"])
        self.assertTrue(
            all(
                lineage["all_external_branches_recover_native_closure_identity"]
                and lineage["relational_composite_is_exactly_native_closure_fibre"]
                and lineage[
                    "selected_embedding_retraction_agrees_with_native_occurrence"
                ]
                for lineage in trace["occurrence_lineages"]
            )
        )

    def test_transported_resolution_and_openness_remain_relational(self) -> None:
        records = {
            record["question_id"]: record
            for record in self.part_3["transported_frame_question_relations"]
        }
        self.assertTrue(records["quotient_identity"]["resolved_in_frame"])
        self.assertTrue(records["element_order"]["resolved_in_frame"])
        presentation = records["presentation_constructor"]
        self.assertTrue(presentation["open_in_frame"])
        self.assertTrue(presentation["open_witness"]["frame_equal"])
        self.assertNotEqual(
            presentation["open_witness"]["left_value"],
            presentation["open_witness"]["right_value"],
        )
        self.assertFalse(presentation["bare_open_label"])
        self.assertTrue(self.part_3["all_open_records_have_separating_witnesses"])

    def test_external_continuation_mints_no_new_token(self) -> None:
        self.assertEqual(self.result["native_tokens_issued"], 1)
        self.assertEqual(self.result["external_interaction_additional_tokens"], 0)
        self.assertEqual(self.result["total_tokens_issued"], 1)
        self.assertEqual(self.part_3["tokens_issued"], 0)

    def test_unknown_external_geometry_is_not_silently_normalized(self) -> None:
        packet = load_json(BENCHMARK / "external_assumptions.json")
        packet["exact_geometries"][0]["equality_rule"] = "external_absolute_normal_form"
        with self.assertRaisesRegex(ValueError, "not normalized or replaced"):
            validate_external_packet(packet)

    def test_external_packet_commitment_mismatch_aborts_reveal(self) -> None:
        packet_path = BENCHMARK / "external_assumptions.json"
        with self.assertRaisesRegex(ValueError, "commitment mismatch"):
            reveal_external_packet(packet_path, "0" * 64)

    def test_candidate_packet_is_separate_and_commitment_checked(self) -> None:
        geometry = load_json(BENCHMARK / "external_assumptions.json")
        geometry_ids = {
            item["assumption_id"] for item in geometry["exact_geometries"]
        }
        candidate_path = BENCHMARK / "external_candidates.json"
        candidate = load_json(candidate_path)
        validate_external_candidate_packet(candidate, geometry_ids)
        with self.assertRaisesRegex(ValueError, "commitment mismatch"):
            reveal_external_candidate_packet(candidate_path, "0" * 64, geometry_ids)

    def test_missing_pi_cannot_forge_an_admitted_translation(self) -> None:
        artifact = load_json(self.output / "presentation_a_frozen.json")
        source_frame = load_json(self.output / "frame_a_frozen.json")
        target_frame = next(
            frame
            for frame in self.frames["exact_frames"]
            if frame["assumption_name"] == "external_coordinate_reexpression"
        )
        geometry = next(
            item
            for item in load_json(BENCHMARK / "external_assumptions.json")[
                "exact_geometries"
            ]
            if item["assumption_id"] == "external_coordinate_reexpression"
        )
        proposal = next(
            item
            for item in load_json(BENCHMARK / "external_candidates.json")[
                "candidate_proposals"
            ]
            if item["assumption_id"] == "external_coordinate_reexpression"
        )
        candidate = load_json(self.output / "external_candidates_frozen.json")[
            "candidates"
        ]["external_coordinate_reexpression"]
        candidate["orientation_proposal"] = None
        certificate = _external_exact_certificate(
            artifact, source_frame, target_frame, geometry, proposal, candidate
        )
        self.assertTrue(certificate["geom_equiv"]["holds"])
        self.assertEqual(certificate["status"], "NATURALITY_OBSTRUCTION")
        self.assertFalse(certificate["naturality"]["holds"])
        self.assertGreater(
            certificate["naturality"]["translation_tuple_failure_count"], 0
        )
        self.assertIsNone(
            certificate["explicit_translational_form"]["translation_tuple_T_phi_pi"]
        )

    def test_instantiator_rejects_an_undeclared_rule(self) -> None:
        artifact = load_json(self.output / "presentation_a_frozen.json")
        assumption = load_json(BENCHMARK / "external_assumptions.json")[
            "exact_geometries"
        ][0]
        assumption["equality_rule"] = "unknown_geometry"
        with self.assertRaisesRegex(ValueError, "not normalized"):
            instantiate_external_geometry(artifact, assumption)

    def test_replay_is_byte_identical(self) -> None:
        with tempfile.TemporaryDirectory(prefix="test-three-part-replay-") as name:
            replay = Path(name)
            run_three_part_simulation(replay)
            expected = sorted(path.name for path in self.output.iterdir())
            observed = sorted(path.name for path in replay.iterdir())
            self.assertEqual(observed, expected)
            for filename in expected:
                self.assertEqual(
                    (self.output / filename).read_bytes(),
                    (replay / filename).read_bytes(),
                )


if __name__ == "__main__":
    unittest.main()
