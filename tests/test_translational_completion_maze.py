from pathlib import Path
import json
import tempfile
import unittest

from experiments.translational_completion_maze import (
    EVIDENCE_ARTIFACTS,
    disclosed_full_line_artifact,
    digest_value,
    equality_alignment,
    file_digest,
    issue_admission_token,
    issue_bounded_topology_receipt,
    line_structure_certificate,
    load_json,
    materialize_frame,
    run,
    validate_receipt_chain,
)


class TranslationalCompletionMazeTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.temporary = tempfile.TemporaryDirectory(prefix="test-completion-maze-")
        cls.output = Path(cls.temporary.name)
        cls.result = run(cls.output)
        cls.frame_a = load_json(cls.output / "frame_a_frozen.json")
        cls.frame_b = load_json(cls.output / "frame_b_frozen.json")
        cls.analysis_a = load_json(cls.output / "frame_a_completion_topology.json")
        cls.analysis_b = load_json(cls.output / "frame_b_completion_topology.json")
        cls.translations = load_json(cls.output / "translation_family.json")
        cls.controls = load_json(cls.output / "completion_local_ivi_w_controls.json")

    @classmethod
    def tearDownClass(cls) -> None:
        cls.temporary.cleanup()

    def test_frame_equality_freezes_before_maze_and_completed_reach_realizes_it(self) -> None:
        for frame, artifact, line_filenames in (
            (
                self.frame_a,
                self.analysis_a,
                ("maze_a_forward_lines_frozen.json", "maze_a_return_lines_frozen.json"),
            ),
            (
                self.frame_b,
                self.analysis_b,
                ("maze_b_forward_lines_frozen.json", "maze_b_return_lines_frozen.json"),
            ),
        ):
            self.assertTrue(frame["admitted_equality"]["frozen_before_maze_completion"])
            self.assertEqual(frame["admitted_equality"]["equivalence_class_count"], 3)
            alignment = artifact["analysis"]["admitted_equality_alignment"]
            self.assertTrue(alignment["raw_reach_exactly_realizes_admitted_equality"])
            self.assertEqual(alignment["undercomplete_pair_count"], 0)
            self.assertEqual(alignment["overreach_pair_count"], 0)
            for line_filename in line_filenames:
                lines = load_json(self.output / line_filename)
                self.assertTrue(lines["frozen_after_local_equality"])
                self.assertFalse(lines["process_independence_claimed"])
                self.assertEqual(lines["parent_frozen_geometry_sha256"], digest_value(frame))

    def test_independent_return_changes_pending_reach_to_completion(self) -> None:
        for artifact in (self.analysis_a, self.analysis_b):
            before = artifact["pre_return_analysis"]
            after = artifact["analysis"]
            self.assertEqual(before["status"], "PENDING_INDEPENDENT_RETURN")
            self.assertFalse(before["translationally_complete"])
            self.assertIsNotNone(before["first_missing_return_witness"])
            self.assertGreater(
                before["admitted_equality_alignment"]["undercomplete_pair_count"], 0
            )
            self.assertTrue(after["translationally_complete"])
            self.assertTrue(after["all_generating_edges_have_return_paths"])
            self.assertEqual(after["symmetry_failure_count"], 0)

    def test_same_line_has_path_wall_polarity_and_return_uses_other_lines(self) -> None:
        for artifact in (self.analysis_a, self.analysis_b):
            semantics = artifact["analysis"]["line_semantics"]
            self.assertTrue(semantics["one_frozen_line_set"])
            self.assertEqual(semantics["line_count"], 48)
            self.assertEqual(semantics["direct_passage_count"], 48)
            self.assertEqual(semantics["inverse_wall_count"], 48)
            self.assertEqual(semantics["path_or_wall_exclusivity_failure_count"], 0)
            self.assertEqual(semantics["inverse_walls_relabeled_as_direct_edges"], 0)
            self.assertEqual(semantics["minimum_return_path_length"], 15)
            self.assertEqual(semantics["maximum_return_path_length"], 15)

    def test_completion_derives_an_actual_non_discrete_saturation_topology(self) -> None:
        for artifact in (self.analysis_a, self.analysis_b):
            topology = artifact["analysis"]["topology"]
            self.assertTrue(topology["topology_axioms_exhaustive_for_reference_partition"])
            self.assertEqual(topology["equivalence_class_count"], 3)
            self.assertEqual(topology["equivalence_class_sizes"], [16, 16, 16])
            self.assertEqual(topology["open_set_count"], 8)
            self.assertFalse(topology["discrete"])
            self.assertFalse(topology["whole_space_connected_in_standard_topological_sense"])
            self.assertEqual(topology["return_connected_fibre_count"], 3)

    def test_relational_question_factors_and_static_questions_have_open_witnesses(self) -> None:
        for artifact in (self.analysis_a, self.analysis_b):
            by_question = {item["question_id"]: item for item in artifact["questions"]}
            relational = by_question["same_returned_basis_as_translated_anchor"]
            self.assertTrue(relational["resolved_in_frame"])
            self.assertTrue(relational["factorization_unique"])
            self.assertEqual(len(relational["unique_quotient_factor"]), 3)
            for question_id in ("literal_first_pole", "literal_goal_stage"):
                opened = by_question[question_id]
                self.assertTrue(opened["open_in_frame"])
                self.assertFalse(opened["resolved_in_frame"])
                self.assertTrue(opened["open_witness"]["frame_equal"])
                self.assertTrue(opened["open_witness"]["separates_frame_equal_pair"])

    def test_return_episode_has_derived_pole_swap_monodromy(self) -> None:
        for artifact in (self.analysis_a, self.analysis_b):
            monodromy = artifact["return_monodromy"]
            self.assertEqual(monodromy["case_count"], 6)
            self.assertEqual(monodromy["nontrivial_occurrence_monodromy_count"], 6)
            self.assertEqual(monodromy["pole_swap_count"], 6)
            self.assertEqual(monodromy["returned_basis_identity_count"], 6)
            self.assertEqual(monodromy["two_episode_literal_return_count"], 6)
            self.assertTrue(
                all(case["one_episode_pole_swapped"] for case in monodromy["cases"])
            )
            self.assertEqual(
                monodromy["formal_holonomy_or_homotopy_status"],
                "PENDING_PRE_COHERENCE_PATH_LAYER",
            )

    def test_post_freeze_translation_preserves_topology_without_canonical_selection(self) -> None:
        self.assertEqual(self.translations["candidate_count"], 96)
        self.assertEqual(self.translations["geom_equiv_count"], 96)
        self.assertEqual(self.translations["fully_admitted_translation_count"], 12)
        self.assertFalse(self.translations["canonical_translation_selected"])
        self.assertEqual(self.translations["topology_transport_failure_count"], 0)
        self.assertEqual(self.translations["admitted_registered_question_failure_count"], 0)
        self.assertEqual(self.translations["admitted_registered_question_cases"], 1728)
        for form in self.translations["admitted_translations"]:
            self.assertTrue(form["full_admission"])
            self.assertTrue(form["registered_question_natural"])
            self.assertEqual(len(form["T"]), 48)
            self.assertEqual(len(form["phi"]), 3)
            self.assertEqual(len(form["pi"]), 2)

    def test_controls_keep_completion_local_ivi_w_and_alignment_distinct(self) -> None:
        cases = self.controls["cases"]
        self.assertTrue(
            cases["completion_with_local_ivi_w"]["translationally_complete"]
        )
        self.assertTrue(cases["completion_with_local_ivi_w"]["local_ivi_w_present"])
        self.assertTrue(
            cases["completion_with_local_ivi_w"][
                "faithful_nondiscrete_proxy_relative_to_frozen_frame"
            ]
        )
        self.assertTrue(
            cases["completion_without_local_ivi_w"]["translationally_complete"]
        )
        self.assertFalse(
            cases["completion_without_local_ivi_w"]["local_ivi_w_present"]
        )
        self.assertTrue(
            cases["local_ivi_w_without_completion"]["local_ivi_w_present"]
        )
        self.assertFalse(
            cases["local_ivi_w_without_completion"]["translationally_complete"]
        )
        self.assertFalse(
            cases["neither_completion_nor_local_ivi_w"]["local_ivi_w_present"]
        )
        self.assertFalse(
            cases["neither_completion_nor_local_ivi_w"]["translationally_complete"]
        )
        self.assertTrue(self.controls["all_six_cases_match_runtime_three_condition_gate"])
        self.assertTrue(self.controls["neither_condition_implies_the_other"])
        self.assertTrue(self.controls["undercomplete_witness_retained"])
        self.assertTrue(self.controls["overreach_witness_retained"])
        undercomplete = self.controls["frame_reach_alignment_controls"][
            "undercomplete_reach_relative_to_frozen_equality"
        ]
        self.assertTrue(undercomplete["translationally_complete"])
        self.assertTrue(undercomplete["local_ivi_w_present"])
        self.assertFalse(
            undercomplete["admitted_equality_alignment"][
                "raw_reach_exactly_realizes_admitted_equality"
            ]
        )
        self.assertFalse(
            undercomplete["runtime_gate_completion_local_ivi_w_and_alignment"]
        )
        self.assertTrue(undercomplete["proxy_matches_runtime_three_condition_gate"])

    def test_incomplete_reach_is_not_repaired_by_a_manufactured_quotient(self) -> None:
        for name in (
            "local_ivi_w_without_completion",
            "neither_completion_nor_local_ivi_w",
        ):
            case = self.controls["cases"][name]
            self.assertFalse(
                case["mutual_reach_quotient_faithfully_represents_raw_reach"]
            )
            self.assertIsNotNone(case["first_chain_lost_by_mutual_reach_quotient"])
            self.assertIsNotNone(
                case["first_return_invented_by_undirected_equivalence_closure"]
            )

    def test_receipt_is_downstream_not_causal(self) -> None:
        receipt = self.result["receipt_gates"]
        self.assertEqual(receipt["bounded_topology_receipt_count"], 1)
        self.assertEqual(receipt["actual_admission_token_count"], 0)
        self.assertTrue(receipt["at_most_one"])
        self.assertTrue(receipt["topology_unchanged_after_receipt_gate"])
        gates = load_json(self.output / "receipt_gates.json")
        bounded = gates["bounded_topology_receipt"]
        recomputation = bounded["topology_recomputation"]
        self.assertFalse(recomputation["receipt_used_as_input"])
        self.assertEqual(
            recomputation["topology_sha256_before_receipt_gate"],
            recomputation["topology_sha256_after_receipt_gate"],
        )
        self.assertEqual(
            recomputation["line_count_before_receipt_gate"],
            recomputation["line_count_after_receipt_gate"],
        )
        self.assertFalse(receipt["self_certified_without_completion"]["issued"])
        self.assertFalse(gates["admission_token"]["issued"])
        self.assertTrue(self.result["receipt_chain"]["ok"])
        self.assertEqual(self.result["receipt_chain"]["count"], 16)

    def test_receipt_and_admission_gates_reject_missing_conditions(self) -> None:
        rejected = issue_bounded_topology_receipt(
            completion=False,
            local_ivi_w=True,
            exact_alignment=False,
            topology_sha256="0" * 64,
            admitted_translation_count=0,
        )
        self.assertFalse(rejected["issued"])
        issued = issue_bounded_topology_receipt(
            completion=True,
            local_ivi_w=True,
            exact_alignment=True,
            topology_sha256="1" * 64,
            admitted_translation_count=12,
        )
        self.assertTrue(issued["issued"])
        self.assertFalse(
            issue_admission_token(
                return_process_independent=False,
                selected_translation=None,
                admitted_translation_ids=["candidate-0"],
            )["issued"]
        )
        self.assertTrue(
            issue_admission_token(
                return_process_independent=True,
                selected_translation="candidate-0",
                admitted_translation_ids=["candidate-0"],
            )["issued"]
        )
        self.assertFalse(
            issue_admission_token(
                return_process_independent=True,
                selected_translation="forged-candidate",
                admitted_translation_ids=["candidate-0"],
            )["issued"]
        )

    def test_line_structure_validator_rejects_role_tampering(self) -> None:
        disclosed = load_json(self.output / "maze_a_line_set_disclosed.json")
        frame = materialize_frame(self.frame_a, disclosed)
        self.assertTrue(line_structure_certificate(frame)["valid"])
        frame["line_set"][0]["inverse_reading"] = "passage"
        certificate = line_structure_certificate(frame)
        self.assertFalse(certificate["valid"])
        self.assertEqual(
            certificate["failures"]["path_or_wall_role_failure_count"], 1
        )

    def test_disclosure_rejects_wrong_parent_and_incomplete_union(self) -> None:
        forward = load_json(self.output / "maze_a_forward_lines_frozen.json")
        returned = load_json(self.output / "maze_a_return_lines_frozen.json")
        wrong_parent = json.loads(json.dumps(forward))
        wrong_parent["parent_frozen_geometry_sha256"] = "0" * 64
        with self.assertRaises(ValueError):
            disclosed_full_line_artifact(self.frame_a, wrong_parent, returned)
        incomplete_return = json.loads(json.dumps(returned))
        incomplete_return["line_set"].pop()
        with self.assertRaises(ValueError):
            disclosed_full_line_artifact(self.frame_a, forward, incomplete_return)

    def test_equality_alignment_rejects_overlapping_classes(self) -> None:
        with self.assertRaises(ValueError):
            equality_alignment(
                ["a", "b"],
                {("a", "a"), ("b", "b")},
                [["a", "b"], ["b"]],
            )

    def test_receipt_chain_rejects_a_forged_previous_link(self) -> None:
        records = [
            json.loads(line)
            for line in (self.output / "receipts.jsonl").read_text(encoding="utf-8").splitlines()
        ]
        records[1]["previous_receipt_sha256"] = "0" * 64
        self.assertFalse(validate_receipt_chain(records))

    def test_strong_classical_control_recomputes_the_same_finite_relations(self) -> None:
        baseline = load_json(self.output / "strong_classical_baseline.json")
        for result in baseline.values():
            self.assertFalse(result["process_independence_claimed"])
            self.assertTrue(result["classical_foundation_can_express_all_finite_certificates"])
            self.assertTrue(result["reach_exact_match"])
            self.assertTrue(result["component_exact_match"])
            self.assertTrue(result["topology_count_exact_match"])
            self.assertTrue(result["completion_exact_match"])

    def test_evidence_manifest_covers_every_nonmanifest_artifact(self) -> None:
        manifest = load_json(self.output / "evidence_manifest.json")
        self.assertEqual(manifest["artifact_count"], len(EVIDENCE_ARTIFACTS))
        by_path = {item["path"]: item for item in manifest["artifacts"]}
        self.assertEqual(set(by_path), set(EVIDENCE_ARTIFACTS))
        for name in EVIDENCE_ARTIFACTS:
            self.assertEqual(by_path[name]["sha256"], file_digest(self.output / name))
            self.assertEqual(by_path[name]["size_bytes"], (self.output / name).stat().st_size)

    def test_replay_is_byte_deterministic(self) -> None:
        with tempfile.TemporaryDirectory(prefix="test-completion-maze-replay-") as directory:
            replay = Path(directory)
            run(replay)
            expected = set(EVIDENCE_ARTIFACTS) | {"evidence_manifest.json"}
            self.assertEqual(
                {path.name for path in self.output.iterdir() if path.is_file()},
                expected,
            )
            self.assertEqual(
                {path.name for path in replay.iterdir() if path.is_file()},
                expected,
            )
            for filename in sorted(expected):
                self.assertEqual(
                    file_digest(self.output / filename),
                    file_digest(replay / filename),
                    filename,
                )


if __name__ == "__main__":
    unittest.main()
