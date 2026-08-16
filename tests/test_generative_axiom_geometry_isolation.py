import json
from pathlib import Path
import shutil
import tempfile
import unittest

from experiments.full_stack_math_asi import file_digest, load_json
from experiments.generative_axiom_geometry_isolation import (
    BENCHMARK,
    _evaluate_translation_candidate,
    _raw_local_assay,
    run_experiment,
    verify_frozen_artifacts,
)


class GenerativeAxiomGeometryIsolationTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.temporary = tempfile.TemporaryDirectory(prefix="test-generative-isolation-")
        cls.output = Path(cls.temporary.name)
        cls.result = run_experiment(cls.output)
        cls.verifier_path = cls.output / cls.result["verifier_artifact"]["path"]
        cls.verifier = load_json(cls.verifier_path)
        cls.artifact_a_path = cls.output / cls.result["generator_artifacts"]["A"]["path"]
        cls.artifact_b_path = cls.output / cls.result["generator_artifacts"]["B"]["path"]
        cls.artifact_a = load_json(cls.artifact_a_path)
        cls.artifact_b = load_json(cls.artifact_b_path)

    @classmethod
    def tearDownClass(cls) -> None:
        cls.temporary.cleanup()

    def test_causal_receipt_order_freezes_both_frames_before_disclosure(self) -> None:
        receipts = [
            json.loads(line)
            for line in (self.output / "receipts.jsonl")
            .read_text(encoding="utf-8")
            .splitlines()
        ]
        stages = [item["stage"] for item in receipts]
        self.assertEqual(stages[0], "GENERATIVE_PROTOCOLS_PRECOMMITTED")
        freeze_a = stages.index("AGENT_A_LOCAL_GEOMETRY_FROZEN")
        freeze_b = stages.index("AGENT_B_LOCAL_GEOMETRY_FROZEN")
        disclosure = stages.index("BOTH_ARTIFACTS_DISCLOSED_TO_VERIFIER_ONLY_AFTER_FREEZE")
        verifier = stages.index("POST_FREEZE_VERIFIER_RESULT_FROZEN")
        self.assertLess(freeze_a, disclosure)
        self.assertLess(freeze_b, disclosure)
        self.assertLess(disclosure, verifier)
        precommit = receipts[0]["payload"]
        self.assertFalse(precommit["cross_language_dictionary_present"])
        self.assertFalse(precommit["preselected_translation_present"])
        self.assertTrue(precommit["raw_artifact_hashes_registered_before_assay_or_comparison"])

    def test_generators_have_disjoint_declared_inputs(self) -> None:
        self.assertEqual(
            self.artifact_a["visible_inputs"], ["objective.json", "agent_a_context.json"]
        )
        self.assertEqual(
            self.artifact_b["visible_inputs"], ["objective.json", "agent_b_context.json"]
        )
        for artifact in (self.artifact_a, self.artifact_b):
            self.assertFalse(artifact["other_agent_artifact_visible"])
            self.assertFalse(artifact["verifier_protocol_visible"])
            self.assertTrue(artifact["internal_unified_evaluation"]["passed"])
        self.assertNotEqual(
            self.artifact_a["context_file_sha256"],
            self.artifact_b["context_file_sha256"],
        )

    def test_each_curvature_map_is_a_return_preserving_idempotent(self) -> None:
        self.assertNotEqual(
            self.artifact_a["axiom_geometry_assumption"]["curvature_representative_pole"],
            self.artifact_b["axiom_geometry_assumption"]["curvature_representative_pole"],
        )
        for artifact in (self.artifact_a, self.artifact_b):
            audit = artifact["internal_unified_evaluation"]
            self.assertEqual(audit["failure_counts"]["C_idempotence"], 0)
            self.assertEqual(audit["failure_counts"]["C_return_preservation"], 0)
            for occurrence, target in artifact["C"].items():
                self.assertEqual(artifact["C"][target], target)
                self.assertEqual(artifact["W"][target], artifact["W"][occurrence])

    def test_strong_classical_baseline_retains_all_ordinary_isomorphisms(self) -> None:
        baseline = self.verifier["strong_classical_post_disclosure_baseline"]
        local = self.verifier["comparison_interpretations"][
            "classical_well_defined_isolation"
        ]
        self.assertEqual(baseline["ordinary_group_isomorphism_count"], 6)
        self.assertEqual(len(baseline["ordinary_group_isomorphism_phi_ids"]), 6)
        self.assertTrue(baseline["accepts_every_operation_preserving_phi"])
        self.assertEqual(local["status"], "BOTH_LOCALLY_WELL_DEFINED")
        self.assertFalse(local["cross_frame_identity_asserted_by_local_checks"])

    def test_exhaustive_post_freeze_search_separates_geom_equiv_and_naturality(self) -> None:
        enumeration = self.verifier["candidate_enumeration"]
        self.assertEqual(enumeration["basis_bijection_count"], 720)
        self.assertEqual(enumeration["orientation_maps_per_bijection"], 2)
        self.assertEqual(enumeration["raw_T_phi_pi_count"], 1440)
        self.assertEqual(
            enumeration["status_histogram"],
            {"ADMITTED_NATURAL_TRANSLATION": 6, "NATURALITY_OBSTRUCTION": 1434},
        )
        self.assertFalse(enumeration["questions_or_held_out_used_during_enumeration"])
        self.assertEqual(self.verifier["admitted_natural_translation_count"], 6)
        for candidate in self.verifier["admitted_natural_translations"]:
            form = candidate["translation_tuple_T_phi_pi"]
            self.assertEqual(form["pi"], "reversed")
            self.assertTrue(candidate["geom_equiv"]["holds"])
            self.assertTrue(candidate["naturality"]["holds"])
            self.assertTrue(candidate["totality_and_bijection"]["T_phi_pi_coherent"])
            self.assertTrue(candidate["downstream_transport"]["passed"])

    def test_resolved_and_open_questions_are_frame_qualified(self) -> None:
        interpretation = self.verifier["comparison_interpretations"][
            "translational_open_isolation"
        ]
        self.assertEqual(
            interpretation["status"], "OPEN_IN_BOTH_FRAMES_AND_TRANSLATION_INVARIANT"
        )
        self.assertTrue(interpretation["every_admitted_translation_preserves_open_status"])
        self.assertFalse(interpretation["missing_or_rejected_comparison_called_open"])
        for role in ("agent_a_open_witness", "agent_b_open_witness"):
            witness = interpretation[role]
            self.assertTrue(witness["frame_equal"])
            self.assertNotEqual(witness["left_value"], witness["right_value"])
        for artifact in (self.artifact_a, self.artifact_b):
            for relation in artifact["question_relations"]:
                self.assertTrue(relation["total"])
                if relation["open_in_frame"]:
                    self.assertIsNotNone(relation["open_witness"])
                    self.assertFalse(relation["bare_open_label"])
                else:
                    self.assertTrue(relation["factorization"]["through_frame_quotient"])

    def test_natural_existence_is_witnessed_but_not_canonically_selected(self) -> None:
        interpretation = self.verifier["comparison_interpretations"][
            "natural_existential_conditional"
        ]
        self.assertEqual(interpretation["status"], "CONDITIONALLY_WITNESSED")
        self.assertEqual(interpretation["natural_translation_form_count"], 6)
        self.assertEqual(len(interpretation["existence_witness_ids"]), 6)
        self.assertFalse(interpretation["unique_translation_claimed"])
        self.assertFalse(interpretation["canonical_translation_selected"])
        self.assertEqual(self.result["tokens_issued"], 0)

    def test_adversaries_produce_typed_obstructions_not_open_labels(self) -> None:
        controls = self.verifier["adversarial_controls"]
        self.assertEqual(controls["equality_collapse"]["status"], "EQUALITY_OBSTRUCTION")
        self.assertGreater(
            controls["equality_collapse"]["geom_equiv"]["reflection_failure_count"], 0
        )
        self.assertEqual(controls["operation_twist"]["status"], "NATURALITY_OBSTRUCTION")
        self.assertTrue(controls["operation_twist"]["geom_equiv"]["holds"])
        self.assertEqual(controls["partial_comparison"]["status"], "PENDING_COMPARISON")
        self.assertEqual(controls["missing_orientation_pi"]["status"], "SCHEMA_OBSTRUCTION")
        self.assertEqual(controls["T_phi_mismatch"]["status"], "NATURALITY_OBSTRUCTION")
        for control in controls.values():
            self.assertFalse(control.get("open_in_emitted", False))

    def test_d4_q8_control_has_explicit_form_and_no_natural_translation(self) -> None:
        control = self.verifier["adversarial_controls"]["D4_Q8_free_choice_contrast"]
        self.assertTrue(control["D4_local_group_valid"])
        self.assertTrue(control["Q8_local_group_valid"])
        self.assertEqual(control["equality_fibre_geom_equiv_form_count"], 80640)
        self.assertEqual(control["operation_natural_translation_count"], 0)
        self.assertEqual(control["status"], "NATURALITY_OBSTRUCTION")
        form = control["explicit_first_control_form"]
        self.assertEqual(form["pi"], "preserved")
        self.assertEqual(len(form["phi"]), 8)
        self.assertEqual(len(form["T"]), 16)
        self.assertIsNotNone(form["operation_counterexample"])

    def test_raw_fresh_agents_are_not_normalized_into_comparability(self) -> None:
        assay = load_json(self.output / "raw_generation_assay.json")
        self.assertEqual(
            assay["comparison"]["status"], "CARDINALITY_GEOM_EQUIV_OBSTRUCTION"
        )
        self.assertFalse(assay["comparison"]["candidate_enumeration_started"])
        self.assertFalse(assay["comparison"]["naturality_search_started"])
        self.assertFalse(assay["comparison"]["global_nonexistence_claimed"])
        self.assertFalse(assay["comparison"]["open_in_emitted"])
        self.assertTrue(assay["comparison"]["no_geometry_was_normalized_or_replaced"])
        raw_a = assay["raw_artifacts"]["A"]
        raw_b = assay["raw_artifacts"]["B"]
        self.assertTrue(raw_a["bytes_preserved"] and raw_b["bytes_preserved"])
        self.assertEqual(raw_a["assay"]["carrier_size"], 8)
        self.assertEqual(raw_b["assay"]["carrier_size"], 6)
        self.assertEqual(
            raw_a["assay"]["trans_frame_interface_status"],
            "OUTSIDE_REGISTERED_TRANS_FRAME_INTERFACE",
        )
        self.assertEqual(
            raw_b["assay"]["trans_frame_interface_status"],
            "REGISTERED_TRANS_FRAME_INTERFACE",
        )

    def test_raw_word_geometry_remains_outside_finite_interface(self) -> None:
        assay = load_json(self.output / "raw_generation_interface_variant_assay.json")
        raw_b = assay["raw_artifacts"]["B"]["assay"]
        self.assertEqual(raw_b["local_group_kernel_status"], "VALID_FINITE_GROUP")
        self.assertTrue(raw_b["declares_nonfinite_occurrence_domain"])
        self.assertEqual(
            raw_b["reference_frame_interface_status"],
            "OUTSIDE_REGISTERED_FINITE_REFERENCE_FRAME_INTERFACE",
        )
        self.assertEqual(
            assay["comparison"]["status"],
            "TRANSLATOR_SEARCH_NOT_RUN_INTERFACE_BOUNDARY",
        )
        self.assertFalse(assay["comparison"]["open_in_emitted"])

    def test_manifest_tampering_aborts_before_candidate_search(self) -> None:
        with tempfile.TemporaryDirectory(prefix="test-generative-tamper-") as name:
            target = Path(name)
            artifact_a = target / self.artifact_a_path.name
            artifact_b = target / self.artifact_b_path.name
            manifest = target / "disclosure_manifest.json"
            shutil.copyfile(self.artifact_a_path, artifact_a)
            shutil.copyfile(self.artifact_b_path, artifact_b)
            shutil.copyfile(self.output / "disclosure_manifest.json", manifest)
            tampered = load_json(artifact_a)
            tampered["solution_artifact"]["solutions"] = []
            artifact_a.write_text(json.dumps(tampered), encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "immutable disclosure manifest mismatch"):
                verify_frozen_artifacts(
                    BENCHMARK / "objective.json",
                    BENCHMARK / "verifier_protocol.json",
                    artifact_a,
                    artifact_b,
                    manifest,
                )

    def test_missing_pi_cannot_be_admitted(self) -> None:
        valid = self.verifier["admitted_natural_translations"][0][
            "translation_tuple_T_phi_pi"
        ]
        certificate = _evaluate_translation_candidate(
            self.artifact_b,
            self.artifact_a,
            valid["phi"],
            None,
            supplied_T=valid["T"],
        )
        self.assertEqual(certificate["status"], "SCHEMA_OBSTRUCTION")
        self.assertFalse(certificate["geom_equiv"]["holds"])
        self.assertFalse(certificate["open_in_emitted"])

    def test_raw_assay_recomputes_local_group_validity(self) -> None:
        _, word_assay = _raw_local_assay(BENCHMARK / "raw_agent_b.json")
        self.assertEqual(word_assay["local_group_kernel_status"], "VALID_FINITE_GROUP")
        self.assertTrue(word_assay["local_group_certificate"]["passed"])
        self.assertTrue(word_assay["declares_nonfinite_occurrence_domain"])
        self.assertFalse(word_assay["registered_finite_reference_frame_interface"])

    def test_replay_is_byte_identical(self) -> None:
        with tempfile.TemporaryDirectory(prefix="test-generative-replay-") as name:
            replay = Path(name)
            result = run_experiment(replay)
            self.assertEqual(result["status"], "PASS")
            expected = sorted(path.name for path in self.output.iterdir())
            observed = sorted(path.name for path in replay.iterdir())
            self.assertEqual(observed, expected)
            for filename in expected:
                self.assertEqual(
                    (self.output / filename).read_bytes(),
                    (replay / filename).read_bytes(),
                )

    def test_committed_reference_hashes_match(self) -> None:
        self.assertEqual(
            file_digest(self.output / "result.json"),
            "d06902a14c55c06651f3c607f4ce22fc02e30da2349c5fd174cdf62f9431b8d3",
        )
        self.assertEqual(
            file_digest(self.verifier_path),
            "9b430e9f3035605b53f6272e60ea723d0471777c6f4d773a615be86d2299dd01",
        )
        self.assertEqual(
            self.result["receipt_chain"]["head"],
            "b9637680304eb8421fcefb4502b8b610a3cf060404cf4ddb8dc6908dbab21512",
        )


if __name__ == "__main__":
    unittest.main()
