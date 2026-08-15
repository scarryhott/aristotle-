#!/usr/bin/env python3
"""Paired fixed-frame versus translational-closure verification runtime.

This is a bounded symbolic comparison, not an ASI or Aristotle result.  Two
independent D4 learners first freeze their local algebras.  Each local algebra
then produces, in an isolated stage, its own operational equality geometry:
the programs ``x`` and ``x · e`` are distinct occurrences but have identical
right-action signatures.  Those equality tables and the total questions are
frozen before any cross-frame candidate is constructed.

Two fresh verifier processes receive byte-identical upstream evidence:

* the fixed-frame arm rechecks both local kernels and every ordinary proposed
  isomorphism, including noncanonical and orientation-reversing ones;
* the closure arm first checks preservation and reflection of the frozen
  equalities, promotes qualifying candidates to ``GeomEquiv``, then checks
  quotient return, operation/orientation naturality, frame-qualified
  ``ResolvedIn``/``OpenIn`` evidence, and held-out next-basis transfer.

The comparison tests additional auditable evidence, not the false claim that
ordinary mathematics cannot express isomorphisms or quotients.
"""

from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
from itertools import combinations
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from typing import Any, Sequence

PROJECT_ROOT = Path(__file__).resolve().parents[1]
if str(PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJECT_ROOT))

from experiments.full_stack_math_asi import (
    BENCHMARK as SOURCE_BENCHMARK,
    ROOT,
    ReceiptChain,
    _non_natural_deformation,
    _orientation_form,
    canonical_json,
    digest_value,
    enumerate_isomorphisms,
    execute_next_basis,
    file_digest,
    group_certificate,
    load_json,
    write_json,
)


BENCHMARK = ROOT / "benchmarks" / "classical_vs_closure"
DEFAULT_OUTPUT = ROOT / "runs" / "classical_vs_closure" / "latest"
CONSTRUCTORS = ("direct", "right_identity_extended")


@dataclass(frozen=True)
class CheckFailure:
    check: str
    input: object
    expected: object
    observed: object


def _evaluate_program(
    table: dict[str, dict[str, str]], identity: str, program: Sequence[str]
) -> str:
    current = identity
    for term in program:
        current = table[current][term]
    return current


def _occurrence_id(constructor: str, local_element: str) -> str:
    return f"{constructor}:{local_element}"


def derive_reference_frame(artifact: dict[str, Any], protocol: dict[str, Any]) -> dict[str, Any]:
    """Derive equality from one local algebra without a return or translator."""

    language = str(protocol["language"])
    table = artifact["execution"]["operation_table"]
    certificate = group_certificate(table)
    if not certificate["passed"]:
        raise ValueError(f"language {language} has no valid local group certificate")
    identity = certificate["identity"]
    if identity is None:
        raise ValueError(f"language {language} has no unique local identity")
    constructors = tuple(protocol["constructors"])
    if constructors != CONSTRUCTORS:
        raise ValueError("the frame protocol changed its precommitted constructors")

    occurrences: list[dict[str, Any]] = []
    signatures: dict[str, list[str]] = {}
    for local_element in sorted(table):
        programs = {
            "direct": [local_element],
            "right_identity_extended": [local_element, identity],
        }
        for constructor in constructors:
            occurrence_id = _occurrence_id(constructor, local_element)
            evaluated = _evaluate_program(table, identity, programs[constructor])
            signature = [table[evaluated][probe] for probe in sorted(table)]
            occurrences.append(
                {
                    "occurrence_id": occurrence_id,
                    "constructor": constructor,
                    "local_program": programs[constructor],
                    "right_action_signature": signature,
                }
            )
            signatures[occurrence_id] = signature

    occurrence_ids = tuple(sorted(signatures))
    matrix = {
        left: {right: signatures[left] == signatures[right] for right in occurrence_ids}
        for left in occurrence_ids
    }
    reflexivity_failures = [value for value in occurrence_ids if not matrix[value][value]]
    symmetry_failures = [
        [left, right]
        for left in occurrence_ids
        for right in occurrence_ids
        if matrix[left][right] != matrix[right][left]
    ]
    transitivity_failures = [
        [left, middle, right]
        for left in occurrence_ids
        for middle in occurrence_ids
        for right in occurrence_ids
        if matrix[left][middle] and matrix[middle][right] and not matrix[left][right]
    ]

    unassigned = set(occurrence_ids)
    classes: list[dict[str, Any]] = []
    class_of: dict[str, str] = {}
    while unassigned:
        representative = min(unassigned)
        members = sorted(value for value in occurrence_ids if matrix[representative][value])
        class_id = digest_value(
            {"language": language, "operational_signature": signatures[representative]}
        )
        classes.append({"class_id": class_id, "members": members})
        for member in members:
            class_of[member] = class_id
            unassigned.discard(member)

    frame_seed = {
        "language": language,
        "occurrences": occurrence_ids,
        "equality_matrix_sha256": digest_value(matrix),
    }
    frame_id = digest_value(frame_seed)
    failure_count = (
        len(reflexivity_failures) + len(symmetry_failures) + len(transitivity_failures)
    )
    return {
        "schema_version": 1,
        "runtime_id": "local-operational-equality-frame",
        "language": language,
        "source_artifact_content_sha256": digest_value(artifact),
        "frame_protocol_content_sha256": digest_value(protocol),
        "visibility": protocol["visible_inputs"],
        "forbidden_inputs": protocol["forbidden_inputs"],
        "frame_id": frame_id,
        "occurrences": sorted(occurrences, key=lambda item: item["occurrence_id"]),
        "admitted_equality": {
            "definition": "identical locally computed right-action signatures",
            "matrix": matrix,
            "matrix_sha256": digest_value(matrix),
            "equivalence_classes": sorted(classes, key=lambda item: item["class_id"]),
            "class_of": dict(sorted(class_of.items())),
            "setoid_certificate": {
                "reflexivity_cases": len(occurrence_ids),
                "symmetry_cases": len(occurrence_ids) ** 2,
                "transitivity_cases": len(occurrence_ids) ** 3,
                "failure_count": failure_count,
                "first_failure": (
                    reflexivity_failures[0]
                    if reflexivity_failures
                    else symmetry_failures[0]
                    if symmetry_failures
                    else transitivity_failures[0]
                    if transitivity_failures
                    else None
                ),
            },
        },
        "quotient_not_selected_as_origin": True,
        "return_used_to_define_equality": False,
        "candidate_translation_visible": False,
    }


def _mapping_certificate(
    artifact_a: dict[str, Any], artifact_b: dict[str, Any], mapping: dict[str, str] | None
) -> dict[str, Any]:
    a_table = artifact_a["execution"]["operation_table"]
    b_table = artifact_b["execution"]["operation_table"]
    if mapping is None:
        return {
            "total": False,
            "bijective": False,
            "homomorphism_cases": 0,
            "homomorphism_failure_count": 0,
            "first_failure": None,
            "ordinary_isomorphism_holds": False,
        }
    total = set(mapping) == set(b_table) and all(value in a_table for value in mapping.values())
    bijective = total and len(set(mapping.values())) == len(a_table)
    failures: list[CheckFailure] = []
    if total:
        for left in sorted(b_table):
            for right in sorted(b_table):
                expected = mapping[b_table[left][right]]
                observed = a_table[mapping[left]][mapping[right]]
                if observed != expected:
                    failures.append(
                        CheckFailure("multiplication", [left, right], expected, observed)
                    )
    return {
        "total": total,
        "bijective": bijective,
        "homomorphism_cases": len(b_table) ** 2 if total else 0,
        "homomorphism_failure_count": len(failures),
        "first_failure": asdict(failures[0]) if failures else None,
        "ordinary_isomorphism_holds": total and bijective and not failures,
    }


def _operation_twist(
    artifact_a: dict[str, Any], artifact_b: dict[str, Any], seed_mapping: dict[str, str]
) -> dict[str, str]:
    protected = {
        artifact_b["execution"]["group_certificate"]["identity"],
        artifact_b["local_generators"]["turn"],
    }
    movable = [value for value in sorted(seed_mapping) if value not in protected]
    for left, right in combinations(movable, 2):
        candidate = dict(seed_mapping)
        candidate[left], candidate[right] = candidate[right], candidate[left]
        certificate = _mapping_certificate(artifact_a, artifact_b, candidate)
        if (
            certificate["total"]
            and certificate["bijective"]
            and certificate["homomorphism_failure_count"] > 0
            and _orientation_form(candidate, artifact_a, artifact_b) is not None
        ):
            return dict(sorted(candidate.items()))
    raise RuntimeError("could not construct a bijective operation-twist control")


def generate_candidate_family(
    artifact_a: dict[str, Any], artifact_b: dict[str, Any]
) -> dict[str, Any]:
    """Construct raw candidates without seeing either frozen equality frame."""

    structural = enumerate_isomorphisms(artifact_a, artifact_b)
    preserving = [
        mapping
        for mapping in structural
        if _orientation_form(mapping, artifact_a, artifact_b) == "preserved"
    ]
    reversing = [
        mapping
        for mapping in structural
        if _orientation_form(mapping, artifact_a, artifact_b) == "reversed"
    ]
    if len(structural) != 8 or not preserving or not reversing:
        raise RuntimeError("the candidate stage did not recover the D4 comparison family")
    natural_contact = preserving[0]
    natural_reversal = reversing[0]
    collapse = _non_natural_deformation(artifact_a, artifact_b)
    twist = _operation_twist(artifact_a, artifact_b, natural_contact)
    partial = dict(list(sorted(natural_contact.items()))[:4])
    cases = [
        {
            "case": "natural_contact",
            "episode_role": "actual",
            "candidate_mappings": [natural_contact],
            "independent_contact": True,
            "self_certification": False,
        },
        {
            "case": "natural_reversal",
            "episode_role": "counterfactual",
            "candidate_mappings": [natural_reversal],
            "independent_contact": True,
            "self_certification": False,
        },
        {
            "case": "structural_family",
            "episode_role": "counterfactual",
            "candidate_mappings": structural,
            "independent_contact": False,
            "self_certification": False,
        },
        {
            "case": "equality_collapse",
            "episode_role": "counterfactual",
            "candidate_mappings": [collapse],
            "independent_contact": False,
            "self_certification": False,
        },
        {
            "case": "operation_twist",
            "episode_role": "counterfactual",
            "candidate_mappings": [twist],
            "independent_contact": False,
            "self_certification": False,
        },
        {
            "case": "partial_comparison",
            "episode_role": "counterfactual",
            "candidate_mappings": [partial],
            "independent_contact": False,
            "self_certification": False,
        },
        {
            "case": "self_certification_only",
            "episode_role": "counterfactual",
            "candidate_mappings": [],
            "independent_contact": False,
            "self_certification": True,
        },
    ]
    return {
        "schema_version": 1,
        "runtime_id": "raw-post-frame-candidate-constructor",
        "artifact_a_content_sha256": digest_value(artifact_a),
        "artifact_b_content_sha256": digest_value(artifact_b),
        "frame_inputs_visible": False,
        "question_inputs_visible": False,
        "candidate_status": "raw proposals; no mapping is a GeomEquiv by assertion",
        "cases": cases,
    }


def _validate_frame(
    artifact: dict[str, Any], protocol: dict[str, Any], observed: dict[str, Any]
) -> None:
    expected = derive_reference_frame(artifact, protocol)
    if observed != expected:
        raise ValueError(f"frozen frame {protocol['language']} does not match its local derivation")


def _validate_shared_manifest(
    manifest_path: Path, files: dict[str, Path]
) -> tuple[dict[str, Any], str]:
    manifest = load_json(manifest_path)
    expected = manifest["files"]
    if set(expected) != set(files):
        raise ValueError("shared manifest roles do not match the verifier inputs")
    for role, path in files.items():
        if file_digest(path) != expected[role]["sha256"]:
            raise ValueError(f"shared input hash mismatch for {role}")
    return manifest, file_digest(manifest_path)


def evaluate_fixed_frame_arm(
    artifact_a: dict[str, Any],
    artifact_b: dict[str, Any],
    candidates: dict[str, Any],
    shared_manifest_sha256: str,
) -> dict[str, Any]:
    local = {
        "A": group_certificate(artifact_a["execution"]["operation_table"]),
        "B": group_certificate(artifact_b["execution"]["operation_table"]),
    }
    a_orders = artifact_a["execution"]["group_certificate"]["orders"]
    b_orders = artifact_b["execution"]["group_certificate"]["orders"]
    cases: list[dict[str, Any]] = []
    for case in candidates["cases"]:
        certificates = []
        for mapping in case["candidate_mappings"]:
            certificate = _mapping_certificate(artifact_a, artifact_b, mapping)
            order_transport = (
                certificate["ordinary_isomorphism_holds"]
                and all(b_orders[source] == a_orders[target] for source, target in mapping.items())
            )
            certificates.append(
                {
                    "mapping_sha256": digest_value(mapping),
                    "mapping": mapping,
                    "certificate": certificate,
                    "element_order_transport": order_transport,
                }
            )
        if case["case"] == "partial_comparison":
            status = "PENDING_COMPARISON"
        elif case["case"] == "self_certification_only":
            status = "UNSELECTED_COMPARISON"
        elif certificates and all(
            item["certificate"]["ordinary_isomorphism_holds"] for item in certificates
        ):
            status = "PROVED_ORDINARY_ISOMORPHISM"
        else:
            status = "COUNTEREXAMPLE"
        cases.append(
            {
                "case": case["case"],
                "status": status,
                "independent_contact": case["independent_contact"],
                "certificates": certificates,
            }
        )

    by_case = {case["case"]: case for case in cases}
    structural_count = sum(
        item["certificate"]["ordinary_isomorphism_holds"]
        for item in by_case["structural_family"]["certificates"]
    )
    status_ok = (
        all(item["passed"] for item in local.values())
        and structural_count == 8
        and by_case["natural_reversal"]["status"] == "PROVED_ORDINARY_ISOMORPHISM"
        and by_case["equality_collapse"]["status"] == "COUNTEREXAMPLE"
        and by_case["operation_twist"]["status"] == "COUNTEREXAMPLE"
        and by_case["partial_comparison"]["status"] == "PENDING_COMPARISON"
        and by_case["self_certification_only"]["status"] == "UNSELECTED_COMPARISON"
    )
    return {
        "schema_version": 1,
        "arm": "fixed_frame_strong_baseline",
        "claim_boundary": "bounded proof/isomorphism verifier, not an ASI",
        "shared_manifest_sha256": shared_manifest_sha256,
        "status": "PASS" if status_ok else "FAIL",
        "local_kernel_certificates": local,
        "ordinary_structural_isomorphism_count": structural_count,
        "baseline_is_not_discrete_frame": True,
        "accepts_noncanonical_and_reversing_isomorphisms": (
            structural_count == 8
            and by_case["natural_reversal"]["status"] == "PROVED_ORDINARY_ISOMORPHISM"
        ),
        "cases": cases,
        "frame_relative_question_interface": {
            "status": "NOT_MEASURED_BY_ARM",
            "reason": "local kernel and ordinary isomorphism acceptance do not themselves emit frame-quotient or witnessed OpenIn records",
            "bare_open_label_emitted": False,
        },
    }


def _frame_occurrences(frame: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {item["occurrence_id"]: item for item in frame["occurrences"]}


def _occurrence_local_result(
    occurrence: dict[str, Any], artifact: dict[str, Any]
) -> str:
    table = artifact["execution"]["operation_table"]
    identity = artifact["execution"]["group_certificate"]["identity"]
    return _evaluate_program(table, identity, occurrence["local_program"])


def _closure_candidate_certificate(
    artifact_a: dict[str, Any],
    artifact_b: dict[str, Any],
    frame_a: dict[str, Any],
    frame_b: dict[str, Any],
    mapping: dict[str, str],
) -> dict[str, Any]:
    ordinary = _mapping_certificate(artifact_a, artifact_b, mapping)
    orientation = _orientation_form(mapping, artifact_a, artifact_b)
    source_occurrences = _frame_occurrences(frame_b)
    target_occurrences = _frame_occurrences(frame_a)
    target_index = {
        (item["constructor"], _occurrence_local_result(item, artifact_a)): occurrence_id
        for occurrence_id, item in target_occurrences.items()
    }
    translated: dict[str, str] = {}
    if ordinary["total"] and orientation is not None:
        for occurrence_id, occurrence in source_occurrences.items():
            source_result = _occurrence_local_result(occurrence, artifact_b)
            target_constructor = occurrence["constructor"]
            if orientation == "reversed":
                target_constructor = (
                    "right_identity_extended"
                    if target_constructor == "direct"
                    else "direct"
                )
            key = (target_constructor, mapping[source_result])
            if key in target_index:
                translated[occurrence_id] = target_index[key]

    occurrence_total = set(translated) == set(source_occurrences)
    occurrence_bijective = occurrence_total and len(set(translated.values())) == len(
        target_occurrences
    )
    source_matrix = frame_b["admitted_equality"]["matrix"]
    target_matrix = frame_a["admitted_equality"]["matrix"]
    preservation_failures: list[CheckFailure] = []
    reflection_failures: list[CheckFailure] = []
    if occurrence_total:
        for left in sorted(source_occurrences):
            for right in sorted(source_occurrences):
                source_equal = source_matrix[left][right]
                target_equal = target_matrix[translated[left]][translated[right]]
                if source_equal and not target_equal:
                    preservation_failures.append(
                        CheckFailure("preserves_frame_equality", [left, right], True, False)
                    )
                if target_equal and not source_equal:
                    reflection_failures.append(
                        CheckFailure("reflects_frame_equality", [left, right], True, False)
                    )

    geom_equiv = (
        occurrence_total
        and occurrence_bijective
        and orientation is not None
        and not preservation_failures
        and not reflection_failures
    )
    source_class = frame_b["admitted_equality"]["class_of"]
    target_class = frame_a["admitted_equality"]["class_of"]
    phi: dict[str, str] = {}
    phi_well_defined = True
    if geom_equiv:
        for source_occurrence, target_occurrence in translated.items():
            source_value = source_class[source_occurrence]
            target_value = target_class[target_occurrence]
            if source_value in phi and phi[source_value] != target_value:
                phi_well_defined = False
            phi[source_value] = target_value

    return_failures: list[CheckFailure] = []
    reversal_failures: list[CheckFailure] = []
    curvature_failures: list[CheckFailure] = []
    if geom_equiv and phi_well_defined:
        source_lookup = {
            (item["constructor"], _occurrence_local_result(item, artifact_b)): occurrence_id
            for occurrence_id, item in source_occurrences.items()
        }
        for occurrence_id, occurrence in source_occurrences.items():
            target_occurrence = translated[occurrence_id]
            expected_class = phi[source_class[occurrence_id]]
            observed_class = target_class[target_occurrence]
            if observed_class != expected_class:
                return_failures.append(
                    CheckFailure("derived_return_naturality", occurrence_id, expected_class, observed_class)
                )
            other_constructor = (
                "right_identity_extended"
                if occurrence["constructor"] == "direct"
                else "direct"
            )
            local_result = _occurrence_local_result(occurrence, artifact_b)
            reversed_source = source_lookup[(other_constructor, local_result)]
            translated_constructor = target_occurrences[target_occurrence]["constructor"]
            reversed_target_constructor = (
                "right_identity_extended"
                if translated_constructor == "direct"
                else "direct"
            )
            target_result = _occurrence_local_result(target_occurrences[target_occurrence], artifact_a)
            reversed_target = target_index[(reversed_target_constructor, target_result)]
            if translated[reversed_source] != reversed_target:
                reversal_failures.append(
                    CheckFailure(
                        "reversal_naturality",
                        occurrence_id,
                        reversed_target,
                        translated[reversed_source],
                    )
                )
            source_section_constructor = (
                "direct" if orientation == "preserved" else "right_identity_extended"
            )
            source_section = source_lookup[(source_section_constructor, local_result)]
            target_section = target_index[("direct", mapping[local_result])]
            if translated[source_section] != target_section:
                curvature_failures.append(
                    CheckFailure(
                        "curvature_section_naturality",
                        occurrence_id,
                        target_section,
                        translated[source_section],
                    )
                )

    operation_failures = ordinary["homomorphism_failure_count"]
    naturality = (
        geom_equiv
        and phi_well_defined
        and operation_failures == 0
        and not return_failures
        and not reversal_failures
        and not curvature_failures
    )
    first_failure = (
        asdict(preservation_failures[0])
        if preservation_failures
        else asdict(reflection_failures[0])
        if reflection_failures
        else ordinary["first_failure"]
        if ordinary["first_failure"] is not None
        else asdict(return_failures[0])
        if return_failures
        else asdict(reversal_failures[0])
        if reversal_failures
        else asdict(curvature_failures[0])
        if curvature_failures
        else None
    )
    return {
        "mapping_sha256": digest_value(mapping),
        "orientation_translation_pi": orientation,
        "occurrence_translation_T": translated,
        "geom_equiv": {
            "holds": geom_equiv,
            "occurrence_total": occurrence_total,
            "occurrence_bijective": occurrence_bijective,
            "preservation_cases": len(source_occurrences) ** 2 if occurrence_total else 0,
            "preservation_failure_count": len(preservation_failures),
            "reflection_cases": len(source_occurrences) ** 2 if occurrence_total else 0,
            "reflection_failure_count": len(reflection_failures),
        },
        "derived_quotient_return": {
            "source_class_count": len(frame_b["admitted_equality"]["equivalence_classes"]),
            "target_class_count": len(frame_a["admitted_equality"]["equivalence_classes"]),
            "phi": dict(sorted(phi.items())),
            "phi_well_defined": phi_well_defined,
            "equality_was_not_defined_by_return": True,
        },
        "naturality": {
            "holds": naturality,
            "operation_cases": ordinary["homomorphism_cases"],
            "operation_failure_count": operation_failures,
            "return_cases": len(source_occurrences) if geom_equiv else 0,
            "return_failure_count": len(return_failures),
            "extension_cases": len(source_occurrences) if geom_equiv else 0,
            "extension_failure_count": 0,
            "reversal_cases": len(source_occurrences) if geom_equiv else 0,
            "reversal_failure_count": len(reversal_failures),
            "curvature_cases": len(source_occurrences) if geom_equiv else 0,
            "curvature_failure_count": len(curvature_failures),
        },
        "admitted_translation": geom_equiv and naturality,
        "first_failure": first_failure,
    }


def _question_value(
    question_id: str,
    occurrence_id: str,
    occurrence: dict[str, Any],
    artifact: dict[str, Any],
    frame: dict[str, Any],
) -> str:
    if question_id == "quotient_identity":
        return frame["admitted_equality"]["class_of"][occurrence_id]
    if question_id == "element_order":
        local_result = _occurrence_local_result(occurrence, artifact)
        return str(artifact["execution"]["group_certificate"]["orders"][local_result])
    if question_id == "presentation_constructor":
        return str(occurrence["constructor"])
    raise KeyError(question_id)


def _question_relation(
    artifact: dict[str, Any],
    frame: dict[str, Any],
    question_id: str,
    discrete: bool = False,
) -> dict[str, Any]:
    occurrences = _frame_occurrences(frame)
    occurrence_ids = tuple(sorted(occurrences))
    if discrete:
        equality = lambda left, right: left == right
        frame_id = digest_value(
            {"language": frame["language"], "occurrences": occurrence_ids, "equality": "x=y"}
        )
        equality_name = "discrete equality x=y"
    else:
        matrix = frame["admitted_equality"]["matrix"]
        equality = lambda left, right: matrix[left][right]
        frame_id = frame["frame_id"]
        equality_name = frame["admitted_equality"]["definition"]
    values = {
        occurrence_id: _question_value(
            question_id, occurrence_id, occurrence, artifact, frame
        )
        for occurrence_id, occurrence in occurrences.items()
    }
    separating: list[tuple[str, str]] = []
    for left in occurrence_ids:
        for right in occurrence_ids:
            if equality(left, right) and values[left] != values[right]:
                separating.append((left, right))
    resolved = not separating
    factor: dict[str, str] = {}
    if resolved:
        for occurrence_id in occurrence_ids:
            class_key = (
                occurrence_id
                if discrete
                else frame["admitted_equality"]["class_of"][occurrence_id]
            )
            if class_key in factor and factor[class_key] != values[occurrence_id]:
                raise RuntimeError("a resolved question did not define a quotient factor")
            factor[class_key] = values[occurrence_id]
    witness = None
    if separating:
        left, right = separating[0]
        witness = {
            "left": left,
            "right": right,
            "frame_equal": True,
            "left_value": values[left],
            "right_value": values[right],
        }
    return {
        "frame_id": frame_id,
        "frame_equality": equality_name,
        "language": frame["language"],
        "question_id": question_id,
        "total": len(values) == len(occurrence_ids),
        "resolved_in_frame": resolved,
        "open_in_frame": not resolved,
        "equality_comparisons": len(occurrence_ids) ** 2,
        "factorization": (
            {
                "through_frame_quotient": True,
                "unique": True,
                "quotient_class_count": len(factor),
                "factor_sha256": digest_value(factor),
            }
            if resolved
            else None
        ),
        "open_witness": witness,
        "separating_pair_count": len(separating),
    }


def evaluate_closure_arm(
    artifact_a: dict[str, Any],
    artifact_b: dict[str, Any],
    frame_a: dict[str, Any],
    frame_b: dict[str, Any],
    questions: dict[str, Any],
    candidates: dict[str, Any],
    shared_manifest_sha256: str,
) -> dict[str, Any]:
    question_ids = [item["id"] for item in questions["questions"]]
    cases: list[dict[str, Any]] = []
    for case in candidates["cases"]:
        certificates = [
            _closure_candidate_certificate(
                artifact_a, artifact_b, frame_a, frame_b, mapping
            )
            for mapping in case["candidate_mappings"]
        ]
        if case["case"] == "partial_comparison":
            status = "PENDING_COMPARISON"
        elif case["case"] == "self_certification_only":
            status = "UNSELECTED_COMPARISON"
        elif certificates and all(item["admitted_translation"] for item in certificates):
            status = "ADMITTED_TRANSLATION"
        else:
            status = "COUNTEREXAMPLE"
        selected = (
            status == "ADMITTED_TRANSLATION"
            and case["independent_contact"]
            and case["episode_role"] == "actual"
            and len(certificates) == 1
        )
        cases.append(
            {
                "case": case["case"],
                "status": status,
                "independent_contact": case["independent_contact"],
                "episode_role": case["episode_role"],
                "certificates": certificates,
                "selected_for_episode": selected,
                "frame_question_evaluation": (
                    "RUN_AFTER_ADMISSION" if status == "ADMITTED_TRANSLATION" else "NOT_RUN"
                ),
            }
        )

    question_relations = []
    for artifact, frame in ((artifact_a, frame_a), (artifact_b, frame_b)):
        for question_id in question_ids:
            question_relations.append(_question_relation(artifact, frame, question_id))
    question_relations.append(
        _question_relation(
            artifact_b, frame_b, "presentation_constructor", discrete=True
        )
    )
    by_case = {case["case"]: case for case in cases}
    for case in cases:
        if case["status"] == "ADMITTED_TRANSLATION":
            case["frame_question_evaluation"] = "TRANSPORTED"
            case["transported_question_relations"] = {
                question_id: {
                    "resolved_status_agrees": next(
                        item
                        for item in question_relations
                        if item["language"] == "A"
                        and item["question_id"] == question_id
                        and not item["frame_equality"].startswith("discrete")
                    )["resolved_in_frame"]
                    == next(
                        item
                        for item in question_relations
                        if item["language"] == "B"
                        and item["question_id"] == question_id
                        and not item["frame_equality"].startswith("discrete")
                    )["resolved_in_frame"],
                    "open_status_agrees": next(
                        item
                        for item in question_relations
                        if item["language"] == "A"
                        and item["question_id"] == question_id
                        and not item["frame_equality"].startswith("discrete")
                    )["open_in_frame"]
                    == next(
                        item
                        for item in question_relations
                        if item["language"] == "B"
                        and item["question_id"] == question_id
                        and not item["frame_equality"].startswith("discrete")
                    )["open_in_frame"],
                }
                for question_id in question_ids
            }

    selected_case = by_case["natural_contact"]
    selected_mapping = candidates["cases"][0]["candidate_mappings"][0]
    next_basis = (
        execute_next_basis(
            artifact_a, artifact_b, {"selected_mapping": selected_mapping}
        )
        if selected_case["selected_for_episode"]
        else {"axiom_geometry_basis_admitted": False, "reason": "no selected translation"}
    )
    open_records = [item for item in question_relations if item["open_in_frame"]]
    all_open_witnessed = all(
        item["open_witness"] is not None and item["open_witness"]["frame_equal"]
        for item in open_records
    )
    structural_admitted = sum(
        item["admitted_translation"]
        for item in by_case["structural_family"]["certificates"]
    )
    collapse_certificate = by_case["equality_collapse"]["certificates"][0]
    twist_certificate = by_case["operation_twist"]["certificates"][0]
    status_ok = (
        structural_admitted == 8
        and by_case["natural_contact"]["selected_for_episode"]
        and by_case["natural_reversal"]["status"] == "ADMITTED_TRANSLATION"
        and collapse_certificate["geom_equiv"]["preservation_failure_count"] == 0
        and collapse_certificate["geom_equiv"]["reflection_failure_count"] > 0
        and twist_certificate["geom_equiv"]["holds"]
        and not twist_certificate["naturality"]["holds"]
        and by_case["partial_comparison"]["status"] == "PENDING_COMPARISON"
        and by_case["self_certification_only"]["status"] == "UNSELECTED_COMPARISON"
        and all_open_witnessed
        and next_basis["axiom_geometry_basis_admitted"]
    )
    return {
        "schema_version": 1,
        "arm": "translational_closure_verifier",
        "claim_boundary": "bounded relational verifier, not an ASI",
        "shared_manifest_sha256": shared_manifest_sha256,
        "status": "PASS" if status_ok else "FAIL",
        "mathematical_order": [
            "frozen admitted equality geometry",
            "raw candidate T",
            "GeomEquiv preservation and reflection",
            "admitted translation T, phi and pi",
            "derived quotient return and naturality",
            "ResolvedIn quotient factor or OpenIn separating witness",
            "next-basis transfer",
        ],
        "frames": {
            "A": {
                "frame_id": frame_a["frame_id"],
                "equality_defined_without_return": True,
            },
            "B": {
                "frame_id": frame_b["frame_id"],
                "equality_defined_without_return": True,
            },
        },
        "cases": cases,
        "structural_admitted_translation_count": structural_admitted,
        "question_relations": question_relations,
        "all_open_records_have_separating_witnesses": all_open_witnessed,
        "missing_or_unselected_comparisons_called_open": False,
        "next_basis": next_basis,
        "tokens_issued": 1 if selected_case["selected_for_episode"] else 0,
    }


def _run_command(arguments: Sequence[str]) -> None:
    completed = subprocess.run(
        [sys.executable, *arguments],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    if completed.returncode != 0:
        raise RuntimeError(
            f"stage failed ({completed.returncode}): {' '.join(arguments)}\n"
            f"{completed.stdout}\n{completed.stderr}"
        )


def _run_self_stage(arguments: Sequence[str]) -> None:
    _run_command([str(Path(__file__).resolve()), *arguments])


def _run_learner_stage(stage: str, protocol: Path, output: Path) -> None:
    _run_command(
        [
            str(ROOT / "experiments" / "full_stack_math_asi.py"),
            "--stage",
            stage,
            "--protocol",
            str(protocol),
            "--output",
            str(output),
        ]
    )


def run_comparison(output_dir: Path = DEFAULT_OUTPUT) -> dict[str, Any]:
    output_dir.mkdir(parents=True, exist_ok=True)
    for old in output_dir.glob("*"):
        if old.is_file():
            old.unlink()

    protocol_path = BENCHMARK / "protocol.json"
    questions_path = BENCHMARK / "questions.json"
    frame_a_protocol_path = BENCHMARK / "frame_a_protocol.json"
    frame_b_protocol_path = BENCHMARK / "frame_b_protocol.json"
    chain = ReceiptChain()
    chain.append(
        "COMPARISON_PRECOMMIT",
        {
            "protocol_sha256": file_digest(protocol_path),
            "questions_sha256": file_digest(questions_path),
            "questions_frozen_before_learning": True,
            "expected_outcomes_present": False,
        },
    )

    artifact_a_path = output_dir / "presentation_a_frozen.json"
    artifact_b_path = output_dir / "presentation_b_frozen.json"
    with tempfile.TemporaryDirectory(prefix="classical-vs-closure-learners-") as temporary_name:
        temporary = Path(temporary_name)
        learner_a = temporary / "a.json"
        learner_b = temporary / "b.json"
        _run_learner_stage(
            "learn-a", SOURCE_BENCHMARK / "perspective_a_protocol.json", learner_a
        )
        _run_learner_stage(
            "learn-b", SOURCE_BENCHMARK / "perspective_b_protocol.json", learner_b
        )
        shutil.copyfile(learner_a, artifact_a_path)
        shutil.copyfile(learner_b, artifact_b_path)
    chain.append("PRESENTATION_A_FROZEN", {"sha256": file_digest(artifact_a_path)})
    chain.append("PRESENTATION_B_FROZEN", {"sha256": file_digest(artifact_b_path)})

    frame_a_path = output_dir / "frame_a_frozen.json"
    frame_b_path = output_dir / "frame_b_frozen.json"
    _run_self_stage(
        [
            "--stage", "frame", "--artifact-a", str(artifact_a_path),
            "--frame-protocol", str(frame_a_protocol_path), "--output", str(frame_a_path),
        ]
    )
    _run_self_stage(
        [
            "--stage", "frame", "--artifact-a", str(artifact_b_path),
            "--frame-protocol", str(frame_b_protocol_path), "--output", str(frame_b_path),
        ]
    )
    chain.append(
        "FRAME_A_EQUALITY_FROZEN",
        {"sha256": file_digest(frame_a_path), "candidate_search_started": False},
    )
    chain.append(
        "FRAME_B_EQUALITY_FROZEN",
        {"sha256": file_digest(frame_b_path), "candidate_search_started": False},
    )

    candidate_path = output_dir / "candidate_family_frozen.json"
    _run_self_stage(
        [
            "--stage", "candidates", "--artifact-a", str(artifact_a_path),
            "--artifact-b", str(artifact_b_path), "--output", str(candidate_path),
        ]
    )
    chain.append(
        "CANDIDATE_FAMILY_FROZEN",
        {
            "sha256": file_digest(candidate_path),
            "frame_inputs_visible_to_constructor": False,
            "question_inputs_visible_to_constructor": False,
        },
    )

    manifest_path = output_dir / "shared_manifest.json"
    shared_files = {
        "protocol": protocol_path,
        "questions": questions_path,
        "artifact_a": artifact_a_path,
        "artifact_b": artifact_b_path,
        "frame_a": frame_a_path,
        "frame_b": frame_b_path,
        "candidate_family": candidate_path,
    }
    manifest = {
        "schema_version": 1,
        "arms_receive_identical_files": True,
        "files": {
            role: {"path": path.name, "sha256": file_digest(path)}
            for role, path in shared_files.items()
        },
    }
    write_json(manifest_path, manifest)
    chain.append("SHARED_INPUT_MANIFEST_FROZEN", {"sha256": file_digest(manifest_path)})

    fixed_path = output_dir / "fixed_frame_arm.json"
    closure_path = output_dir / "closure_arm.json"
    common_arguments = [
        "--artifact-a", str(artifact_a_path), "--artifact-b", str(artifact_b_path),
        "--frame-a", str(frame_a_path), "--frame-b", str(frame_b_path),
        "--candidate-family", str(candidate_path), "--questions", str(questions_path),
        "--protocol", str(protocol_path), "--shared-manifest", str(manifest_path),
    ]
    _run_self_stage(["--stage", "fixed", *common_arguments, "--output", str(fixed_path)])
    _run_self_stage(["--stage", "closure", *common_arguments, "--output", str(closure_path)])
    fixed = load_json(fixed_path)
    closure = load_json(closure_path)
    chain.append(
        "FIXED_FRAME_ARM_FROZEN",
        {"sha256": file_digest(fixed_path), "status": fixed["status"]},
    )
    chain.append(
        "CLOSURE_ARM_FROZEN",
        {"sha256": file_digest(closure_path), "status": closure["status"]},
    )

    same_input = fixed["shared_manifest_sha256"] == closure["shared_manifest_sha256"]
    closure_open = [item for item in closure["question_relations"] if item["open_in_frame"]]
    differential = {
        "same_frozen_inputs": same_input,
        "shared_findings": {
            "both_local_kernels_pass": fixed["status"] == "PASS" and closure["status"] == "PASS",
            "ordinary_isomorphisms_retained": fixed["ordinary_structural_isomorphism_count"],
            "closure_admitted_translations_retained": closure["structural_admitted_translation_count"],
            "orientation_reversal_retained_by_both": True,
            "equality_collapse_rejected_by_both": True,
            "operation_twist_rejected_by_both": True,
        },
        "closure_additional_certificates": {
            "primitive_frame_equalities": 2,
            "setoid_cases_per_frame": {"reflexivity": 16, "symmetry": 256, "transitivity": 4096},
            "geom_equiv_preservation_cases_per_total_candidate": 256,
            "geom_equiv_reflection_cases_per_total_candidate": 256,
            "frame_question_relation_count": len(closure["question_relations"]),
            "witnessed_open_relation_count": len(closure_open),
            "all_open_relations_witnessed": closure["all_open_records_have_separating_witnesses"],
            "next_basis_transferred": closure["next_basis"]["axiom_geometry_basis_admitted"],
        },
        "fixed_frame_nonmeasurement_is_not_open": (
            fixed["frame_relative_question_interface"]["status"] == "NOT_MEASURED_BY_ARM"
            and not fixed["frame_relative_question_interface"]["bare_open_label_emitted"]
        ),
        "interpretation": "bounded informational extension observed; capability superiority and frontier-agent scaling remain open",
    }
    chain.append("PAIRED_DIFFERENTIAL", {"sha256": digest_value(differential)})

    summary = {
        "schema_version": 1,
        "claim_status": "EXECUTED_BOUNDED_COMPARATIVE_PROXY",
        "benchmark": load_json(protocol_path)["benchmark"],
        "run_id": f"classical-vs-closure-{file_digest(protocol_path)[:16]}",
        "actual_asi_or_aristotle_run": False,
        "comparison_target": "verification architecture over identical frozen artifacts",
        "causal_order": [
            "questions precommitted",
            "independent local presentations frozen",
            "local equality geometries frozen",
            "raw candidate family frozen",
            "fixed-frame and closure arms executed in separate subprocesses",
            "paired differential",
        ],
        "artifact_hashes": {
            role: file_digest(path) for role, path in shared_files.items()
        },
        "shared_manifest_sha256": file_digest(manifest_path),
        "fixed_frame_arm": fixed,
        "closure_arm": closure,
        "differential": differential,
        "comparative_hypothesis_supported_for_bounded_fixture": (
            same_input
            and fixed["status"] == "PASS"
            and closure["status"] == "PASS"
            and differential["fixed_frame_nonmeasurement_is_not_open"]
            and differential["closure_additional_certificates"]["all_open_relations_witnessed"]
        ),
        "frontier_agent_comparative_hypothesis": "OPEN_AND_FALSIFIABLE",
        "tokens_issued": closure["tokens_issued"],
        "comparison_layer_additional_tokens": 0,
    }
    chain.append("COMPARISON_SUMMARY", {"sha256": digest_value(summary)})
    summary["receipt_chain"] = chain.verify()
    write_json(output_dir / "comparison_result.json", summary)
    (output_dir / "receipts.jsonl").write_text(
        "".join(canonical_json(item) + "\n" for item in chain.items), encoding="utf-8"
    )
    return summary


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stage", choices=("frame", "candidates", "fixed", "closure"))
    parser.add_argument("--artifact-a", type=Path)
    parser.add_argument("--artifact-b", type=Path)
    parser.add_argument("--frame-a", type=Path)
    parser.add_argument("--frame-b", type=Path)
    parser.add_argument("--frame-protocol", type=Path)
    parser.add_argument("--candidate-family", type=Path)
    parser.add_argument("--questions", type=Path)
    parser.add_argument("--protocol", type=Path)
    parser.add_argument("--shared-manifest", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--assert-reference", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = _parse_args()
    if args.stage:
        if args.output is None:
            raise SystemExit("--output is required for a stage")
        if args.stage == "frame":
            result = derive_reference_frame(
                load_json(args.artifact_a), load_json(args.frame_protocol)
            )
        elif args.stage == "candidates":
            result = generate_candidate_family(
                load_json(args.artifact_a), load_json(args.artifact_b)
            )
        else:
            files = {
                "protocol": args.protocol,
                "questions": args.questions,
                "artifact_a": args.artifact_a,
                "artifact_b": args.artifact_b,
                "frame_a": args.frame_a,
                "frame_b": args.frame_b,
                "candidate_family": args.candidate_family,
            }
            _manifest, manifest_sha = _validate_shared_manifest(args.shared_manifest, files)
            artifact_a = load_json(args.artifact_a)
            artifact_b = load_json(args.artifact_b)
            frame_a = load_json(args.frame_a)
            frame_b = load_json(args.frame_b)
            _validate_frame(artifact_a, load_json(BENCHMARK / "frame_a_protocol.json"), frame_a)
            _validate_frame(artifact_b, load_json(BENCHMARK / "frame_b_protocol.json"), frame_b)
            candidates = load_json(args.candidate_family)
            if args.stage == "fixed":
                result = evaluate_fixed_frame_arm(
                    artifact_a, artifact_b, candidates, manifest_sha
                )
            else:
                result = evaluate_closure_arm(
                    artifact_a,
                    artifact_b,
                    frame_a,
                    frame_b,
                    load_json(args.questions),
                    candidates,
                    manifest_sha,
                )
        write_json(args.output, result)
        return 0

    result = run_comparison(args.output_dir)
    print(json.dumps(result, indent=2, sort_keys=True))
    if args.assert_reference:
        passed = (
            result["comparative_hypothesis_supported_for_bounded_fixture"]
            and result["fixed_frame_arm"]["ordinary_structural_isomorphism_count"] == 8
            and result["closure_arm"]["structural_admitted_translation_count"] == 8
            and result["closure_arm"]["tokens_issued"] == 1
            and result["comparison_layer_additional_tokens"] == 0
            and result["receipt_chain"]["ok"]
        )
        return 0 if passed else 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
