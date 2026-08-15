#!/usr/bin/env python3
"""Three-part classical/closure/external-assumption interaction simulation.

This executable is a bounded, deterministic symbolic proxy, not an ASI or an
Aristotle result.  It first runs the existing strong classical and
closure-native comparison over independently frozen D4 presentations.  Only
after those two parts are frozen does it reveal a separately content-addressed
packet of external equality assumptions, instantiate every assumption in its
own declared geometry, and test the proposed interactions.

Exact interactions are admitted only as ``GeomEquiv`` after both preservation
and reflection.  A strictly larger designed ``D4 x C2`` isolation is handled
by explicitly typed split-extension and closure-quotient relations instead of
being mislabeled as a bijective translation.  "Continuous" means that every
finite isolation and adjacent relation has a gap-free, compositional receipt
and occurrence lineage; no topological continuity is asserted.
"""

from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
import json
from pathlib import Path
import shutil
import sys
import tempfile
from typing import Any, Callable, Sequence

PROJECT_ROOT = Path(__file__).resolve().parents[1]
if str(PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJECT_ROOT))

from experiments.classical_vs_closure_asi import (
    CONSTRUCTORS,
    _frame_occurrences,
    _occurrence_local_result,
    _operation_twist,
    _question_value,
    run_comparison,
)
from experiments.full_stack_math_asi import (
    ROOT,
    ReceiptChain,
    canonical_json,
    digest_value,
    file_digest,
    group_certificate,
    load_json,
    write_json,
)


BENCHMARK = ROOT / "benchmarks" / "three_part_assumption_interaction"
QUESTIONS = ROOT / "benchmarks" / "classical_vs_closure" / "questions.json"
PAIRED_BENCHMARK = ROOT / "benchmarks" / "classical_vs_closure"
DEFAULT_OUTPUT = ROOT / "runs" / "three_part_assumption_interaction" / "latest"
SUPPORTED_EQUALITY_RULES = {
    "local_right_action_signature_equivalence",
    "local_signature_and_constructor_equivalence",
    "rotation_reflection_parity_equivalence",
}
SUPPORTED_CANDIDATES = {
    "constructor_swap",
    "identity",
    "operation_twist",
    "partial_identity",
}
REQUIRED_EXACT_CASES = {
    "external_coordinate_reexpression",
    "literal_isolation_split",
    "normal_subgroup_parity_collapse",
    "external_basis_twist",
    "partial_external_interaction",
}


@dataclass(frozen=True)
class Failure:
    check: str
    input: object
    expected: object
    observed: object


def validate_external_packet(packet: dict[str, Any]) -> None:
    """Reject undeclared evaluator semantics instead of normalizing them."""

    if packet.get("schema_version") != 1:
        raise ValueError("unsupported external assumption packet schema")
    cases = packet.get("exact_geometries")
    if not isinstance(cases, list):
        raise ValueError("external packet has no exact interaction list")
    identifiers = {case.get("assumption_id") for case in cases}
    if identifiers != REQUIRED_EXACT_CASES:
        raise ValueError("external packet changed its precommitted interaction cases")
    for case in cases:
        if case.get("equality_rule") not in SUPPORTED_EQUALITY_RULES:
            raise ValueError(
                f"unsupported external equality rule {case.get('equality_rule')!r}; "
                "it was not normalized or replaced"
            )
        obligations = case.get("declared_obligations")
        if not isinstance(obligations, list) or not obligations:
            raise ValueError(f"external case {case.get('assumption_id')} has no obligations")
    extension = packet.get("non_bijective_interaction")
    if not isinstance(extension, dict):
        raise ValueError("external packet has no non-bijective interaction")
    if extension.get("external_operation") != "direct_product_with_central_C2":
        raise ValueError("unsupported external operation; it was not replaced by D4")
    if extension.get("equality_rule") != "external_right_action_signature_equivalence":
        raise ValueError("unsupported central-isolation equality")
    if extension.get("interaction_sequence") != [
        "SPLIT_EXTENSION",
        "CLOSURE_QUOTIENT",
    ]:
        raise ValueError("external interaction sequence changed")


def validate_external_candidate_packet(
    packet: dict[str, Any], geometry_ids: set[str]
) -> None:
    if packet.get("schema_version") != 1:
        raise ValueError("unsupported external candidate packet schema")
    proposals = packet.get("candidate_proposals")
    if not isinstance(proposals, list):
        raise ValueError("external packet has no separately declared candidate proposals")
    proposal_ids = {proposal.get("assumption_id") for proposal in proposals}
    if proposal_ids != geometry_ids or len(proposals) != len(geometry_ids):
        raise ValueError("external candidate proposals do not match the frozen geometries")
    for proposal in proposals:
        if proposal.get("candidate_kind") not in SUPPORTED_CANDIDATES:
            raise ValueError(
                f"unsupported external candidate {proposal.get('candidate_kind')!r}"
            )
    if packet.get("interaction_sequence") != [
        "SPLIT_EXTENSION",
        "CLOSURE_QUOTIENT",
    ]:
        raise ValueError("external candidate interaction sequence changed")
    central = packet.get("central_interaction_proposals")
    if not isinstance(central, list) or {
        item.get("relation_kind") for item in central
    } != {"SPLIT_EXTENSION", "CLOSURE_QUOTIENT"}:
        raise ValueError("external central candidate proposals changed")


def reveal_external_packet(path: Path, expected_sha256: str) -> dict[str, Any]:
    """Open a packet only when its bytes still match the pre-Part-1 commitment."""

    if file_digest(path) != expected_sha256:
        raise ValueError("external packet commitment mismatch at reveal")
    packet = load_json(path)
    validate_external_packet(packet)
    return packet


def reveal_external_candidate_packet(
    path: Path, expected_sha256: str, geometry_ids: set[str]
) -> dict[str, Any]:
    if file_digest(path) != expected_sha256:
        raise ValueError("external candidate packet commitment mismatch at reveal")
    packet = load_json(path)
    validate_external_candidate_packet(packet, geometry_ids)
    return packet


def _opposite_constructor(constructor: str) -> str:
    if constructor == "direct":
        return "right_identity_extended"
    if constructor == "right_identity_extended":
        return "direct"
    raise ValueError(f"unknown constructor {constructor!r}")


def _rotation_subgroup(artifact: dict[str, Any]) -> set[str]:
    table = artifact["execution"]["operation_table"]
    identity = artifact["execution"]["group_certificate"]["identity"]
    turn = artifact["local_generators"]["turn"]
    rotations: set[str] = set()
    current = identity
    while current not in rotations:
        rotations.add(current)
        current = table[current][turn]
    return rotations


def _equivalence_classes(
    language: str, matrix: dict[str, dict[str, bool]], keys: dict[str, object]
) -> tuple[list[dict[str, Any]], dict[str, str]]:
    remaining = set(matrix)
    classes: list[dict[str, Any]] = []
    class_of: dict[str, str] = {}
    while remaining:
        representative = min(remaining)
        members = sorted(item for item in matrix if matrix[representative][item])
        class_id = digest_value(
            {"language": language, "admitted_equality_key": keys[representative]}
        )
        classes.append({"class_id": class_id, "members": members})
        for member in members:
            class_of[member] = class_id
            remaining.discard(member)
    return sorted(classes, key=lambda item: item["class_id"]), dict(sorted(class_of.items()))


def _audit_geometry(
    identities: Sequence[str],
    table: dict[str, dict[str, str]],
    occurrences: list[dict[str, Any]],
    matrix: dict[str, dict[str, bool]],
    declared_obligations: Sequence[str],
) -> dict[str, Any]:
    occurrence_by_id = {item["occurrence_id"]: item for item in occurrences}
    occurrence_ids = tuple(sorted(occurrence_by_id))
    lookup = {
        (item["constructor"], item["evaluated_local_result"]): item["occurrence_id"]
        for item in occurrences
    }
    reflexivity = [item for item in occurrence_ids if not matrix[item][item]]
    symmetry = [
        [left, right]
        for left in occurrence_ids
        for right in occurrence_ids
        if matrix[left][right] != matrix[right][left]
    ]
    transitivity = [
        [left, middle, right]
        for left in occurrence_ids
        for middle in occurrence_ids
        for right in occurrence_ids
        if matrix[left][middle]
        and matrix[middle][right]
        and not matrix[left][right]
    ]
    setoid_failures: list[object] = [*reflexivity, *symmetry, *transitivity]

    returning: list[object] = []
    reversal: list[object] = []
    for occurrence_id in occurrence_ids:
        item = occurrence_by_id[occurrence_id]
        result = item["evaluated_local_result"]
        direct = lookup[("direct", result)]
        reverse = lookup[(_opposite_constructor(item["constructor"]), result)]
        if not matrix[occurrence_id][direct]:
            returning.append([occurrence_id, direct])
        if not matrix[occurrence_id][reverse]:
            reversal.append([occurrence_id, reverse])

    grounding = []
    for left in identities:
        for right in identities:
            if left != right and matrix[lookup[("direct", left)]][lookup[("direct", right)]]:
                grounding.append([left, right])

    equal_pairs = [
        (left, right)
        for left in occurrence_ids
        for right in occurrence_ids
        if matrix[left][right]
    ]
    operation = []
    for left, left_prime in equal_pairs:
        for right, right_prime in equal_pairs:
            product = table[occurrence_by_id[left]["evaluated_local_result"]][
                occurrence_by_id[right]["evaluated_local_result"]
            ]
            product_prime = table[occurrence_by_id[left_prime]["evaluated_local_result"]][
                occurrence_by_id[right_prime]["evaluated_local_result"]
            ]
            if not matrix[lookup[("direct", product)]][lookup[("direct", product_prime)]]:
                operation.append([[left, left_prime], [right, right_prime]])

    checks = {
        "setoid": {
            "cases": {
                "reflexivity": len(occurrence_ids),
                "symmetry": len(occurrence_ids) ** 2,
                "transitivity": len(occurrence_ids) ** 3,
            },
            "failure_count": len(setoid_failures),
            "first_failure": setoid_failures[0] if setoid_failures else None,
            "passed": not setoid_failures,
        },
        "returning": {
            "cases": len(occurrence_ids),
            "failure_count": len(returning),
            "first_failure": returning[0] if returning else None,
            "passed": not returning,
        },
        "grounded": {
            "cases": len(identities) ** 2,
            "failure_count": len(grounding),
            "first_failure": grounding[0] if grounding else None,
            "passed": not grounding,
        },
        "operation_congruence": {
            "cases": len(equal_pairs) ** 2,
            "failure_count": len(operation),
            "first_failure": operation[0] if operation else None,
            "passed": not operation,
        },
        "presentation_reversal": {
            "cases": len(occurrence_ids),
            "failure_count": len(reversal),
            "first_failure": reversal[0] if reversal else None,
            "passed": not reversal,
        },
    }
    declared = tuple(declared_obligations)
    unknown = sorted(set(declared) - set(checks))
    if unknown:
        raise ValueError(f"unknown local geometry obligations {unknown}")
    return {
        "evaluated_only_in_declared_external_geometry": True,
        "source_equality_substituted": False,
        "declared_obligations": list(declared),
        "checks": checks,
        "undeclared_check_failures_retained": {
            name: check["failure_count"]
            for name, check in checks.items()
            if name not in declared and check["failure_count"]
        },
        "declared_obligations_passed": all(checks[name]["passed"] for name in declared),
        "full_returning_grounded_closure_obligations_passed": all(
            check["passed"] for check in checks.values()
        ),
    }


def instantiate_external_geometry(
    artifact: dict[str, Any], assumption: dict[str, Any]
) -> dict[str, Any]:
    """Instantiate a predeclared external equality without consulting a candidate map."""

    rule = assumption["equality_rule"]
    if rule not in SUPPORTED_EQUALITY_RULES:
        raise ValueError(f"unsupported external equality rule {rule!r}; it was not normalized")
    table = artifact["execution"]["operation_table"]
    identities = tuple(sorted(table))
    language = str(assumption["language"])
    rotations = _rotation_subgroup(artifact)
    occurrences: list[dict[str, Any]] = []
    keys: dict[str, object] = {}
    for identity in identities:
        signature = [table[identity][probe] for probe in identities]
        for constructor in CONSTRUCTORS:
            occurrence_id = f"{language}/{constructor}:{identity}"
            item = {
                "occurrence_id": occurrence_id,
                "constructor": constructor,
                "evaluated_local_result": identity,
                "right_action_signature": signature,
            }
            occurrences.append(item)
            if rule == "local_right_action_signature_equivalence":
                keys[occurrence_id] = signature
            elif rule == "local_signature_and_constructor_equivalence":
                keys[occurrence_id] = [signature, constructor]
            else:
                keys[occurrence_id] = "rotation" if identity in rotations else "reflection"
    occurrences.sort(key=lambda item: item["occurrence_id"])
    matrix = {
        left: {right: keys[left] == keys[right] for right in sorted(keys)}
        for left in sorted(keys)
    }
    classes, class_of = _equivalence_classes(language, matrix, keys)
    assumption_seed = {
        "assumption": assumption,
        "artifact_content_sha256": digest_value(artifact),
    }
    assumption_hash = digest_value(assumption_seed)
    frame_id = digest_value(
        {
            "assumption_id": assumption_hash,
            "occurrences": sorted(keys),
            "equality_matrix_sha256": digest_value(matrix),
        }
    )
    audit = _audit_geometry(
        identities,
        table,
        occurrences,
        matrix,
        assumption["declared_obligations"],
    )
    return {
        "schema_version": 1,
        "runtime_id": "externally-assumed-axiom-geometry",
        "language": language,
        "assumption_name": assumption["assumption_id"],
        "axiom_geometry_assumption": assumption,
        "axiom_geometry_assumption_id": assumption_hash,
        "assumption_status": "ASSUMED_FOR_OWN_UNIFIED_EVALUATION",
        "frame_id": frame_id,
        "occurrences": occurrences,
        "identity_basis": list(identities),
        "operation_table": table,
        "admitted_equality": {
            "relation_kind": rule,
            "definition": "the precommitted external rule evaluated on the external carrier",
            "matrix": matrix,
            "matrix_sha256": digest_value(matrix),
            "equivalence_classes": classes,
            "class_of": class_of,
        },
        "internal_unified_evaluation": audit,
        "candidate_interaction_visible_during_instantiation": False,
    }


def _central_identity(base: str, bit: int) -> str:
    return f"{base}|z{bit}"


def _split_central_identity(value: str) -> tuple[str, int]:
    base, suffix = value.rsplit("|z", 1)
    return base, int(suffix)


def instantiate_central_isolation(
    artifact: dict[str, Any], assumption: dict[str, Any]
) -> dict[str, Any]:
    base_table = artifact["execution"]["operation_table"]
    bases = tuple(sorted(base_table))
    identities = tuple(_central_identity(base, bit) for base in bases for bit in (0, 1))
    table: dict[str, dict[str, str]] = {}
    for left in identities:
        left_base, left_bit = _split_central_identity(left)
        table[left] = {}
        for right in identities:
            right_base, right_bit = _split_central_identity(right)
            table[left][right] = _central_identity(
                base_table[left_base][right_base], left_bit ^ right_bit
            )
    certificate = group_certificate(table)
    if not certificate["passed"]:
        raise ValueError("the external central isolation failed its own group laws")
    language = str(assumption["language"])
    occurrences: list[dict[str, Any]] = []
    keys: dict[str, object] = {}
    for identity in identities:
        signature = [table[identity][probe] for probe in identities]
        for constructor in CONSTRUCTORS:
            occurrence_id = f"{language}/{constructor}:{identity}"
            occurrences.append(
                {
                    "occurrence_id": occurrence_id,
                    "constructor": constructor,
                    "evaluated_local_result": identity,
                    "right_action_signature": signature,
                }
            )
            keys[occurrence_id] = signature
    occurrences.sort(key=lambda item: item["occurrence_id"])
    matrix = {
        left: {right: keys[left] == keys[right] for right in sorted(keys)}
        for left in sorted(keys)
    }
    classes, class_of = _equivalence_classes(language, matrix, keys)
    assumption_hash = digest_value(
        {"assumption": assumption, "base_artifact_content_sha256": digest_value(artifact)}
    )
    audit = _audit_geometry(
        identities,
        table,
        occurrences,
        matrix,
        assumption["declared_obligations"],
    )
    return {
        "schema_version": 1,
        "runtime_id": "external-central-C2-axiom-geometry",
        "language": language,
        "assumption_name": assumption["assumption_id"],
        "axiom_geometry_assumption": assumption,
        "axiom_geometry_assumption_id": assumption_hash,
        "assumption_status": "ASSUMED_FOR_OWN_UNIFIED_EVALUATION",
        "frame_id": digest_value(
            {
                "assumption_id": assumption_hash,
                "equality_matrix_sha256": digest_value(matrix),
            }
        ),
        "identity_basis": list(identities),
        "operation_table": table,
        "group_certificate": certificate,
        "occurrences": occurrences,
        "admitted_equality": {
            "relation_kind": assumption["equality_rule"],
            "definition": "equality of external D4 x C2 right-action signatures",
            "matrix": matrix,
            "matrix_sha256": digest_value(matrix),
            "equivalence_classes": classes,
            "class_of": class_of,
        },
        "internal_unified_evaluation": audit,
        "candidate_interaction_visible_during_instantiation": False,
        "base_geometry_was_not_substituted_for_external_geometry": True,
    }


def _lookup(frame: dict[str, Any]) -> dict[tuple[str, str], str]:
    return {
        (item["constructor"], item["evaluated_local_result"]): item["occurrence_id"]
        for item in frame["occurrences"]
    }


def _external_candidate(
    artifact: dict[str, Any], source_frame: dict[str, Any], target_frame: dict[str, Any], kind: str
) -> tuple[dict[str, str], dict[str, str], str | None]:
    source = _frame_occurrences(source_frame)
    target_lookup = _lookup(target_frame)
    elements = tuple(sorted(artifact["execution"]["operation_table"]))
    if kind == "operation_twist":
        basis = _operation_twist(artifact, artifact, {element: element for element in elements})
    else:
        basis = {element: element for element in elements}
    occurrence_map: dict[str, str] = {}
    for occurrence_id in sorted(source):
        item = source[occurrence_id]
        constructor = item["constructor"]
        if kind == "constructor_swap":
            constructor = _opposite_constructor(constructor)
        result = item["evaluated_local_result"]
        occurrence_map[occurrence_id] = target_lookup[(constructor, basis[result])]
    if kind == "partial_identity":
        occurrence_map = dict(list(sorted(occurrence_map.items()))[: len(occurrence_map) // 2])
        basis = dict(list(sorted(basis.items()))[: len(basis) // 2])
        orientation = None
    else:
        orientation = "reversed" if kind == "constructor_swap" else "preserved"
    return dict(sorted(occurrence_map.items())), dict(sorted(basis.items())), orientation


def _external_exact_certificate(
    artifact: dict[str, Any],
    source_frame: dict[str, Any],
    target_frame: dict[str, Any],
    assumption: dict[str, Any],
    candidate_proposal: dict[str, Any],
    frozen_candidate: dict[str, Any] | None = None,
) -> dict[str, Any]:
    if frozen_candidate is None:
        occurrence_map, basis_map, orientation = _external_candidate(
            artifact,
            source_frame,
            target_frame,
            candidate_proposal["candidate_kind"],
        )
    else:
        occurrence_map = dict(frozen_candidate["occurrence_map"])
        basis_map = dict(frozen_candidate["basis_map"])
        orientation = frozen_candidate["orientation_proposal"]
    source_occurrences = _frame_occurrences(source_frame)
    target_occurrences = _frame_occurrences(target_frame)
    source_matrix = source_frame["admitted_equality"]["matrix"]
    target_matrix = target_frame["admitted_equality"]["matrix"]
    total = set(occurrence_map) == set(source_occurrences)
    bijective = total and set(occurrence_map.values()) == set(target_occurrences)
    preservation: list[Failure] = []
    reflection: list[Failure] = []
    if total:
        for left in sorted(source_occurrences):
            for right in sorted(source_occurrences):
                source_equal = source_matrix[left][right]
                target_equal = target_matrix[occurrence_map[left]][occurrence_map[right]]
                if source_equal and not target_equal:
                    preservation.append(
                        Failure("preserves_external_equality", [left, right], True, False)
                    )
                if target_equal and not source_equal:
                    reflection.append(
                        Failure("reflects_external_equality", [left, right], True, False)
                    )
    geom_equiv = total and bijective and not preservation and not reflection

    source_class = source_frame["admitted_equality"]["class_of"]
    target_class = target_frame["admitted_equality"]["class_of"]
    phi: dict[str, str] = {}
    phi_well_defined = True
    if geom_equiv:
        for source_id, target_id in occurrence_map.items():
            left = source_class[source_id]
            right = target_class[target_id]
            if left in phi and phi[left] != right:
                phi_well_defined = False
            phi[left] = right

    table = artifact["execution"]["operation_table"]
    operation_failures: list[Failure] = []
    basis_total = set(basis_map) == set(table)
    if basis_total:
        for left in sorted(table):
            for right in sorted(table):
                expected = basis_map[table[left][right]]
                observed = table[basis_map[left]][basis_map[right]]
                if observed != expected:
                    operation_failures.append(
                        Failure("external_operation_naturality", [left, right], expected, observed)
                    )

    reversal_failures: list[Failure] = []
    section_failures: list[Failure] = []
    return_failures: list[Failure] = []
    tuple_coherence_failures: list[Failure] = []
    orientation_valid = orientation in {"preserved", "reversed"}
    source_lookup = {
        (item["constructor"], item["evaluated_local_result"]): occurrence_id
        for occurrence_id, item in source_occurrences.items()
    }
    target_lookup = _lookup(target_frame)
    if geom_equiv and phi_well_defined and orientation_valid and basis_total:
        for source_id, item in source_occurrences.items():
            target_id = occurrence_map[source_id]
            if phi[source_class[source_id]] != target_class[target_id]:
                return_failures.append(
                    Failure("W_quotient_return", source_id, phi[source_class[source_id]], target_class[target_id])
                )
            result = item["evaluated_local_result"]
            reversed_source = source_lookup[(_opposite_constructor(item["constructor"]), result)]
            target_item = target_occurrences[target_id]
            reversed_target = target_lookup[
                (_opposite_constructor(target_item["constructor"]), target_item["evaluated_local_result"])
            ]
            if occurrence_map[reversed_source] != reversed_target:
                reversal_failures.append(
                    Failure("J_reversal_naturality", source_id, reversed_target, occurrence_map[reversed_source])
                )
            expected_constructor = (
                item["constructor"]
                if orientation == "preserved"
                else _opposite_constructor(item["constructor"])
            )
            expected_target = target_lookup[
                (expected_constructor, basis_map[item["evaluated_local_result"]])
            ]
            if target_id != expected_target:
                tuple_coherence_failures.append(
                    Failure(
                        "T_phi_pi_coherence",
                        source_id,
                        expected_target,
                        target_id,
                    )
                )
        for element in sorted(table):
            expected_constructor = (
                "direct" if orientation == "preserved" else "right_identity_extended"
            )
            expected = target_lookup[(expected_constructor, basis_map[element])]
            observed = occurrence_map[source_lookup[("direct", element)]]
            if observed != expected:
                section_failures.append(
                    Failure("E_C_section_naturality", element, expected, observed)
                )

    naturality = (
        geom_equiv
        and phi_well_defined
        and basis_total
        and orientation_valid
        and not operation_failures
        and not reversal_failures
        and not section_failures
        and not return_failures
        and not tuple_coherence_failures
    )
    if candidate_proposal["candidate_kind"] == "partial_identity":
        status = "PENDING_COMPARISON"
    elif not target_frame["internal_unified_evaluation"]["declared_obligations_passed"]:
        status = "INTERNAL_INCOHERENCE"
    elif not geom_equiv:
        status = "EQUALITY_OBSTRUCTION"
    elif not naturality:
        status = "NATURALITY_OBSTRUCTION"
    else:
        status = "TRACE_PRESERVED"
    first = (
        asdict(preservation[0])
        if preservation
        else asdict(reflection[0])
        if reflection
        else asdict(operation_failures[0])
        if operation_failures
        else asdict(reversal_failures[0])
        if reversal_failures
        else asdict(section_failures[0])
        if section_failures
        else asdict(tuple_coherence_failures[0])
        if tuple_coherence_failures
        else asdict(
            Failure(
                "orientation_translation_pi",
                assumption["assumption_id"],
                "preserved or reversed",
                orientation,
            )
        )
        if geom_equiv and not orientation_valid
        else None
    )
    form_seed = {
        "source_assumption_id": source_frame["axiom_geometry_assumption_id"],
        "target_assumption_id": target_frame["axiom_geometry_assumption_id"],
        "T": occurrence_map,
        "phi": phi if geom_equiv else None,
        "pi": orientation,
    }
    form_id = digest_value(form_seed)
    return {
        "case": assumption["assumption_id"],
        "status": status,
        "source_isolation_id": source_frame["frame_id"],
        "target_isolation_id": target_frame["frame_id"],
        "candidate_constructed_after_target_freeze": True,
        "geom_equiv": {
            "holds": geom_equiv,
            "total": total,
            "bijective": bijective,
            "preservation_cases": len(source_occurrences) ** 2 if total else 0,
            "preservation_failure_count": len(preservation),
            "reflection_cases": len(source_occurrences) ** 2 if total else 0,
            "reflection_failure_count": len(reflection),
        },
        "naturality": {
            "holds": naturality,
            "W_cases": len(source_occurrences) if geom_equiv else 0,
            "W_failure_count": len(return_failures),
            "E_cases": len(table) if geom_equiv else 0,
            "E_failure_count": len(section_failures),
            "J_cases": len(source_occurrences) if geom_equiv else 0,
            "J_failure_count": len(reversal_failures),
            "C_cases": len(table) if geom_equiv else 0,
            "C_failure_count": len(section_failures),
            "operation_cases": len(table) ** 2 if basis_total else 0,
            "operation_failure_count": len(operation_failures),
            "translation_tuple_cases": len(source_occurrences) if geom_equiv else 0,
            "translation_tuple_failure_count": len(tuple_coherence_failures)
            + (1 if geom_equiv and not orientation_valid else 0),
        },
        "explicit_translational_form": {
            "translational_form_id": form_id,
            "source_axiom_geometry_assumption_id": source_frame[
                "axiom_geometry_assumption_id"
            ],
            "target_axiom_geometry_assumption_id": target_frame[
                "axiom_geometry_assumption_id"
            ],
            "candidate_T": {
                "occurrence_map": occurrence_map,
                "basis_map": basis_map,
                "total": total,
                "bijective": bijective,
            },
            "geom_equiv_admission": "ADMITTED" if geom_equiv else "REJECTED",
            "translation_tuple_T_phi_pi": (
                {"T": occurrence_map, "phi": dict(sorted(phi.items())), "pi": orientation}
                if geom_equiv and phi_well_defined and orientation_valid
                else None
            ),
            "closure_derivations": {
                "W": "VERIFIED" if geom_equiv and not return_failures else "BLOCKED",
                "E": (
                    "VERIFIED"
                    if geom_equiv and orientation_valid and not section_failures
                    else "BLOCKED"
                ),
                "J": (
                    "VERIFIED"
                    if geom_equiv and orientation_valid and not reversal_failures
                    else "BLOCKED"
                ),
                "C": (
                    "VERIFIED"
                    if geom_equiv and orientation_valid and not section_failures
                    else "BLOCKED"
                ),
                "operation": (
                    "VERIFIED"
                    if geom_equiv and not operation_failures
                    else "COUNTEREXAMPLE"
                    if geom_equiv
                    else "BLOCKED"
                ),
                "quotient_questions": "ELIGIBLE" if naturality else "BLOCKED",
                "next_basis": "ELIGIBLE" if naturality else "BLOCKED",
            },
            "closure_chain_complete": naturality,
        },
        "first_obstruction": first,
        "non_admission_is_not_openness": status != "TRACE_PRESERVED",
        "open_in_emitted": False,
        "tokens_issued": 0,
    }


def _transport_questions(
    artifact_b: dict[str, Any],
    frame_b: dict[str, Any],
    external_frame: dict[str, Any],
    composite: dict[str, str],
    question_ids: Sequence[str],
    form_ids: Sequence[str],
) -> list[dict[str, Any]]:
    source_occurrences = _frame_occurrences(frame_b)
    target_occurrences = _frame_occurrences(external_frame)
    inverse = {target: source for source, target in composite.items()}
    if set(inverse) != set(target_occurrences):
        raise ValueError("question transport requires a total composite equivalence")
    matrix = external_frame["admitted_equality"]["matrix"]
    class_of = external_frame["admitted_equality"]["class_of"]
    records: list[dict[str, Any]] = []
    for question_id in question_ids:
        source_values = {
            source_id: _question_value(
                question_id, source_id, item, artifact_b, frame_b
            )
            for source_id, item in source_occurrences.items()
        }
        values = {target: source_values[inverse[target]] for target in sorted(target_occurrences)}
        separating = [
            (left, right)
            for left in sorted(target_occurrences)
            for right in sorted(target_occurrences)
            if matrix[left][right] and values[left] != values[right]
        ]
        resolved = not separating
        factor: dict[str, str] = {}
        if resolved:
            for occurrence_id, value in values.items():
                key = class_of[occurrence_id]
                if key in factor and factor[key] != value:
                    raise RuntimeError("transported resolved question did not factor")
                factor[key] = value
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
        records.append(
            {
                "frame_id": external_frame["frame_id"],
                "frame_equality": external_frame["admitted_equality"]["definition"],
                "language": external_frame["language"],
                "question_id": question_id,
                "total": len(values) == len(target_occurrences),
                "resolved_in_frame": resolved,
                "open_in_frame": not resolved,
                "factorization": (
                    {
                        "through_external_frame_quotient": True,
                        "unique": True,
                        "factor_sha256": digest_value(factor),
                    }
                    if resolved
                    else None
                ),
                "open_witness": witness,
                "explicit_translation_lineage": {
                    "translational_form_ids": list(form_ids),
                    "composite_occurrence_map_sha256": digest_value(composite),
                    "target_axiom_geometry_assumption_id": external_frame[
                        "axiom_geometry_assumption_id"
                    ],
                },
                "bare_open_label": False,
            }
        )
    return records


def _raw_central_interaction_candidate(
    frame_a: dict[str, Any],
    coordinate_frame: dict[str, Any],
    central_frame: dict[str, Any],
) -> dict[str, Any]:
    """Construct the extension/retraction proposal without evaluating its laws."""

    coordinate_occurrences = _frame_occurrences(coordinate_frame)
    central_occurrences = _frame_occurrences(central_frame)
    central_lookup = _lookup(central_frame)
    a_lookup = _lookup(frame_a)
    # The frame's class identifiers are hashes, whereas this interaction is declared on its local
    # identity basis. Recover that basis solely from the already-frozen occurrences.
    local_basis = sorted(
        {
            item["evaluated_local_result"]
            for item in _frame_occurrences(frame_a).values()
        }
    )
    identity_relation = [
        [base, _central_identity(base, bit)] for base in local_basis for bit in (0, 1)
    ]
    cross_relation = [
        [source_id, target_id]
        for source_id, source_item in sorted(coordinate_occurrences.items())
        for target_id, target_item in sorted(central_occurrences.items())
        if _split_central_identity(target_item["evaluated_local_result"])[0]
        == source_item["evaluated_local_result"]
    ]
    embedding = {
        source_id: central_lookup[
            (item["constructor"], _central_identity(item["evaluated_local_result"], 0))
        ]
        for source_id, item in coordinate_occurrences.items()
    }
    quotient = {
        source_id: a_lookup[
            (
                _opposite_constructor(item["constructor"]),
                _split_central_identity(item["evaluated_local_result"])[0],
            )
        ]
        for source_id, item in central_occurrences.items()
    }
    return {
        "source_coordinate_frame_id": coordinate_frame["frame_id"],
        "central_frame_id": central_frame["frame_id"],
        "returned_frame_id": frame_a["frame_id"],
        "identity_relation_S": identity_relation,
        "occurrence_relation_R": cross_relation,
        "embedding_e": dict(sorted(embedding.items())),
        "quotient_q": dict(sorted(quotient.items())),
        "verdicts_present": False,
    }


def _central_trace(
    artifact_a: dict[str, Any],
    frame_a: dict[str, Any],
    coordinate_frame: dict[str, Any],
    central_frame: dict[str, Any],
    native_map: dict[str, str],
    coordinate_map: dict[str, str],
    frame_b: dict[str, Any],
    native_form_id: str,
    coordinate_form_id: str,
    returned_basis: dict[str, Any],
    native_certificate: dict[str, Any],
    coordinate_certificate: dict[str, Any],
    frozen_candidate: dict[str, Any] | None = None,
) -> dict[str, Any]:
    table_a = artifact_a["execution"]["operation_table"]
    coordinate_occurrences = _frame_occurrences(coordinate_frame)
    central_occurrences = _frame_occurrences(central_frame)
    a_occurrences = _frame_occurrences(frame_a)
    central_lookup = _lookup(central_frame)
    a_lookup = {
        (item["constructor"], item["evaluated_local_result"]): occurrence_id
        for occurrence_id, item in a_occurrences.items()
    }

    candidate = frozen_candidate or _raw_central_interaction_candidate(
        frame_a, coordinate_frame, central_frame
    )
    if (
        candidate["source_coordinate_frame_id"] != coordinate_frame["frame_id"]
        or candidate["central_frame_id"] != central_frame["frame_id"]
        or candidate["returned_frame_id"] != frame_a["frame_id"]
        or candidate["verdicts_present"]
    ):
        raise ValueError("frozen central interaction candidate does not match its isolations")
    identity_relation = [list(pair) for pair in candidate["identity_relation_S"]]
    identity_relation_set = {tuple(pair) for pair in identity_relation}
    cross_relation = [list(pair) for pair in candidate["occurrence_relation_R"]]
    cross_relation_set = {tuple(pair) for pair in cross_relation}
    embedding = dict(candidate["embedding_e"])
    quotient = dict(candidate["quotient_q"])

    coordinate_matrix = coordinate_frame["admitted_equality"]["matrix"]
    central_matrix = central_frame["admitted_equality"]["matrix"]
    a_matrix = frame_a["admitted_equality"]["matrix"]
    embedding_failures: list[Failure] = []
    for left in sorted(coordinate_occurrences):
        for right in sorted(coordinate_occurrences):
            observed = central_matrix[embedding[left]][embedding[right]]
            expected = coordinate_matrix[left][right]
            if observed != expected:
                embedding_failures.append(
                    Failure("split_extension_equality_on_image", [left, right], expected, observed)
                )

    quotient_preservation: list[Failure] = []
    quotient_reflection: list[Failure] = []
    for left in sorted(central_occurrences):
        for right in sorted(central_occurrences):
            source_equal = central_matrix[left][right]
            target_equal = a_matrix[quotient[left]][quotient[right]]
            if source_equal and not target_equal:
                quotient_preservation.append(
                    Failure("closure_quotient_preservation", [left, right], True, False)
                )
            if target_equal and not source_equal:
                quotient_reflection.append(
                    Failure("closure_quotient_expected_fibre", [left, right], False, True)
                )

    split_W_failures = []
    split_E_failures = []
    split_J_failures = []
    split_C_failures = []
    coordinate_lookup = _lookup(coordinate_frame)
    for source_id, target_id in cross_relation:
        source_item = coordinate_occurrences[source_id]
        target_item = central_occurrences[target_id]
        target_base, _ = _split_central_identity(target_item["evaluated_local_result"])
        if source_item["evaluated_local_result"] != target_base:
            split_W_failures.append([source_id, target_id])
        reversed_source = coordinate_lookup[
            (
                _opposite_constructor(source_item["constructor"]),
                source_item["evaluated_local_result"],
            )
        ]
        reversed_target = central_lookup[
            (
                _opposite_constructor(target_item["constructor"]),
                target_item["evaluated_local_result"],
            )
        ]
        if (reversed_source, reversed_target) not in cross_relation_set:
            split_J_failures.append([source_id, target_id])
    for base, external_identity in identity_relation:
        source_section = coordinate_lookup[("direct", base)]
        target_section = central_lookup[("direct", external_identity)]
        if (source_section, target_section) not in cross_relation_set:
            split_E_failures.append([base, external_identity])
        if (source_section, target_section) not in cross_relation_set:
            split_C_failures.append([base, external_identity])

    split_operation = []
    for source_left, target_left in identity_relation:
        for source_right, target_right in identity_relation:
            source_product = table_a[source_left][source_right]
            target_product = central_frame["operation_table"][target_left][target_right]
            if (source_product, target_product) not in identity_relation_set:
                split_operation.append(
                    [source_left, target_left, source_right, target_right]
                )

    embedding_operation = []
    quotient_operation = []
    for left in sorted(table_a):
        for right in sorted(table_a):
            product = table_a[left][right]
            h_left = _central_identity(left, 0)
            h_right = _central_identity(right, 0)
            observed = central_frame["operation_table"][h_left][h_right]
            expected = _central_identity(product, 0)
            if observed != expected:
                embedding_operation.append([left, right, expected, observed])
    for left in central_frame["identity_basis"]:
        for right in central_frame["identity_basis"]:
            product = central_frame["operation_table"][left][right]
            left_base, _ = _split_central_identity(left)
            right_base, _ = _split_central_identity(right)
            product_base, _ = _split_central_identity(product)
            expected = table_a[left_base][right_base]
            if product_base != expected:
                quotient_operation.append([left, right, expected, product_base])

    quotient_W_failures = []
    quotient_E_failures = []
    quotient_J_failures = []
    quotient_C_failures = []
    for source_id, target_id in quotient.items():
        source_item = central_occurrences[source_id]
        target_item = a_occurrences[target_id]
        source_base, _ = _split_central_identity(source_item["evaluated_local_result"])
        if source_base != target_item["evaluated_local_result"]:
            quotient_W_failures.append([source_id, target_id])
        reversed_source = central_lookup[
            (
                _opposite_constructor(source_item["constructor"]),
                source_item["evaluated_local_result"],
            )
        ]
        reversed_target = a_lookup[
            (
                _opposite_constructor(target_item["constructor"]),
                target_item["evaluated_local_result"],
            )
        ]
        if quotient[reversed_source] != reversed_target:
            quotient_J_failures.append([source_id, target_id])
    for external_identity in central_frame["identity_basis"]:
        base, _ = _split_central_identity(external_identity)
        source_section = central_lookup[("direct", external_identity)]
        expected_section = a_lookup[("right_identity_extended", base)]
        if quotient[source_section] != expected_section:
            quotient_E_failures.append([external_identity, expected_section])
        if quotient[source_section] != expected_section:
            quotient_C_failures.append([external_identity, expected_section])

    related_targets = {target for _, target in cross_relation}
    related_sources = {source for source, _ in cross_relation}
    new_residues = sorted(
        occurrence_id
        for occurrence_id, item in central_occurrences.items()
        if _split_central_identity(item["evaluated_local_result"])[1] == 1
    )
    split_transition_seed = {
        "source": coordinate_frame["frame_id"],
        "target": central_frame["frame_id"],
        "relation": cross_relation,
        "embedding": embedding,
    }
    split_transition_id = digest_value(split_transition_seed)
    quotient_transition_seed = {
        "source": central_frame["frame_id"],
        "target": frame_a["frame_id"],
        "quotient": quotient,
    }
    quotient_transition_id = digest_value(quotient_transition_seed)

    lineages = []
    composite: dict[str, str] = {}
    relational_endpoint_pairs: list[list[str]] = []
    relational_composition_failures = []
    for source_b in sorted(native_map):
        native_a = native_map[source_b]
        coordinate = coordinate_map[native_a]
        central_zero = embedding[coordinate]
        all_central_branches = sorted(
            target for source, target in cross_relation if source == coordinate
        )
        all_returned_branches = sorted({quotient[target] for target in all_central_branches})
        final_zero = quotient[central_zero]
        composite[source_b] = final_zero
        expected_closure_fibre = sorted(
            target for target in a_occurrences if a_matrix[native_a][target]
        )
        relational_endpoint_pairs.extend(
            [source_b, target] for target in all_returned_branches
        )
        if all_returned_branches != expected_closure_fibre:
            relational_composition_failures.append(
                [source_b, expected_closure_fibre, all_returned_branches]
            )
        lineages.append(
            {
                "source_occurrence": source_b,
                "native_occurrence": native_a,
                "external_coordinate_occurrence": coordinate,
                "central_isolation_occurrences": all_central_branches,
                "returned_occurrences": all_returned_branches,
                "all_external_branches_recover_native_closure_identity": all(
                    a_matrix[native_a][target] for target in all_returned_branches
                ),
                "relational_composite_is_exactly_native_closure_fibre": (
                    all_returned_branches == expected_closure_fibre
                ),
                "selected_embedding_retraction_agrees_with_native_occurrence": (
                    final_zero == native_a
                ),
            }
        )

    frame_b_matrix = frame_b["admitted_equality"]["matrix"]
    composite_equality_failures = []
    for left in sorted(native_map):
        for right in sorted(native_map):
            expected = frame_b_matrix[left][right]
            observed = a_matrix[composite[left]][composite[right]]
            if observed != expected:
                composite_equality_failures.append([left, right, expected, observed])

    replay = returned_basis["new_execution"]
    external_basis_map = coordinate_certificate["explicit_translational_form"][
        "candidate_T"
    ]["basis_map"]
    external_word = [external_basis_map[element] for element in replay["translated_word"]]
    identity_a = artifact_a["execution"]["group_certificate"]["identity"]
    external_result = identity_a
    for element in external_word:
        external_result = table_a[external_result][element]
    central_word = [_central_identity(element, 0) for element in external_word]
    central_result = _central_identity(identity_a, 0)
    for element in central_word:
        central_result = central_frame["operation_table"][central_result][element]
    returned_result, _ = _split_central_identity(central_result)
    held_out_replay = {
        "source_word": replay["source_word"],
        "native_translated_word": replay["translated_word"],
        "external_coordinate_word": external_word,
        "central_extension_word": central_word,
        "expected_returned_result": replay["expected_target_result"],
        "external_coordinate_result": external_result,
        "central_extension_result": central_result,
        "closure_quotient_result": returned_result,
        "passed": replay["expected_target_result"] == external_result == returned_result,
    }

    split_transition = {
        "transition_id": split_transition_id,
        "relation_kind": "SPLIT_EXTENSION",
        "source_assumption_id": coordinate_frame["axiom_geometry_assumption_id"],
        "target_assumption_id": central_frame["axiom_geometry_assumption_id"],
        "identity_relation_S": identity_relation,
        "occurrence_relation_R": cross_relation,
        "embedding_e": dict(sorted(embedding.items())),
        "coverage": {
            "source_total": related_sources == set(coordinate_occurrences),
            "target_total": related_targets == set(central_occurrences),
            "new_target_residues": new_residues,
            "unrelated_target_residues": sorted(set(central_occurrences) - related_targets),
        },
        "equality_law": {
            "mode": "iff_on_embedding_image",
            "cases": len(coordinate_occurrences) ** 2,
            "failure_count": len(embedding_failures),
            "first_failure": asdict(embedding_failures[0]) if embedding_failures else None,
        },
        "naturality": {
            "W_relation_cases": len(cross_relation),
            "W_failure_count": len(split_W_failures),
            "E_relation_cases": len(identity_relation),
            "E_failure_count": len(split_E_failures),
            "J_relation_cases": len(cross_relation),
            "J_failure_count": len(split_J_failures),
            "C_relation_cases": len(identity_relation),
            "C_failure_count": len(split_C_failures),
            "operation_cases": len(identity_relation) ** 2,
            "operation_failure_count": len(split_operation),
            "embedding_operation_cases": len(table_a) ** 2,
            "embedding_operation_failure_count": len(embedding_operation),
        },
        "typed_not_geom_equiv": True,
        "orientation_translation_pi": "preserved_on_embedding",
        "closure_lineage_complete": (
            not embedding_failures
            and not split_W_failures
            and not split_E_failures
            and not split_J_failures
            and not split_C_failures
            and not split_operation
            and not embedding_operation
            and related_sources == set(coordinate_occurrences)
            and related_targets == set(central_occurrences)
        ),
    }
    quotient_transition = {
        "transition_id": quotient_transition_id,
        "relation_kind": "CLOSURE_QUOTIENT",
        "source_assumption_id": central_frame["axiom_geometry_assumption_id"],
        "target_assumption_id": frame_a["axiom_geometry_assumption_id"],
        "quotient_q": dict(sorted(quotient.items())),
        "coverage": {
            "source_total": set(quotient) == set(central_occurrences),
            "target_total": set(quotient.values()) == set(a_occurrences),
        },
        "equality_law": {
            "mode": "quotient_preservation_with_explicit_fibres",
            "preservation_cases": len(central_occurrences) ** 2,
            "preservation_failure_count": len(quotient_preservation),
            "reflection_not_required_for_quotient": True,
            "collapsed_fibre_pair_count": len(quotient_reflection),
            "first_collapsed_fibre": (
                asdict(quotient_reflection[0]) if quotient_reflection else None
            ),
        },
        "naturality": {
            "W_cases": len(central_occurrences),
            "W_failure_count": len(quotient_W_failures),
            "E_cases": len(central_frame["identity_basis"]),
            "E_failure_count": len(quotient_E_failures),
            "J_cases": len(central_occurrences),
            "J_failure_count": len(quotient_J_failures),
            "C_cases": len(central_frame["identity_basis"]),
            "C_failure_count": len(quotient_C_failures),
            "operation_cases": len(central_frame["identity_basis"]) ** 2,
            "operation_failure_count": len(quotient_operation),
        },
        "typed_not_geom_equiv": True,
        "orientation_translation_pi": "reversed",
        "closure_lineage_complete": (
            not quotient_preservation
            and not quotient_W_failures
            and not quotient_E_failures
            and not quotient_J_failures
            and not quotient_C_failures
            and not quotient_operation
        ),
    }
    native_transition = {
        "transition_id": native_form_id,
        "relation_kind": "GEOM_EQUIV",
        "transition_role": "closure_native_translation",
        "source_assumption_id": frame_b["axiom_geometry_assumption_id"],
        "target_assumption_id": frame_a["axiom_geometry_assumption_id"],
        "geom_equiv": native_certificate["geom_equiv"],
        "naturality": native_certificate["naturality"],
        "closure_lineage_complete": native_certificate["admitted_translation"],
    }
    coordinate_transition = {
        "transition_id": coordinate_form_id,
        "relation_kind": "GEOM_EQUIV",
        "transition_role": "external_coordinate_reexpression",
        "source_assumption_id": frame_a["axiom_geometry_assumption_id"],
        "target_assumption_id": coordinate_frame["axiom_geometry_assumption_id"],
        "geom_equiv": coordinate_certificate["geom_equiv"],
        "naturality": coordinate_certificate["naturality"],
        "closure_lineage_complete": coordinate_certificate[
            "explicit_translational_form"
        ]["closure_chain_complete"],
    }
    trace_preserved = (
        native_transition["closure_lineage_complete"]
        and coordinate_transition["closure_lineage_complete"]
        and split_transition["closure_lineage_complete"]
        and quotient_transition["closure_lineage_complete"]
        and all(
            item["all_external_branches_recover_native_closure_identity"]
            for item in lineages
        )
        and all(
            item["relational_composite_is_exactly_native_closure_fibre"]
            for item in lineages
        )
        and all(
            item["selected_embedding_retraction_agrees_with_native_occurrence"]
            for item in lineages
        )
        and not composite_equality_failures
        and not relational_composition_failures
        and held_out_replay["passed"]
    )
    return {
        "status": "TRACE_PRESERVED" if trace_preserved else "COMPOSITION_OBSTRUCTION",
        "continuity_meaning": "gap-free finite relational and receipt continuity, not topology",
        "isolation_sequence": [
            frame_b["frame_id"],
            frame_a["frame_id"],
            coordinate_frame["frame_id"],
            central_frame["frame_id"],
            frame_a["frame_id"],
        ],
        "selected_translation_ids": [
            native_form_id,
            coordinate_form_id,
            split_transition_id,
            quotient_transition_id,
        ],
        "adjacent_relations": [
            native_transition,
            coordinate_transition,
            split_transition,
            quotient_transition,
        ],
        "occurrence_lineages": lineages,
        "lineage_count": len(lineages),
        "composite_coherence": {
            "cases": len(lineages),
            "failure_count": sum(
                not item["selected_embedding_retraction_agrees_with_native_occurrence"]
                for item in lineages
            ),
            "equality_cases": len(native_map) ** 2,
            "equality_failure_count": len(composite_equality_failures),
            "direct_recomputation_agrees": not composite_equality_failures,
            "selected_split_retraction_point_map": dict(sorted(composite.items())),
            "full_relational_endpoint_pairs": relational_endpoint_pairs,
            "full_relational_endpoint_pair_count": len(relational_endpoint_pairs),
            "full_relational_composition_failure_count": len(
                relational_composition_failures
            ),
            "full_relational_composite_is_native_closure_relation": (
                not relational_composition_failures
            ),
        },
        "split_relation_pair_count": len(cross_relation),
        "all_new_isolation_residues_relationally_identified": (
            related_targets == set(central_occurrences)
        ),
        "final_returned_basis": returned_basis,
        "returned_basis_content_sha256": digest_value(returned_basis),
        "held_out_next_basis_replay": held_out_replay,
        "first_obstruction": None if trace_preserved else (
            composite_equality_failures[0] if composite_equality_failures else "adjacent failure"
        ),
        "tokens_issued": 0,
    }


def _copy_inputs(source: Path, target: Path) -> dict[str, Path]:
    sources = {
        "presentation_a_frozen.json": source / "presentation_a_frozen.json",
        "presentation_b_frozen.json": source / "presentation_b_frozen.json",
        "frame_a_frozen.json": source / "frame_a_frozen.json",
        "frame_b_frozen.json": source / "frame_b_frozen.json",
        "candidate_family_frozen.json": source / "candidate_family_frozen.json",
        "shared_manifest.json": source / "shared_manifest.json",
        "upstream_paired_receipts.jsonl": source / "receipts.jsonl",
        "upstream_protocol.json": PAIRED_BENCHMARK / "protocol.json",
        "upstream_questions.json": PAIRED_BENCHMARK / "questions.json",
        "upstream_frame_a_protocol.json": PAIRED_BENCHMARK / "frame_a_protocol.json",
        "upstream_frame_b_protocol.json": PAIRED_BENCHMARK / "frame_b_protocol.json",
    }
    copied: dict[str, Path] = {}
    for name, source_path in sources.items():
        destination = target / name
        shutil.copyfile(source_path, destination)
        copied[name] = destination
    return copied


def run_three_part_simulation(output_dir: Path = DEFAULT_OUTPUT) -> dict[str, Any]:
    output_dir.mkdir(parents=True, exist_ok=True)
    for old in output_dir.glob("*"):
        if old.is_file():
            old.unlink()

    protocol_path = BENCHMARK / "protocol.json"
    geometry_packet_path = BENCHMARK / "external_assumptions.json"
    candidate_packet_path = BENCHMARK / "external_candidates.json"
    protocol = load_json(protocol_path)
    registered_packets = protocol["registered_packet_sha256"]
    external_geometry_commitment = registered_packets["external_geometries"]
    external_candidate_commitment = registered_packets["external_candidates"]
    if file_digest(geometry_packet_path) != external_geometry_commitment:
        raise ValueError("external geometry packet does not match the registered precommit")
    if file_digest(candidate_packet_path) != external_candidate_commitment:
        raise ValueError("external candidate packet does not match the registered precommit")
    chain = ReceiptChain()
    chain.append(
        "THREE_PART_PRECOMMIT",
        {
            "protocol_sha256": file_digest(protocol_path),
            "questions_sha256": file_digest(QUESTIONS),
            "registered_external_geometry_sha256": external_geometry_commitment,
            "registered_external_candidate_sha256": external_candidate_commitment,
            "external_geometry_packet_parsed": False,
            "external_candidate_packet_parsed": False,
            "questions_and_geometries_frozen_before_interaction": True,
            "control_statuses_precommitted_in_protocol": True,
        },
    )

    with tempfile.TemporaryDirectory(prefix="three-part-upstream-") as temporary_name:
        upstream_dir = Path(temporary_name) / "paired"
        paired = run_comparison(upstream_dir)
        copied = _copy_inputs(upstream_dir, output_dir)
        fixed = load_json(upstream_dir / "fixed_frame_arm.json")
        closure = load_json(upstream_dir / "closure_arm.json")
        part_1 = {
            "schema_version": 1,
            "part": 1,
            "architecture": "classical_full_mathematical_stack_bounded",
            "claim_boundary": "strong finite proof/isomorphism stack; not an actual ASI",
            "status": fixed["status"],
            "frozen_input_hashes": {name: file_digest(path) for name, path in copied.items()},
            "exhaustive_local_and_cross_frame_verification": fixed,
            "formal_kernel_integration": {
                "lake_target": "NRRF627",
                "bridge_module": "lean/NRRF631RuntimeFrameConditionalBridge.lean",
                "bridge_source_sha256": file_digest(
                    ROOT / "lean" / "NRRF631RuntimeFrameConditionalBridge.lean"
                ),
                "verification": "separate lake build and CI job; this JSON does not forge a kernel verdict",
            },
            "external_geometry_or_candidate_packet_was_not_an_input": True,
            "bare_open_label_emitted": False,
        }
        write_json(output_dir / "part_1_classical_stack.json", part_1)
        chain.append(
            "PART_1_CLASSICAL_STACK_FROZEN",
            {
                "sha256": file_digest(output_dir / "part_1_classical_stack.json"),
                "status": part_1["status"],
                "external_packets_supplied_as_inputs": False,
            },
        )

        part_2 = {
            "schema_version": 1,
            "part": 2,
            "architecture": "closure_native_translation",
            "claim_boundary": "bounded explicit translational verifier; not an actual ASI",
            "status": closure["status"],
            "closure_native_arm": closure,
            "upstream_paired_receipt_head": paired["receipt_chain"]["head"],
            "explicit_order": [
                "locally assumed frame equalities",
                "raw T",
                "GeomEquiv preservation and reflection",
                "(T, phi, pi)",
                "W/E/J/C and operation naturality",
                "quotient factor or witnessed OpenIn",
                "next-basis transfer",
            ],
            "external_geometry_or_candidate_packet_was_not_an_input": True,
        }
        write_json(output_dir / "part_2_closure_native.json", part_2)
        chain.append(
            "PART_2_CLOSURE_NATIVE_FROZEN",
            {
                "sha256": file_digest(output_dir / "part_2_closure_native.json"),
                "status": part_2["status"],
                "external_packets_supplied_as_inputs": False,
                "native_tokens_issued": closure["tokens_issued"],
            },
        )

    geometry_packet = reveal_external_packet(
        geometry_packet_path, external_geometry_commitment
    )
    chain.append(
        "EXTERNAL_GEOMETRY_PACKET_REVEALED",
        {
            "sha256": file_digest(geometry_packet_path),
            "registered_precommit_verified": True,
            "parts_1_and_2_already_frozen": True,
            "candidate_packet_revealed": False,
        },
    )

    artifact_a = load_json(output_dir / "presentation_a_frozen.json")
    artifact_b = load_json(output_dir / "presentation_b_frozen.json")
    frame_a = load_json(output_dir / "frame_a_frozen.json")
    frame_b = load_json(output_dir / "frame_b_frozen.json")
    external_frames = [
        instantiate_external_geometry(artifact_a, assumption)
        for assumption in geometry_packet["exact_geometries"]
    ]
    central_frame = instantiate_central_isolation(
        artifact_a, geometry_packet["non_bijective_interaction"]
    )
    frame_bundle = {
        "schema_version": 1,
        "external_geometry_packet_sha256": external_geometry_commitment,
        "exact_frames": external_frames,
        "central_isolation_frame": central_frame,
        "all_frames_evaluated_in_own_declared_geometry": all(
            frame["internal_unified_evaluation"][
                "evaluated_only_in_declared_external_geometry"
            ]
            for frame in [*external_frames, central_frame]
        ),
        "candidate_interactions_visible_during_instantiation": False,
    }
    write_json(output_dir / "external_frames_frozen.json", frame_bundle)
    external_frames_sha256 = file_digest(output_dir / "external_frames_frozen.json")
    chain.append(
        "EXTERNAL_GEOMETRIES_INSTANTIATED_AND_FROZEN",
        {
            "sha256": external_frames_sha256,
            "frame_count": len(external_frames) + 1,
            "candidate_search_started": False,
            "all_declared_local_audits_passed": all(
                frame["internal_unified_evaluation"]["declared_obligations_passed"]
                for frame in [*external_frames, central_frame]
            ),
        },
    )

    # Consume the serialized frame boundary rather than the in-memory construction objects.
    frame_bundle = load_json(output_dir / "external_frames_frozen.json")
    if file_digest(output_dir / "external_frames_frozen.json") != external_frames_sha256:
        raise ValueError("external frame artifact changed after its freeze receipt")
    external_frames = frame_bundle["exact_frames"]
    central_frame = frame_bundle["central_isolation_frame"]
    geometry_ids = {frame["assumption_name"] for frame in external_frames}
    candidate_packet = reveal_external_candidate_packet(
        candidate_packet_path, external_candidate_commitment, geometry_ids
    )
    chain.append(
        "EXTERNAL_CANDIDATE_PACKET_REVEALED",
        {
            "sha256": file_digest(candidate_packet_path),
            "registered_precommit_verified": True,
            "external_geometries_already_frozen": True,
        },
    )

    external_by_name = {frame["assumption_name"]: frame for frame in external_frames}
    assumption_by_name = {
        assumption["assumption_id"]: assumption
        for assumption in geometry_packet["exact_geometries"]
    }
    candidate_by_name = {
        proposal["assumption_id"]: proposal
        for proposal in candidate_packet["candidate_proposals"]
    }
    candidate_bundle = {
        "schema_version": 1,
        "constructed_after_all_external_frames_frozen": True,
        "candidate_verdicts_present": False,
        "candidates": {},
    }
    for name in sorted(external_by_name):
        occurrence_map, basis_map, orientation = _external_candidate(
            artifact_a,
            frame_a,
            external_by_name[name],
            candidate_by_name[name]["candidate_kind"],
        )
        candidate_bundle["candidates"][name] = {
            "candidate_kind": candidate_by_name[name]["candidate_kind"],
            "source_frame_id": frame_a["frame_id"],
            "target_frame_id": external_by_name[name]["frame_id"],
            "occurrence_map": occurrence_map,
            "basis_map": basis_map,
            "orientation_proposal": orientation,
        }
    candidate_bundle["central_interaction"] = _raw_central_interaction_candidate(
        frame_a,
        external_by_name["external_coordinate_reexpression"],
        central_frame,
    )
    write_json(output_dir / "external_candidates_frozen.json", candidate_bundle)
    external_candidates_sha256 = file_digest(
        output_dir / "external_candidates_frozen.json"
    )
    chain.append(
        "EXTERNAL_INTERACTION_CANDIDATES_FROZEN",
        {
            "sha256": external_candidates_sha256,
            "candidate_count": len(candidate_bundle["candidates"]) + 2,
            "verdicts_present": False,
        },
    )
    candidate_bundle = load_json(output_dir / "external_candidates_frozen.json")
    if (
        file_digest(output_dir / "external_candidates_frozen.json")
        != external_candidates_sha256
    ):
        raise ValueError("external candidate artifact changed after its freeze receipt")
    exact_cases = [
        _external_exact_certificate(
            artifact_a,
            frame_a,
            external_by_name[name],
            assumption_by_name[name],
            candidate_by_name[name],
            candidate_bundle["candidates"][name],
        )
        for name in sorted(external_by_name)
    ]
    exact_by_name = {case["case"]: case for case in exact_cases}
    coordinate = exact_by_name["external_coordinate_reexpression"]
    if coordinate["status"] != "TRACE_PRESERVED":
        raise RuntimeError("selected external coordinate interaction was not admitted")

    native_case = next(
        case for case in closure["cases"] if case["case"] == "natural_contact"
    )
    native_certificate = native_case["certificates"][0]
    native_map = native_certificate["explicit_translational_form"]["candidate_T"][
        "occurrence_map"
    ]
    coordinate_map = coordinate["explicit_translational_form"]["candidate_T"][
        "occurrence_map"
    ]
    composite = {
        source: coordinate_map[target] for source, target in native_map.items()
    }
    questions = load_json(QUESTIONS)
    transported_questions = _transport_questions(
        artifact_b,
        frame_b,
        external_by_name["external_coordinate_reexpression"],
        composite,
        [item["id"] for item in questions["questions"]],
        [
            native_certificate["explicit_translational_form"]["translational_form_id"],
            coordinate["explicit_translational_form"]["translational_form_id"],
        ],
    )
    continuous = _central_trace(
        artifact_a,
        frame_a,
        external_by_name["external_coordinate_reexpression"],
        central_frame,
        native_map,
        coordinate_map,
        frame_b,
        native_certificate["explicit_translational_form"]["translational_form_id"],
        coordinate["explicit_translational_form"]["translational_form_id"],
        closure["next_basis"],
        native_certificate,
        coordinate,
        candidate_bundle["central_interaction"],
    )

    reference_statuses = protocol["precommitted_control_statuses"]
    observed_statuses = {case["case"]: case["status"] for case in exact_cases}
    witnessed_open = [item for item in transported_questions if item["open_in_frame"]]
    part_3_ok = (
        observed_statuses == reference_statuses
        and continuous["status"] == "TRACE_PRESERVED"
        and all(
            item["open_witness"] is not None
            and item["open_witness"]["frame_equal"]
            and item["open_witness"]["left_value"] != item["open_witness"]["right_value"]
            for item in witnessed_open
        )
    )
    part_3 = {
        "schema_version": 1,
        "part": 3,
        "architecture": "closure_preservation_under_external_assumption_interaction",
        "claim_boundary": (
            "bounded external-assumption stress test; does not establish the truth of the "
            "assumptions or preservation under arbitrary mathematics"
        ),
        "status": "PASS" if part_3_ok else "FAIL",
        "external_geometry_packet_sha256": external_geometry_commitment,
        "external_candidate_packet_sha256": external_candidate_commitment,
        "geometry_packet_revealed_after_parts_1_and_2": True,
        "candidate_packet_revealed_after_external_frame_freeze": True,
        "exact_interactions": exact_cases,
        "transported_frame_question_relations": transported_questions,
        "all_open_records_have_separating_witnesses": all(
            item["open_witness"] is not None for item in witnessed_open
        ),
        "continuous_relational_identification": continuous,
        "closure_preservation_definition": (
            "identity remains recoverable through every immutable isolation by typed adjacent "
            "relations, exhaustive W/E/J/C/operation checks, relational coverage, and coherent composition"
        ),
        "continuous_does_not_mean_topological": True,
        "failure_or_partial_data_is_never_open": all(
            case["open_in_emitted"] is False
            for case in exact_cases
            if case["status"] != "TRACE_PRESERVED"
        ),
        "tokens_issued": 0,
    }
    write_json(output_dir / "part_3_external_interaction.json", part_3)
    chain.append(
        "PART_3_EXTERNAL_INTERACTION_FROZEN",
        {
            "sha256": file_digest(output_dir / "part_3_external_interaction.json"),
            "status": part_3["status"],
            "continuous_trace_status": continuous["status"],
            "additional_tokens_issued": 0,
        },
    )

    summary = {
        "schema_version": 1,
        "benchmark": protocol["benchmark"],
        "claim_status": "EXECUTED_BOUNDED_THREE_PART_PROXY",
        "actual_asi_or_aristotle_run": False,
        "parts": {
            "classical_full_stack": part_1["status"],
            "closure_native_translation": part_2["status"],
            "external_assumption_interaction": part_3["status"],
        },
        "causal_order": [
            "verify registered geometry/candidate packet hashes without supplying them to Parts 1 or 2",
            "freeze strong classical full-stack proxy",
            "freeze closure-native explicit translation",
            "consume the geometry packet, freeze frames, then consume candidate proposals",
            "assume and audit external geometries in their own terms",
            "test exact and typed non-bijective interactions",
            "verify continuous composite relational identification",
        ],
        "continuous_trace_preserved_for_bounded_fixture": continuous["status"]
        == "TRACE_PRESERVED",
        "arbitrary_external_assumption_preservation": "NOT_CLAIMED",
        "native_tokens_issued": closure["tokens_issued"],
        "external_interaction_additional_tokens": 0,
        "total_tokens_issued": closure["tokens_issued"],
        "artifact_hashes": {
            "protocol": file_digest(protocol_path),
            "questions": file_digest(QUESTIONS),
            "external_geometries": external_geometry_commitment,
            "external_candidate_proposals": external_candidate_commitment,
            "part_1": file_digest(output_dir / "part_1_classical_stack.json"),
            "part_2": file_digest(output_dir / "part_2_closure_native.json"),
            "external_frames": file_digest(output_dir / "external_frames_frozen.json"),
            "external_candidates": file_digest(
                output_dir / "external_candidates_frozen.json"
            ),
            "part_3": file_digest(output_dir / "part_3_external_interaction.json"),
        },
        "overall_status": (
            "PASS"
            if part_1["status"] == "PASS"
            and part_2["status"] == "PASS"
            and part_3["status"] == "PASS"
            else "FAIL"
        ),
    }
    chain.append("THREE_PART_SUMMARY", {"sha256": digest_value(summary)})
    summary["receipt_chain"] = chain.verify()
    write_json(output_dir / "three_part_result.json", summary)
    (output_dir / "receipts.jsonl").write_text(
        "".join(canonical_json(item) + "\n" for item in chain.items), encoding="utf-8"
    )
    return summary


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--assert-reference", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = _parse_args()
    result = run_three_part_simulation(args.output_dir)
    print(json.dumps(result, indent=2, sort_keys=True))
    if args.assert_reference:
        passed = (
            result["overall_status"] == "PASS"
            and result["continuous_trace_preserved_for_bounded_fixture"]
            and result["total_tokens_issued"] == 1
            and result["external_interaction_additional_tokens"] == 0
            and result["receipt_chain"]["ok"]
        )
        return 0 if passed else 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
