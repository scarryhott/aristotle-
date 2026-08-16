#!/usr/bin/env python3
"""Causally staged generative axiom-geometry isolation proxy.

This is a bounded deterministic finite-model experiment, not an ASI or an
Aristotle result.  Two generator subprocesses receive the same abstract
objective and different precommitted construction contexts.  They cannot see
one another's context or artifact through their command interfaces.  After
both outputs are content-addressed and frozen, a third subprocess receives
only the immutable artifacts, objective, verifier protocol, and disclosure
manifest.

The subprocess boundary establishes a reproducible causal ordering; it does
not establish epistemic independence or sandbox hostile code.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import asdict, dataclass
from itertools import permutations
import json
import math
from pathlib import Path
import random
import shutil
import subprocess
import sys
import tempfile
from typing import Any, Callable, Iterable, Sequence

PROJECT_ROOT = Path(__file__).resolve().parents[1]
if str(PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJECT_ROOT))

from experiments.full_stack_math_asi import (
    ReceiptChain,
    canonical_json,
    digest_value,
    file_digest,
    group_certificate,
    load_json,
    write_json,
)


BENCHMARK = PROJECT_ROOT / "benchmarks" / "generative_axiom_geometry_isolation"
DEFAULT_OUTPUT = PROJECT_ROOT / "runs" / "generative_axiom_geometry_isolation" / "latest"
OBJECTIVE = BENCHMARK / "objective.json"
CONTEXT_A = BENCHMARK / "agent_a_context.json"
CONTEXT_B = BENCHMARK / "agent_b_context.json"
VERIFIER_PROTOCOL = BENCHMARK / "verifier_protocol.json"
RAW_AGENT_A = BENCHMARK / "raw_agent_a.json"
RAW_AGENT_B_FINITE = BENCHMARK / "raw_agent_b_finite.json"
RAW_AGENT_B_INTERFACE_VARIANT = BENCHMARK / "raw_agent_b.json"
POLE_COUNT = 2


@dataclass(frozen=True)
class Failure:
    check: str
    input: object
    expected: object
    observed: object


def _payload_digest(artifact: dict[str, Any]) -> str:
    payload = dict(artifact)
    payload.pop("artifact_content_id", None)
    return digest_value(payload)


def _permutation_compose(left: tuple[int, ...], right: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(left[right[index]] for index in range(len(left)))


def _generated_closure(
    identity: tuple[int, ...],
    generators: Sequence[tuple[int, ...]],
    operation: Callable[[tuple[int, ...], tuple[int, ...]], tuple[int, ...]],
) -> tuple[tuple[int, ...], ...]:
    known = {identity, *generators}
    changed = True
    while changed:
        changed = False
        snapshot = tuple(known)
        for left in snapshot:
            for right in snapshot:
                product = operation(left, right)
                if product not in known:
                    known.add(product)
                    changed = True
    return tuple(sorted(known))


def _table_from_values(
    values: Sequence[tuple[int, ...]],
    labels: dict[tuple[int, ...], str],
    operation: Callable[[tuple[int, ...], tuple[int, ...]], tuple[int, ...]],
) -> dict[str, dict[str, str]]:
    return {
        labels[left]: {labels[right]: labels[operation(left, right)] for right in values}
        for left in values
    }


def _is_nonabelian(table: dict[str, dict[str, str]]) -> bool:
    return any(
        table[left][right] != table[right][left]
        for left in table
        for right in table
    )


def _labels(
    role: str, prefix: str, seed: int, values: Sequence[tuple[int, ...]]
) -> dict[tuple[int, ...], str]:
    shuffled = list(range(len(values)))
    random.Random(seed).shuffle(shuffled)
    return {
        value: f"{prefix}_{role.lower()}_{shuffled[index]:02d}"
        for index, value in enumerate(values)
    }


def _candidate_summary(table: dict[str, dict[str, str]], target: dict[str, Any]) -> dict[str, Any]:
    certificate = group_certificate(table)
    orders = sorted(value for value in certificate["orders"].values() if value is not None)
    matches = (
        certificate["passed"]
        and len(table) == int(target["carrier_size"])
        and _is_nonabelian(table) == bool(target["nonabelian"])
        and orders == list(target["element_order_multiset"])
    )
    return {
        "carrier_size": len(table),
        "group_certificate_passed": certificate["passed"],
        "nonabelian": _is_nonabelian(table),
        "element_order_multiset": orders,
        "matches_objective": matches,
    }


def _search_permutation_model(
    objective: dict[str, Any], context: dict[str, Any]
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    search: list[dict[str, Any]] = []
    target = objective["shared_abstract_constraints"]
    for degree in context["candidate_degrees"]:
        identity = tuple(range(degree))
        rotation = tuple((index + 1) % degree for index in range(degree))
        reflection = tuple((-index) % degree for index in range(degree))
        values = _generated_closure(
            identity, (rotation, reflection), _permutation_compose
        )
        labels = _labels(
            context["agent_role"], context["local_label_prefix"], int(context["seed"]), values
        )
        table = _table_from_values(values, labels, _permutation_compose)
        summary = {
            "candidate_parameter": degree,
            "construction": "rotation/reflection permutation closure",
            **_candidate_summary(table, target),
        }
        search.append(summary)
        if summary["matches_objective"]:
            return (
                {
                    "values": values,
                    "labels": labels,
                    "table": table,
                    "encodings": {labels[value]: list(value) for value in values},
                    "r": labels[rotation],
                    "s": labels[reflection],
                    "parameter": degree,
                },
                search,
            )
    raise RuntimeError("agent A found no local model satisfying the shared objective")


def _affine_multiply(left: tuple[int, ...], right: tuple[int, ...]) -> tuple[int, ...]:
    modulus, left_scale, left_shift = left
    other_modulus, right_scale, right_shift = right
    if modulus != other_modulus:
        raise ValueError("mixed affine moduli")
    return (
        modulus,
        (left_scale * right_scale) % modulus,
        (left_scale * right_shift + left_shift) % modulus,
    )


def _search_affine_model(
    objective: dict[str, Any], context: dict[str, Any]
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    search: list[dict[str, Any]] = []
    target = objective["shared_abstract_constraints"]
    for prime in context["candidate_primes"]:
        values = tuple(
            sorted(
                (prime, scale, shift)
                for scale in range(1, prime)
                for shift in range(prime)
            )
        )
        labels = _labels(
            context["agent_role"], context["local_label_prefix"], int(context["seed"]), values
        )
        table = _table_from_values(values, labels, _affine_multiply)
        summary = {
            "candidate_parameter": prime,
            "construction": "affine transformations x -> a*x+b over F_p",
            **_candidate_summary(table, target),
        }
        search.append(summary)
        if summary["matches_objective"]:
            rotation = (prime, 1, 1)
            reflection = (prime, prime - 1, 0)
            return (
                {
                    "values": values,
                    "labels": labels,
                    "table": table,
                    "encodings": {
                        labels[value]: {
                            "modulus": value[0],
                            "scale": value[1],
                            "shift": value[2],
                        }
                        for value in values
                    },
                    "r": labels[rotation],
                    "s": labels[reflection],
                    "parameter": prime,
                },
                search,
            )
    raise RuntimeError("agent B found no local model satisfying the shared objective")


def _power(table: dict[str, dict[str, str]], identity: str, value: str, exponent: int) -> str:
    current = identity
    for _ in range(exponent):
        current = table[current][value]
    return current


def _question_value(
    question_id: str,
    occurrence: dict[str, Any],
    table: dict[str, dict[str, str]],
    certificate: dict[str, Any],
) -> object:
    basis = occurrence["returned_identity"]
    if question_id == "element_order":
        return certificate["orders"][basis]
    if question_id == "square_is_identity":
        return table[basis][basis] == certificate["identity"]
    if question_id == "literal_pole":
        return occurrence["pole"]
    raise KeyError(question_id)


def _classes(
    role: str, signatures: dict[str, list[str]]
) -> tuple[list[dict[str, Any]], dict[str, str]]:
    remaining = set(signatures)
    classes: list[dict[str, Any]] = []
    class_of: dict[str, str] = {}
    while remaining:
        representative = min(remaining)
        members = sorted(
            occurrence
            for occurrence in signatures
            if signatures[occurrence] == signatures[representative]
        )
        class_id = digest_value(
            {"agent_role": role, "right_action_signature": signatures[representative]}
        )
        classes.append({"class_id": class_id, "members": members})
        for member in members:
            class_of[member] = class_id
            remaining.discard(member)
    return sorted(classes, key=lambda item: item["class_id"]), dict(sorted(class_of.items()))


def _evaluate_questions(
    objective: dict[str, Any],
    frame_id: str,
    assumption_id: str,
    occurrences: list[dict[str, Any]],
    matrix: dict[str, dict[str, bool]],
    class_of: dict[str, str],
    table: dict[str, dict[str, str]],
    certificate: dict[str, Any],
) -> list[dict[str, Any]]:
    occurrence_by_id = {item["occurrence_id"]: item for item in occurrences}
    ids = tuple(sorted(occurrence_by_id))
    records: list[dict[str, Any]] = []
    for question in objective["questions"]:
        question_id = question["id"]
        values = {
            occurrence_id: _question_value(
                question_id, occurrence_by_id[occurrence_id], table, certificate
            )
            for occurrence_id in ids
        }
        separating = [
            (left, right)
            for left in ids
            for right in ids
            if matrix[left][right] and values[left] != values[right]
        ]
        resolved = not separating
        factor: dict[str, object] = {}
        if resolved:
            for occurrence_id, value in values.items():
                key = class_of[occurrence_id]
                if key in factor and factor[key] != value:
                    raise RuntimeError("resolved local question did not factor")
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
                "frame_id": frame_id,
                "axiom_geometry_assumption_id": assumption_id,
                "question_id": question_id,
                "question_definition_sha256": digest_value(question),
                "total": len(values) == len(ids),
                "resolved_in_frame": resolved,
                "open_in_frame": not resolved,
                "factorization": (
                    {
                        "through_frame_quotient": True,
                        "unique": True,
                        "factor": dict(sorted(factor.items())),
                        "factor_sha256": digest_value(factor),
                    }
                    if resolved
                    else None
                ),
                "open_witness": witness,
                "separating_pair_count": len(separating),
                "bare_open_label": False,
            }
        )
    return records


def _local_audit(
    table: dict[str, dict[str, str]],
    certificate: dict[str, Any],
    occurrences: list[dict[str, Any]],
    W: dict[str, str],
    E: dict[str, dict[str, str]],
    J: dict[str, str],
    C: dict[str, str],
    matrix: dict[str, dict[str, bool]],
) -> dict[str, Any]:
    ids = tuple(sorted(W))
    basis = tuple(sorted(table))
    reflexivity = [value for value in ids if not matrix[value][value]]
    symmetry = [
        [left, right]
        for left in ids
        for right in ids
        if matrix[left][right] != matrix[right][left]
    ]
    transitivity = [
        [left, middle, right]
        for left in ids
        for middle in ids
        for right in ids
        if matrix[left][middle] and matrix[middle][right] and not matrix[left][right]
    ]
    returning = [
        occurrence
        for occurrence in ids
        if not matrix[occurrence][E[next(iter(E))][W[occurrence]]]
    ]
    grounded = [
        [left, right]
        for left in basis
        for right in basis
        if left != right and matrix[E[next(iter(E))][left]][E[next(iter(E))][right]]
    ]
    quotient = [
        [left, right]
        for left in ids
        for right in ids
        if matrix[left][right] != (W[left] == W[right])
    ]
    equal_pairs = [
        (left, right) for left in ids for right in ids if matrix[left][right]
    ]
    operation = []
    first_pole = next(iter(E))
    for left, left_prime in equal_pairs:
        for right, right_prime in equal_pairs:
            product = table[W[left]][W[right]]
            product_prime = table[W[left_prime]][W[right_prime]]
            if not matrix[E[first_pole][product]][E[first_pole][product_prime]]:
                operation.append([[left, left_prime], [right, right_prime]])
    j_failures = [
        occurrence
        for occurrence in ids
        if J[J[occurrence]] != occurrence or W[J[occurrence]] != W[occurrence]
    ]
    c_idempotence_failures = [
        occurrence
        for occurrence in ids
        if C[C[occurrence]] != C[occurrence]
    ]
    c_return_failures = [
        occurrence
        for occurrence in ids
        if W[C[occurrence]] != W[occurrence]
    ]
    failures = {
        "setoid": len(reflexivity) + len(symmetry) + len(transitivity),
        "returning": len(returning),
        "grounded": len(grounded),
        "quotient_recovery": len(quotient),
        "operation_congruence": len(operation),
        "J_involution": len(j_failures),
        "C_idempotence": len(c_idempotence_failures),
        "C_return_preservation": len(c_return_failures),
    }
    return {
        "evaluated_under_own_frozen_equality": True,
        "group_certificate_passed": certificate["passed"],
        "cases": {
            "setoid_reflexivity": len(ids),
            "setoid_symmetry": len(ids) ** 2,
            "setoid_transitivity": len(ids) ** 3,
            "returning": len(ids),
            "grounded": len(basis) ** 2,
            "quotient_recovery": len(ids) ** 2,
            "operation_congruence": len(equal_pairs) ** 2,
            "J": len(ids),
            "C_idempotence": len(ids),
            "C_return_preservation": len(ids),
        },
        "failure_counts": failures,
        "failure_count": sum(failures.values()),
        "passed": certificate["passed"] and not any(failures.values()),
    }


def generate_local_artifact(
    objective_path: Path, context_path: Path
) -> dict[str, Any]:
    objective = load_json(objective_path)
    context = load_json(context_path)
    role = context["agent_role"]
    family = context["construction_family"]
    if family == "generated_permutation_groups" and role == "A":
        model, search = _search_permutation_model(objective, context)
    elif family == "affine_groups_over_prime_fields" and role == "B":
        model, search = _search_affine_model(objective, context)
    else:
        raise ValueError("generator context does not match an isolated role implementation")

    table = model["table"]
    certificate = group_certificate(table)
    if not certificate["passed"]:
        raise RuntimeError(f"agent {role} generated an invalid local group")
    basis = tuple(sorted(table))
    poles = tuple(context["pole_labels"])
    if len(poles) != POLE_COUNT or len(set(poles)) != POLE_COUNT:
        raise ValueError("each local geometry requires two distinct poles")

    occurrences: list[dict[str, Any]] = []
    signatures: dict[str, list[str]] = {}
    W: dict[str, str] = {}
    E: dict[str, dict[str, str]] = {pole: {} for pole in poles}
    for basis_value in basis:
        signature = [table[basis_value][probe] for probe in basis]
        for pole in poles:
            occurrence_id = f"{role}/{pole}::{basis_value}"
            occurrences.append(
                {
                    "occurrence_id": occurrence_id,
                    "pole": pole,
                    "returned_identity": basis_value,
                    "right_action_signature": signature,
                }
            )
            signatures[occurrence_id] = signature
            W[occurrence_id] = basis_value
            E[pole][basis_value] = occurrence_id
    occurrences.sort(key=lambda item: item["occurrence_id"])
    ids = tuple(sorted(signatures))
    matrix = {
        left: {
            right: signatures[left] == signatures[right]
            for right in ids
        }
        for left in ids
    }
    equivalence_classes, class_of = _classes(role, signatures)
    assumption = {
        "rule": objective["local_axiom_geometry_contract"]["admitted_equality_rule"],
        "poles": list(poles),
        "curvature_representative_pole": context["curvature_representative_pole"],
        "carrier": "two independently named occurrence presentations per local identity",
        "status": "ASSUMED_THEN_EXHAUSTIVELY_AUDITED_LOCALLY",
    }
    assumption_id = digest_value(
        {
            "role": role,
            "objective_content_id": digest_value(objective),
            "context_content_id": digest_value(context),
            "assumption": assumption,
        }
    )
    frame_id = digest_value(
        {
            "assumption_id": assumption_id,
            "matrix_sha256": digest_value(matrix),
            "occurrences": ids,
        }
    )
    other_pole = {poles[0]: poles[1], poles[1]: poles[0]}
    J = {
        item["occurrence_id"]: E[other_pole[item["pole"]]][item["returned_identity"]]
        for item in occurrences
    }
    identity = certificate["identity"]
    curvature_pole = context["curvature_representative_pole"]
    if curvature_pole not in poles:
        raise ValueError("curvature representative pole is not one of the local poles")
    C = {
        item["occurrence_id"]: E[curvature_pole][item["returned_identity"]]
        for item in occurrences
    }
    audit = _local_audit(table, certificate, occurrences, W, E, J, C, matrix)
    questions = _evaluate_questions(
        objective,
        frame_id,
        assumption_id,
        occurrences,
        matrix,
        class_of,
        table,
        certificate,
    )
    solutions = sorted(value for value in basis if table[value][value] == identity)
    solution_audit = {
        "problem_id": objective["local_solution_problem"]["id"],
        "solutions": solutions,
        "exhaustive_cases": len(basis),
        "all_listed_satisfy": all(table[value][value] == identity for value in solutions),
        "all_solutions_listed": all(
            (table[value][value] == identity) == (value in solutions) for value in basis
        ),
    }
    artifact: dict[str, Any] = {
        "schema_version": 1,
        "runtime_id": "isolated-generative-local-axiom-geometry",
        "agent_role": role,
        "claim_boundary": "deterministic constrained model search in one subprocess",
        "objective_content_id": digest_value(objective),
        "objective_file_sha256": file_digest(objective_path),
        "context_content_id": digest_value(context),
        "context_file_sha256": file_digest(context_path),
        "visible_inputs": [objective_path.name, context_path.name],
        "other_agent_artifact_visible": False,
        "verifier_protocol_visible": False,
        "construction_family": family,
        "search_trace": search,
        "selected_parameter": model["parameter"],
        "local_encodings": model["encodings"],
        "basis": list(basis),
        "operation_table": table,
        "group_certificate": certificate,
        "local_generators": {"r": model["r"], "s": model["s"]},
        "axiom_geometry_assumption": assumption,
        "axiom_geometry_assumption_id": assumption_id,
        "frame_id": frame_id,
        "occurrences": occurrences,
        "W": dict(sorted(W.items())),
        "E": {pole: dict(sorted(values.items())) for pole, values in E.items()},
        "J": dict(sorted(J.items())),
        "C": dict(sorted(C.items())),
        "admitted_equality": {
            "matrix": matrix,
            "matrix_sha256": digest_value(matrix),
            "equivalence_classes": equivalence_classes,
            "class_of": class_of,
        },
        "internal_unified_evaluation": audit,
        "question_relations": questions,
        "solution_artifact": solution_audit,
    }
    artifact["artifact_content_id"] = _payload_digest(artifact)
    return artifact


def _artifact_occurrences(artifact: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {item["occurrence_id"]: item for item in artifact["occurrences"]}


def _replay_local_artifact(
    objective: dict[str, Any], artifact: dict[str, Any]
) -> dict[str, Any]:
    table = artifact["operation_table"]
    certificate = group_certificate(table)
    occurrences = artifact["occurrences"]
    ids = tuple(sorted(item["occurrence_id"] for item in occurrences))
    occurrence_by_id = _artifact_occurrences(artifact)
    recomputed_signatures = {
        occurrence_id: [
            table[artifact["W"][occurrence_id]][probe] for probe in sorted(table)
        ]
        for occurrence_id in ids
    }
    expected_matrix = {
        left: {
            right: recomputed_signatures[left] == recomputed_signatures[right]
            for right in ids
        }
        for left in ids
    }
    matrix_matches = expected_matrix == artifact["admitted_equality"]["matrix"]
    operation_payload_matches = certificate == artifact["group_certificate"]
    W_matches = all(
        artifact["W"].get(occurrence_id)
        == occurrence_by_id[occurrence_id]["returned_identity"]
        for occurrence_id in ids
    )
    audit = _local_audit(
        table,
        certificate,
        occurrences,
        artifact["W"],
        artifact["E"],
        artifact["J"],
        artifact["C"],
        expected_matrix,
    )
    question_replay = _evaluate_questions(
        objective,
        artifact["frame_id"],
        artifact["axiom_geometry_assumption_id"],
        occurrences,
        expected_matrix,
        artifact["admitted_equality"]["class_of"],
        table,
        certificate,
    )
    questions_match = question_replay == artifact["question_relations"]
    identity = certificate["identity"]
    solution = sorted(value for value in table if table[value][value] == identity)
    solutions_match = solution == artifact["solution_artifact"]["solutions"]
    content_id_matches = _payload_digest(artifact) == artifact["artifact_content_id"]
    return {
        "artifact_content_id_matches": content_id_matches,
        "operation_payload_matches": operation_payload_matches,
        "equality_recomputed_from_local_rule": matrix_matches,
        "W_matches_occurrence_payload": W_matches,
        "local_axiom_geometry_audit": audit,
        "questions_replayed_exactly": questions_match,
        "solutions_replayed_exactly": solutions_match,
        "passed": (
            content_id_matches
            and operation_payload_matches
            and matrix_matches
            and W_matches
            and audit["passed"]
            and questions_match
            and solutions_match
        ),
    }


def _pole_map(source: dict[str, Any], target: dict[str, Any], pi: str | None) -> dict[str, str]:
    source_poles = list(source["axiom_geometry_assumption"]["poles"])
    target_poles = list(target["axiom_geometry_assumption"]["poles"])
    if pi == "preserved":
        return dict(zip(source_poles, target_poles))
    if pi == "reversed":
        return dict(zip(source_poles, reversed(target_poles)))
    return {}


def _induced_T(
    source: dict[str, Any],
    target: dict[str, Any],
    phi: dict[str, str],
    pi: str | None,
) -> dict[str, str]:
    target_lookup = {
        (item["pole"], item["returned_identity"]): item["occurrence_id"]
        for item in target["occurrences"]
    }
    poles = _pole_map(source, target, pi)
    result: dict[str, str] = {}
    for item in source["occurrences"]:
        basis = item["returned_identity"]
        if basis not in phi or item["pole"] not in poles:
            continue
        key = (poles[item["pole"]], phi[basis])
        if key in target_lookup:
            result[item["occurrence_id"]] = target_lookup[key]
    return dict(sorted(result.items()))


def _evaluate_translation_candidate(
    source: dict[str, Any],
    target: dict[str, Any],
    phi: dict[str, str],
    pi: str | None,
    supplied_T: dict[str, str] | None = None,
    pending_if_partial: bool = False,
) -> dict[str, Any]:
    source_basis = tuple(sorted(source["basis"]))
    target_basis = tuple(sorted(target["basis"]))
    source_occurrences = _artifact_occurrences(source)
    target_occurrences = _artifact_occurrences(target)
    T = _induced_T(source, target, phi, pi) if supplied_T is None else dict(supplied_T)
    expected_T = _induced_T(source, target, phi, pi)
    phi_total = set(phi) == set(source_basis) and all(
        value in target_basis for value in phi.values()
    )
    phi_bijective = phi_total and set(phi.values()) == set(target_basis)
    pi_valid = pi in {"preserved", "reversed"}
    T_total = set(T) == set(source_occurrences) and all(
        value in target_occurrences for value in T.values()
    )
    T_bijective = T_total and set(T.values()) == set(target_occurrences)
    tuple_coherent = pi_valid and T == expected_T

    source_matrix = source["admitted_equality"]["matrix"]
    target_matrix = target["admitted_equality"]["matrix"]
    preservation: list[Failure] = []
    reflection: list[Failure] = []
    if T_total:
        for left in sorted(source_occurrences):
            for right in sorted(source_occurrences):
                source_equal = source_matrix[left][right]
                target_equal = target_matrix[T[left]][T[right]]
                if source_equal and not target_equal:
                    preservation.append(
                        Failure("equality_preservation", [left, right], True, False)
                    )
                if target_equal and not source_equal:
                    reflection.append(
                        Failure("equality_reflection", [left, right], True, False)
                    )
    geom_equiv = (
        phi_total
        and phi_bijective
        and T_total
        and T_bijective
        and pi_valid
        and tuple_coherent
        and not preservation
        and not reflection
    )

    W_failures: list[Failure] = []
    E_failures: list[Failure] = []
    J_failures: list[Failure] = []
    C_failures: list[Failure] = []
    operation_failures: list[Failure] = []
    if phi_total and T_total:
        for occurrence_id in sorted(source_occurrences):
            expected = phi[source["W"][occurrence_id]]
            observed = target["W"][T[occurrence_id]]
            if observed != expected:
                W_failures.append(Failure("W_naturality", occurrence_id, expected, observed))
    if geom_equiv:
        poles = _pole_map(source, target, pi)
        for pole in source["E"]:
            for basis in source_basis:
                left = T[source["E"][pole][basis]]
                right = target["E"][poles[pole]][phi[basis]]
                if left != right:
                    E_failures.append(
                        Failure("E_naturality", [pole, basis], right, left)
                    )
        for occurrence_id in sorted(source_occurrences):
            left_j = T[source["J"][occurrence_id]]
            right_j = target["J"][T[occurrence_id]]
            if left_j != right_j:
                J_failures.append(Failure("J_naturality", occurrence_id, right_j, left_j))
            left_c = T[source["C"][occurrence_id]]
            right_c = target["C"][T[occurrence_id]]
            if left_c != right_c:
                C_failures.append(Failure("C_naturality", occurrence_id, right_c, left_c))
        source_table = source["operation_table"]
        target_table = target["operation_table"]
        for left in source_basis:
            for right in source_basis:
                expected = phi[source_table[left][right]]
                observed = target_table[phi[left]][phi[right]]
                if observed != expected:
                    operation_failures.append(
                        Failure("operation_naturality", [left, right], expected, observed)
                    )

    naturality = (
        geom_equiv
        and not W_failures
        and not E_failures
        and not J_failures
        and not C_failures
        and not operation_failures
    )
    incomplete = not phi_total or not T_total
    if pending_if_partial and incomplete:
        status = "PENDING_COMPARISON"
    elif not pi_valid:
        status = "SCHEMA_OBSTRUCTION"
    elif not tuple_coherent:
        status = "NATURALITY_OBSTRUCTION"
    elif not geom_equiv:
        status = "EQUALITY_OBSTRUCTION"
    elif not naturality:
        status = "NATURALITY_OBSTRUCTION"
    else:
        status = "ADMITTED_NATURAL_TRANSLATION"
    first_failure: object = None
    if not pi_valid:
        first_failure = {"check": "pi_required", "observed": pi}
    elif not tuple_coherent:
        first_failure = {"check": "T_phi_pi_coherence", "expected_sha256": digest_value(expected_T), "observed_sha256": digest_value(T)}
    elif preservation:
        first_failure = asdict(preservation[0])
    elif reflection:
        first_failure = asdict(reflection[0])
    elif W_failures:
        first_failure = asdict(W_failures[0])
    elif E_failures:
        first_failure = asdict(E_failures[0])
    elif J_failures:
        first_failure = asdict(J_failures[0])
    elif C_failures:
        first_failure = asdict(C_failures[0])
    elif operation_failures:
        first_failure = asdict(operation_failures[0])

    candidate_seed = {
        "source_artifact_content_id": source["artifact_content_id"],
        "target_artifact_content_id": target["artifact_content_id"],
        "phi": dict(sorted(phi.items())),
        "pi": pi,
        "T": dict(sorted(T.items())),
    }
    candidate_id = digest_value(candidate_seed)
    return {
        "candidate_id": candidate_id,
        "status": status,
        "source_frame_id": source["frame_id"],
        "target_frame_id": target["frame_id"],
        "translation_tuple_T_phi_pi": {
            "T": dict(sorted(T.items())),
            "phi": dict(sorted(phi.items())),
            "pi": pi,
        },
        "totality_and_bijection": {
            "phi_total": phi_total,
            "phi_bijective": phi_bijective,
            "T_total": T_total,
            "T_bijective": T_bijective,
            "pi_valid": pi_valid,
            "T_phi_pi_coherent": tuple_coherent,
        },
        "geom_equiv": {
            "holds": geom_equiv,
            "preservation_cases": len(source_occurrences) ** 2 if T_total else 0,
            "preservation_failure_count": len(preservation),
            "reflection_cases": len(source_occurrences) ** 2 if T_total else 0,
            "reflection_failure_count": len(reflection),
        },
        "naturality": {
            "holds": naturality,
            "W_cases": len(source_occurrences) if phi_total and T_total else 0,
            "W_failure_count": len(W_failures),
            "E_cases": len(source_basis) * POLE_COUNT if geom_equiv else 0,
            "E_failure_count": len(E_failures),
            "J_cases": len(source_occurrences) if geom_equiv else 0,
            "J_failure_count": len(J_failures),
            "C_cases": len(source_occurrences) if geom_equiv else 0,
            "C_failure_count": len(C_failures),
            "operation_cases": len(source_basis) ** 2 if geom_equiv else 0,
            "operation_failure_count": len(operation_failures),
        },
        "first_obstruction": first_failure,
        "non_admission_is_not_openness": status != "ADMITTED_NATURAL_TRANSLATION",
        "open_in_emitted": False,
    }


def _evaluate_word(artifact: dict[str, Any], word: Sequence[str], mapped: dict[str, str] | None = None) -> str:
    table = artifact["operation_table"]
    current = artifact["group_certificate"]["identity"]
    for symbol in word:
        local = artifact["local_generators"][symbol]
        term = mapped[local] if mapped is not None else local
        current = table[current][term]
    return current


def _transport_questions_and_heldout(
    objective: dict[str, Any],
    verifier_protocol: dict[str, Any],
    source: dict[str, Any],
    target: dict[str, Any],
    certificate: dict[str, Any],
) -> dict[str, Any]:
    tuple_data = certificate["translation_tuple_T_phi_pi"]
    T = tuple_data["T"]
    phi = tuple_data["phi"]
    pi = tuple_data["pi"]
    source_records = {item["question_id"]: item for item in source["question_relations"]}
    target_records = {item["question_id"]: item for item in target["question_relations"]}
    source_occurrences = _artifact_occurrences(source)
    target_occurrences = _artifact_occurrences(target)
    poles = _pole_map(source, target, pi)
    question_records = []
    for question in objective["questions"]:
        question_id = question["id"]
        source_record = source_records[question_id]
        target_record = target_records[question_id]
        value_failures = []
        for source_id, source_item in sorted(source_occurrences.items()):
            target_id = T[source_id]
            source_value = _question_value(
                question_id,
                source_item,
                source["operation_table"],
                source["group_certificate"],
            )
            target_value = _question_value(
                question_id,
                target_occurrences[target_id],
                target["operation_table"],
                target["group_certificate"],
            )
            expected = poles[source_value] if question_id == "literal_pole" else source_value
            if target_value != expected:
                value_failures.append([source_id, expected, target_value])
        question_records.append(
            {
                "question_id": question_id,
                "source_frame_id": source["frame_id"],
                "target_frame_id": target["frame_id"],
                "source_resolved": source_record["resolved_in_frame"],
                "target_resolved": target_record["resolved_in_frame"],
                "source_open": source_record["open_in_frame"],
                "target_open": target_record["open_in_frame"],
                "status_transport_agrees": (
                    source_record["resolved_in_frame"] == target_record["resolved_in_frame"]
                    and source_record["open_in_frame"] == target_record["open_in_frame"]
                ),
                "value_transport_cases": len(source_occurrences),
                "value_transport_failure_count": len(value_failures),
                "first_failure": value_failures[0] if value_failures else None,
                "source_open_witness": source_record["open_witness"],
                "target_open_witness": target_record["open_witness"],
                "translational_form_id": certificate["candidate_id"],
            }
        )

    heldout = verifier_protocol["held_out_transfer"]
    word = heldout["word"]
    source_result = _evaluate_word(source, word)
    target_table = target["operation_table"]
    target_result = target["group_certificate"]["identity"]
    for symbol in word:
        mapped_generator = phi[source["local_generators"][symbol]]
        target_result = target_table[target_result][mapped_generator]
    word_transfer = phi[source_result] == target_result
    source_solutions = set(source["solution_artifact"]["solutions"])
    target_solutions = set(target["solution_artifact"]["solutions"])
    mapped_solutions = {phi[value] for value in source_solutions}
    solution_transfer = mapped_solutions == target_solutions
    return {
        "question_transport": question_records,
        "all_question_statuses_and_values_transport": all(
            item["status_transport_agrees"]
            and item["value_transport_failure_count"] == 0
            for item in question_records
        ),
        "held_out_transfer": {
            "word_sha256": digest_value(word),
            "word_length": len(word),
            "source_result": source_result,
            "target_result": target_result,
            "phi_source_result": phi[source_result],
            "word_transfer_holds": word_transfer,
            "solution_problem_id": heldout["solution_problem_id"],
            "mapped_source_solution_count": len(mapped_solutions),
            "target_solution_count": len(target_solutions),
            "solution_transfer_holds": solution_transfer,
        },
        "passed": (
            all(
                item["status_transport_agrees"]
                and item["value_transport_failure_count"] == 0
                for item in question_records
            )
            and word_transfer
            and solution_transfer
        ),
    }


def _d4_table() -> dict[str, dict[str, str]]:
    values = tuple((rotation, flip) for rotation in range(4) for flip in (0, 1))
    labels = {value: f"d{index}" for index, value in enumerate(values)}

    def multiply(left: tuple[int, int], right: tuple[int, int]) -> tuple[int, int]:
        rotation, flip = left
        other_rotation, other_flip = right
        sign = -1 if flip else 1
        return ((rotation + sign * other_rotation) % 4, flip ^ other_flip)

    return {
        labels[left]: {labels[right]: labels[multiply(left, right)] for right in values}
        for left in values
    }


def _q8_table() -> dict[str, dict[str, str]]:
    values = tuple((sign, unit) for unit in range(4) for sign in (1, -1))
    labels = {value: f"q{index}" for index, value in enumerate(values)}
    cyclic = {(1, 2): 3, (2, 3): 1, (3, 1): 2}

    def multiply(left: tuple[int, int], right: tuple[int, int]) -> tuple[int, int]:
        left_sign, left_unit = left
        right_sign, right_unit = right
        sign = left_sign * right_sign
        if left_unit == 0:
            return (sign, right_unit)
        if right_unit == 0:
            return (sign, left_unit)
        if left_unit == right_unit:
            return (-sign, 0)
        if (left_unit, right_unit) in cyclic:
            return (sign, cyclic[(left_unit, right_unit)])
        return (-sign, cyclic[(right_unit, left_unit)])

    return {
        labels[left]: {labels[right]: labels[multiply(left, right)] for right in values}
        for left in values
    }


def _free_choice_contrast() -> dict[str, Any]:
    d4 = _d4_table()
    q8 = _q8_table()
    d4_cert = group_certificate(d4)
    q8_cert = group_certificate(q8)
    d_basis = tuple(sorted(d4))
    q_basis = tuple(sorted(q8))
    homomorphism_count = 0
    first_failure = None
    first_mapping = None
    basis_bijection_count = 0
    for targets in permutations(d_basis):
        mapping = dict(zip(q_basis, targets))
        basis_bijection_count += 1
        failures = []
        for left in q_basis:
            for right in q_basis:
                expected = mapping[q8[left][right]]
                observed = d4[mapping[left]][mapping[right]]
                if observed != expected:
                    failures.append([left, right, expected, observed])
                    break
            if failures:
                break
        if not failures:
            homomorphism_count += 1
        elif first_failure is None:
            first_failure = failures[0]
            first_mapping = dict(sorted(mapping.items()))
    if first_mapping is None:
        raise RuntimeError("D4/Q8 control unexpectedly had no failing comparison")
    first_T = {
        f"{source}@{pole}": f"{first_mapping[source]}@{pole}"
        for source in q_basis
        for pole in ("pole_0", "pole_1")
    }
    return {
        "control": "D4_Q8_free_choice_contrast",
        "status": "NATURALITY_OBSTRUCTION",
        "D4_local_group_valid": d4_cert["passed"],
        "Q8_local_group_valid": q8_cert["passed"],
        "D4_order_multiset": sorted(d4_cert["orders"].values()),
        "Q8_order_multiset": sorted(q8_cert["orders"].values()),
        "basis_bijection_count": basis_bijection_count,
        "orientation_forms_per_basis_bijection": 2,
        "equality_fibre_geom_equiv_form_count": basis_bijection_count * 2,
        "equality_fibre_count_status": "STRUCTURALLY_DERIVED_NOT_OCCURRENCE_PAIR_ENUMERATED",
        "operation_natural_basis_map_count": homomorphism_count,
        "operation_natural_translation_count": homomorphism_count * 2,
        "first_operation_counterexample": first_failure,
        "explicit_first_control_form": {
            "phi": first_mapping,
            "pi": "preserved",
            "alternate_pi_also_considered": "reversed",
            "T": dict(sorted(first_T.items())),
            "T_rule": "T(q@pole) = phi(q)@pi(pole)",
            "equality_fibre_geom_equiv": "structurally induced by the displayed bijective phi and pi",
            "operation_counterexample": first_failure,
        },
        "local_well_definedness_does_not_imply_natural_translation": True,
        "open_in_emitted": False,
        "obstruction_is_not_openness": True,
    }


def _adversarial_controls(
    objective: dict[str, Any], source: dict[str, Any], target: dict[str, Any], admitted: list[dict[str, Any]]
) -> dict[str, Any]:
    source_basis = tuple(sorted(source["basis"]))
    target_basis = tuple(sorted(target["basis"]))
    identity_target = target["group_certificate"]["identity"]
    valid = admitted[0]["translation_tuple_T_phi_pi"]

    collapse_phi = {value: identity_target for value in source_basis}
    collapse = _evaluate_translation_candidate(source, target, collapse_phi, "preserved")

    twist_phi = None
    for target_values in permutations(target_basis):
        proposal = dict(zip(source_basis, target_values))
        if proposal == valid["phi"]:
            continue
        trial = _evaluate_translation_candidate(source, target, proposal, "preserved")
        if trial["geom_equiv"]["holds"] and trial["naturality"]["operation_failure_count"] > 0:
            twist_phi = proposal
            operation_twist = trial
            break
    if twist_phi is None:
        raise RuntimeError("could not construct operation-twist control")

    half = len(source_basis) // 2
    partial_phi = dict(list(sorted(valid["phi"].items()))[:half])
    partial = _evaluate_translation_candidate(
        source, target, partial_phi, "preserved", pending_if_partial=True
    )
    missing_pi = _evaluate_translation_candidate(
        source, target, valid["phi"], None, supplied_T=valid["T"]
    )

    alternative = next(
        item["translation_tuple_T_phi_pi"]
        for item in admitted
        if item["translation_tuple_T_phi_pi"]["phi"] != valid["phi"]
    )
    mismatch = _evaluate_translation_candidate(
        source,
        target,
        valid["phi"],
        valid["pi"],
        supplied_T=alternative["T"],
    )

    mutated_artifact = json.loads(json.dumps(source))
    mutated_artifact["solution_artifact"]["solutions"] = []
    artifact_hash_control = {
        "control": "artifact_hash_mutation",
        "status": "MANIFEST_REJECTED",
        "stored_artifact_content_id": source["artifact_content_id"],
        "mutated_payload_content_id": _payload_digest(mutated_artifact),
        "hash_mismatch_detected": _payload_digest(mutated_artifact)
        != source["artifact_content_id"],
        "open_in_emitted": False,
    }
    mutated_objective = json.loads(json.dumps(objective))
    mutated_objective["questions"][0]["definition"] += " after disclosure"
    question_hash_control = {
        "control": "question_hash_mutation",
        "status": "MANIFEST_REJECTED",
        "stored_objective_content_id": source["objective_content_id"],
        "mutated_objective_content_id": digest_value(mutated_objective),
        "hash_mismatch_detected": digest_value(mutated_objective)
        != source["objective_content_id"],
        "open_in_emitted": False,
    }
    return {
        "equality_collapse": collapse,
        "operation_twist": operation_twist,
        "partial_comparison": partial,
        "missing_orientation_pi": missing_pi,
        "T_phi_mismatch": mismatch,
        "artifact_hash_mutation": artifact_hash_control,
        "question_hash_mutation": question_hash_control,
        "D4_Q8_free_choice_contrast": _free_choice_contrast(),
    }


def verify_frozen_artifacts(
    objective_path: Path,
    verifier_protocol_path: Path,
    artifact_a_path: Path,
    artifact_b_path: Path,
    manifest_path: Path,
) -> dict[str, Any]:
    objective = load_json(objective_path)
    verifier_protocol = load_json(verifier_protocol_path)
    manifest = load_json(manifest_path)
    paths = {"agent_a": artifact_a_path, "agent_b": artifact_b_path}
    manifest_failures = [
        role
        for role, path in paths.items()
        if file_digest(path) != manifest["files"][role]["sha256"]
    ]
    if file_digest(objective_path) != manifest["files"]["objective"]["sha256"]:
        manifest_failures.append("objective")
    if file_digest(verifier_protocol_path) != manifest["files"]["verifier_protocol"]["sha256"]:
        manifest_failures.append("verifier_protocol")
    if manifest_failures:
        raise ValueError(f"immutable disclosure manifest mismatch: {manifest_failures}")

    artifact_a = load_json(artifact_a_path)
    artifact_b = load_json(artifact_b_path)
    if artifact_a["agent_role"] != "A" or artifact_b["agent_role"] != "B":
        raise ValueError("verifier received incorrectly assigned generator roles")
    replay_a = _replay_local_artifact(objective, artifact_a)
    replay_b = _replay_local_artifact(objective, artifact_b)

    source_basis = tuple(sorted(artifact_b["basis"]))
    target_basis = tuple(sorted(artifact_a["basis"]))
    enumeration_digest_rows = []
    histogram: Counter[str] = Counter()
    admitted: list[dict[str, Any]] = []
    for target_values in permutations(target_basis):
        phi = dict(zip(source_basis, target_values))
        for pi in ("preserved", "reversed"):
            certificate = _evaluate_translation_candidate(
                artifact_b, artifact_a, phi, pi
            )
            histogram[certificate["status"]] += 1
            enumeration_digest_rows.append(
                {
                    "candidate_id": certificate["candidate_id"],
                    "status": certificate["status"],
                    "first_obstruction": certificate["first_obstruction"],
                }
            )
            if certificate["status"] == "ADMITTED_NATURAL_TRANSLATION":
                admitted.append(certificate)
    for certificate in admitted:
        certificate["downstream_transport"] = _transport_questions_and_heldout(
            objective,
            verifier_protocol,
            artifact_b,
            artifact_a,
            certificate,
        )

    controls = _adversarial_controls(objective, artifact_b, artifact_a, admitted)
    literal_a = next(
        item for item in artifact_a["question_relations"] if item["question_id"] == "literal_pole"
    )
    literal_b = next(
        item for item in artifact_b["question_relations"] if item["question_id"] == "literal_pole"
    )
    every_natural_transport = all(
        item["downstream_transport"]["passed"] for item in admitted
    )
    admitted_phi_ids = sorted(
        {
            digest_value(item["translation_tuple_T_phi_pi"]["phi"])
            for item in admitted
        }
    )
    interpretations = {
        "classical_well_defined_isolation": {
            "status": "BOTH_LOCALLY_WELL_DEFINED",
            "agent_a_local_replay_passed": replay_a["passed"],
            "agent_b_local_replay_passed": replay_b["passed"],
            "cross_frame_identity_asserted_by_local_checks": False,
        },
        "translational_open_isolation": {
            "status": "OPEN_IN_BOTH_FRAMES_AND_TRANSLATION_INVARIANT",
            "question_id": "literal_pole",
            "agent_a_frame_id": artifact_a["frame_id"],
            "agent_b_frame_id": artifact_b["frame_id"],
            "agent_a_open_witness": literal_a["open_witness"],
            "agent_b_open_witness": literal_b["open_witness"],
            "every_admitted_translation_preserves_open_status": all(
                next(
                    question
                    for question in item["downstream_transport"]["question_transport"]
                    if question["question_id"] == "literal_pole"
                )["status_transport_agrees"]
                for item in admitted
            ),
            "missing_or_rejected_comparison_called_open": False,
        },
        "natural_existential_conditional": {
            "status": (
                "CONDITIONALLY_WITNESSED"
                if admitted
                else "CONDITION_NOT_WITNESSED"
            ),
            "conditions": [
                "both frozen local geometry replays pass",
                "candidate enumeration starts only after disclosure",
                "at least one complete T-phi-pi form passes every equality and naturality check",
            ],
            "natural_translation_form_count": len(admitted),
            "existence_witness_ids": [item["candidate_id"] for item in admitted],
            "unique_translation_claimed": False,
            "canonical_translation_selected": False,
        },
    }
    controls_ok = (
        controls["equality_collapse"]["status"] == "EQUALITY_OBSTRUCTION"
        and controls["equality_collapse"]["geom_equiv"]["reflection_failure_count"] > 0
        and controls["operation_twist"]["status"] == "NATURALITY_OBSTRUCTION"
        and controls["operation_twist"]["geom_equiv"]["holds"]
        and controls["partial_comparison"]["status"] == "PENDING_COMPARISON"
        and controls["missing_orientation_pi"]["status"] == "SCHEMA_OBSTRUCTION"
        and controls["T_phi_mismatch"]["status"] == "NATURALITY_OBSTRUCTION"
        and controls["artifact_hash_mutation"]["hash_mismatch_detected"]
        and controls["question_hash_mutation"]["hash_mismatch_detected"]
        and controls["D4_Q8_free_choice_contrast"]["operation_natural_translation_count"] == 0
    )
    passed = (
        replay_a["passed"]
        and replay_b["passed"]
        and len(admitted) > 0
        and every_natural_transport
        and controls_ok
        and literal_a["open_witness"] is not None
        and literal_b["open_witness"] is not None
    )
    return {
        "schema_version": 1,
        "runtime_id": "post-freeze-generative-axiom-geometry-verifier",
        "claim_boundary": "bounded exhaustive verifier subprocess; not actual ASI",
        "status": "PASS" if passed else "FAIL",
        "verifier_started_after_both_artifacts_frozen": True,
        "immutable_manifest_sha256": file_digest(manifest_path),
        "manifest_validation": {
            "checked_roles": sorted(paths),
            "failure_count": len(manifest_failures),
            "passed": not manifest_failures,
        },
        "local_geometry_replay": {"A": replay_a, "B": replay_b},
        "strong_classical_post_disclosure_baseline": {
            "ordinary_group_isomorphism_count": len(admitted_phi_ids),
            "ordinary_group_isomorphism_phi_ids": admitted_phi_ids,
            "orientation_pi_ignored_for_classical_count": True,
            "accepts_every_operation_preserving_phi": True,
        },
        "candidate_enumeration": {
            "basis_bijection_count": math.factorial(len(source_basis)),
            "orientation_maps_per_bijection": 2,
            "raw_T_phi_pi_count": len(enumeration_digest_rows),
            "candidate_search_inputs": [
                "immutable basis carriers",
                "immutable occurrence fibres",
                "frozen equality matrices",
            ],
            "questions_or_held_out_used_during_enumeration": False,
            "status_histogram": dict(sorted(histogram.items())),
            "enumeration_receipt_sha256": digest_value(enumeration_digest_rows),
        },
        "admitted_natural_translations": admitted,
        "admitted_natural_translation_count": len(admitted),
        "all_admitted_forms_have_explicit_T_phi_pi": all(
            item["totality_and_bijection"]["T_phi_pi_coherent"] for item in admitted
        ),
        "all_admitted_forms_pass_downstream_transfer": every_natural_transport,
        "comparison_interpretations": interpretations,
        "adversarial_controls": controls,
        "failure_partial_or_unselected_called_open": False,
        "tokens_issued": 0,
    }


def _declares_nonfinite_occurrence_domain(artifact: dict[str, Any]) -> tuple[bool, str | None]:
    """Recognize an explicit free-word/infinite domain without redefining it."""

    domain_fields = {
        key: value
        for key, value in artifact.items()
        if "occurrence" in key.lower()
        or key.lower() in {"domain", "carrier_of_occurrences", "word_domain", "w"}
    }
    declaration = canonical_json(domain_fields).lower()
    markers = (
        "free-word",
        "free word",
        "free_monoid",
        "free monoid",
        "all finite words",
        "all finite json arrays",
        "infinite",
    )
    marker = next((value for value in markers if value in declaration), None)
    return marker is not None, marker


def _raw_local_assay(path: Path) -> tuple[dict[str, Any], dict[str, Any]]:
    artifact = load_json(path)
    carrier = artifact.get("carrier")
    table_payload = artifact.get("operation_table")
    table = table_payload
    if isinstance(table_payload, dict) and isinstance(
        table_payload.get("column_order"), list
    ):
        columns = [str(value) for value in table_payload["column_order"]]
        rows = table_payload.get("rows")
        if isinstance(rows, dict) and all(isinstance(row, list) for row in rows.values()):
            table = {
                str(label): dict(zip(columns, row)) for label, row in rows.items()
            }
        elif isinstance(rows, list) and all(isinstance(row, list) for row in rows):
            row_order = table_payload.get("row_order", carrier)
            if isinstance(row_order, list) and len(row_order) == len(rows):
                table = {
                    str(label): dict(zip(columns, row))
                    for label, row in zip(row_order, rows)
                }
    elif isinstance(table_payload, dict) and isinstance(table_payload.get("rows"), dict):
        table = table_payload["rows"]
    if not isinstance(carrier, list) or not isinstance(table, dict):
        return artifact, {
            "source_sha256": file_digest(path),
            "local_group_kernel_status": "UNSUPPORTED_LOCAL_GROUP_SCHEMA",
            "local_group_mathematics_refuted": False,
            "registered_finite_reference_frame_interface": False,
            "reference_frame_interface_status": "OUTSIDE_REGISTERED_FINITE_REFERENCE_FRAME_INTERFACE",
            "registered_trans_frame_interface": False,
            "trans_frame_interface_status": "OUTSIDE_REGISTERED_TRANS_FRAME_INTERFACE",
            "reason": "carrier or total operation_table is absent from the registered assay schema",
            "open_in_emitted": False,
        }
    carrier_set = set(str(value) for value in carrier)
    table_shape = (
        set(table) == carrier_set
        and all(
            isinstance(table.get(left), dict)
            and set(table[left]) == carrier_set
            and all(value in carrier_set for value in table[left].values())
            for left in carrier_set
        )
    )
    certificate = group_certificate(table) if table_shape else None
    nonfinite, marker = _declares_nonfinite_occurrence_domain(artifact)
    occurrences = artifact.get("occurrences")
    W_payload = artifact.get("W")
    E_payload = artifact.get("E")
    J_payload = artifact.get("J")
    C_payload = artifact.get("C")
    W = W_payload.get("table") if isinstance(W_payload, dict) and isinstance(W_payload.get("table"), dict) else W_payload
    E = E_payload.get("table") if isinstance(E_payload, dict) and isinstance(E_payload.get("table"), dict) else E_payload
    J = J_payload.get("table") if isinstance(J_payload, dict) and isinstance(J_payload.get("table"), dict) else J_payload
    C = C_payload.get("table") if isinstance(C_payload, dict) and isinstance(C_payload.get("table"), dict) else C_payload
    finite_occurrence_ids: list[str] = []
    finite_occurrence_shape = False
    if isinstance(occurrences, list) and all(
        isinstance(item, (str, dict)) for item in occurrences
    ):
        finite_occurrence_ids = [
            str(item.get("occurrence_id")) if isinstance(item, dict) else item
            for item in occurrences
        ]
        finite_occurrence_shape = (
            len(finite_occurrence_ids) == 2 * len(carrier_set)
            and len(set(finite_occurrence_ids)) == len(finite_occurrence_ids)
        )
    occurrence_set = set(finite_occurrence_ids)
    equality_payload = artifact.get("admitted_equality")
    if not isinstance(equality_payload, dict):
        equality_payload = artifact.get("admitted_equality_definition")
    classes = None
    if isinstance(equality_payload, dict):
        classes = equality_payload.get("exhaustive_equivalence_classes")
        if classes is None:
            classes = equality_payload.get("equivalence_classes")
    equality_partition_valid = (
        isinstance(classes, list)
        and all(isinstance(eq_class, list) and eq_class for eq_class in classes)
        and len([member for eq_class in classes for member in eq_class])
        == len(occurrence_set)
        and set(member for eq_class in classes for member in eq_class) == occurrence_set
        and len([member for eq_class in classes for member in eq_class])
        == len(set(member for eq_class in classes for member in eq_class))
    )
    reference_registered = (
        finite_occurrence_shape and equality_partition_valid and not nonfinite
    )

    W_valid = (
        isinstance(W, dict)
        and set(W) == occurrence_set
        and all(value in carrier_set for value in W.values())
    )
    E_failures = []
    if isinstance(E, dict) and len(E) == 2 and W_valid:
        for pole, section in E.items():
            if not isinstance(section, dict) or set(section) != carrier_set:
                E_failures.append([pole, "section_keys_are_not_the_carrier"])
                continue
            for basis, occurrence_id in section.items():
                if occurrence_id not in occurrence_set or W[occurrence_id] != basis:
                    E_failures.append([pole, basis, occurrence_id])
    else:
        E_failures.append("E_is_not_two_total_sections")
    J_failures = []
    if isinstance(J, dict) and set(J) == occurrence_set and W_valid:
        for occurrence_id in finite_occurrence_ids:
            target = J[occurrence_id]
            if (
                target not in occurrence_set
                or J.get(target) != occurrence_id
                or W.get(target) != W[occurrence_id]
            ):
                J_failures.append(occurrence_id)
    else:
        J_failures.append("J_is_not_total")
    C_failures = []
    if isinstance(C, dict) and set(C) == occurrence_set and W_valid:
        for occurrence_id in finite_occurrence_ids:
            target = C[occurrence_id]
            if (
                target not in occurrence_set
                or C.get(target) != target
                or W.get(target) != W[occurrence_id]
            ):
                C_failures.append(occurrence_id)
    else:
        C_failures.append("C_is_not_total")
    trans_frame_registered = (
        reference_registered
        and W_valid
        and not E_failures
        and not J_failures
        and not C_failures
    )
    if nonfinite:
        reason = (
            f"artifact explicitly declares a non-finite/free-word occurrence domain ({marker}); "
            "listed sample occurrences are not substituted for that domain"
        )
    elif not finite_occurrence_shape:
        reason = "occurrences do not instantiate the registered finite two-presentation carrier"
    elif not equality_partition_valid:
        reason = "admitted equality is not an explicit exhaustive partition of the finite occurrences"
    else:
        reason = None
    return artifact, {
        "source_sha256": file_digest(path),
        "carrier_size": len(carrier_set),
        "operation_table_shape_valid": table_shape,
        "local_group_kernel_status": (
            "UNSUPPORTED_LOCAL_GROUP_TABLE_SCHEMA"
            if not table_shape
            else "VALID_FINITE_GROUP"
            if certificate is not None and certificate["passed"]
            else "LOCAL_GROUP_COUNTEREXAMPLE"
        ),
        "local_group_certificate": certificate,
        "local_group_mathematics_refuted": False,
        "declares_nonfinite_occurrence_domain": nonfinite,
        "listed_occurrence_count": len(finite_occurrence_ids),
        "finite_occurrence_shape_valid": finite_occurrence_shape,
        "equality_partition_valid": equality_partition_valid,
        "registered_finite_reference_frame_interface": reference_registered,
        "reference_frame_interface_status": (
            "REGISTERED_FINITE_REFERENCE_FRAME_INTERFACE"
            if reference_registered
            else "OUTSIDE_REGISTERED_FINITE_REFERENCE_FRAME_INTERFACE"
        ),
        "reason": reason,
        "trans_frame_law_audit": {
            "W_total_and_carrier_valued": W_valid,
            "E_failure_count": len(E_failures),
            "E_first_failure": E_failures[0] if E_failures else None,
            "J_failure_count": len(J_failures),
            "J_first_failure": J_failures[0] if J_failures else None,
            "C_failure_count": len(C_failures),
            "C_first_failure": C_failures[0] if C_failures else None,
        },
        "registered_trans_frame_interface": trans_frame_registered,
        "trans_frame_interface_status": (
            "REGISTERED_TRANS_FRAME_INTERFACE"
            if trans_frame_registered
            else "OUTSIDE_REGISTERED_TRANS_FRAME_INTERFACE"
        ),
        "open_in_emitted": False,
    }


def run_raw_generation_assay(
    raw_agent_a: Path,
    raw_agent_b: Path,
    output_dir: Path,
    *,
    output_name: str = "raw_generation_assay.json",
    assay_label: str = "optional_raw_generation_interface_assay",
) -> dict[str, Any]:
    """Preserve fresh bytes and classify interface eligibility without normalization."""

    artifact_a, assay_a = _raw_local_assay(raw_agent_a)
    artifact_b, assay_b = _raw_local_assay(raw_agent_b)
    sha_a = file_digest(raw_agent_a)
    sha_b = file_digest(raw_agent_b)
    frozen_a = output_dir / f"raw_agent_a.{sha_a[:16]}.json"
    frozen_b = output_dir / f"raw_agent_b.{sha_b[:16]}.json"
    shutil.copyfile(raw_agent_a, frozen_a)
    shutil.copyfile(raw_agent_b, frozen_b)
    bytes_preserved = (
        frozen_a.read_bytes() == raw_agent_a.read_bytes()
        and frozen_b.read_bytes() == raw_agent_b.read_bytes()
    )
    both_registered = (
        assay_a["registered_finite_reference_frame_interface"]
        and assay_b["registered_finite_reference_frame_interface"]
    )
    cardinality_obstruction = (
        both_registered
        and (
            assay_a["carrier_size"] != assay_b["carrier_size"]
            or assay_a["listed_occurrence_count"] != assay_b["listed_occurrence_count"]
        )
    )
    if cardinality_obstruction:
        comparison_status = "CARDINALITY_GEOM_EQUIV_OBSTRUCTION"
        comparison_reason = (
            "the two frozen finite identity/occurrence carriers have different cardinalities, "
            "so no total bijective GeomEquiv exists in this registered interface"
        )
    elif both_registered:
        comparison_status = "ELIGIBLE_FOR_SEPARATE_TRANSLATOR_SEARCH"
        comparison_reason = None
    else:
        comparison_status = "TRANSLATOR_SEARCH_NOT_RUN_INTERFACE_BOUNDARY"
        comparison_reason = (
            "at least one raw occurrence domain lies outside the registered finite frame interface"
        )
    comparison = {
        "status": comparison_status,
        "reason": comparison_reason,
        "candidate_enumeration_started": False,
        "global_nonexistence_claimed": False,
        "both_registered_trans_frame_interfaces": (
            assay_a["registered_trans_frame_interface"]
            and assay_b["registered_trans_frame_interface"]
        ),
        "naturality_search_started": False,
        "no_geometry_was_normalized_or_replaced": True,
        "outside_interface_is_not_false_mathematics": True,
        "outside_interface_is_not_open_in": True,
        "open_in_emitted": False,
    }
    result = {
        "schema_version": 1,
        "assay": assay_label,
        "status": "ASSAY_COMPLETE",
        "claim_boundary": "hash preservation and registered-interface classification only",
        "raw_artifacts": {
            "A": {
                "preserved_path": frozen_a.name,
                "source_sha256": sha_a,
                "preserved_sha256": file_digest(frozen_a),
                "bytes_preserved": bytes_preserved,
                "declared_local_name": artifact_a.get("local_name"),
                "assay": assay_a,
            },
            "B": {
                "preserved_path": frozen_b.name,
                "source_sha256": sha_b,
                "preserved_sha256": file_digest(frozen_b),
                "bytes_preserved": bytes_preserved,
                "declared_local_name": artifact_b.get("local_name"),
                "assay": assay_b,
            },
        },
        "comparison": comparison,
        "reference_positive_lane_pass_does_not_depend_on_this_assay": True,
    }
    write_json(output_dir / output_name, result)
    return result


def _run_role(arguments: Sequence[str]) -> None:
    completed = subprocess.run(
        [sys.executable, str(Path(__file__).resolve()), *arguments],
        cwd=PROJECT_ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    if completed.returncode != 0:
        raise RuntimeError(
            f"role failed ({completed.returncode}): {' '.join(arguments)}\n"
            f"{completed.stdout}\n{completed.stderr}"
        )


def _launch_generators(
    objective: Path, context_a: Path, context_b: Path, output_a: Path, output_b: Path
) -> None:
    commands = [
        [
            sys.executable,
            str(Path(__file__).resolve()),
            "--role",
            "agent-a",
            "--objective",
            str(objective),
            "--context",
            str(context_a),
            "--output",
            str(output_a),
        ],
        [
            sys.executable,
            str(Path(__file__).resolve()),
            "--role",
            "agent-b",
            "--objective",
            str(objective),
            "--context",
            str(context_b),
            "--output",
            str(output_b),
        ],
    ]
    processes = [
        subprocess.Popen(
            command,
            cwd=PROJECT_ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        for command in commands
    ]
    failures = []
    for index, process in enumerate(processes):
        stdout, stderr = process.communicate()
        if process.returncode != 0:
            failures.append(
                f"generator {index} failed ({process.returncode})\n{stdout}\n{stderr}"
            )
    if failures:
        raise RuntimeError("\n".join(failures))


def run_experiment(
    output_dir: Path = DEFAULT_OUTPUT,
    raw_agent_a: Path | None = None,
    raw_agent_b: Path | None = None,
) -> dict[str, Any]:
    output_dir.mkdir(parents=True, exist_ok=True)
    for old in output_dir.glob("*"):
        if old.is_file():
            old.unlink()

    selected_raw_a = raw_agent_a
    selected_raw_b = raw_agent_b
    if selected_raw_a is None and selected_raw_b is None:
        if RAW_AGENT_A.exists() and RAW_AGENT_B_FINITE.exists():
            selected_raw_a = RAW_AGENT_A
            selected_raw_b = RAW_AGENT_B_FINITE

    chain = ReceiptChain()
    precommit = {
        "objective_sha256": file_digest(OBJECTIVE),
        "objective_content_id": digest_value(load_json(OBJECTIVE)),
        "agent_a_context_sha256": file_digest(CONTEXT_A),
        "agent_b_context_sha256": file_digest(CONTEXT_B),
        "verifier_protocol_sha256": file_digest(VERIFIER_PROTOCOL),
        "cross_language_dictionary_present": False,
        "preselected_translation_present": False,
        "optional_raw_agent_a_sha256": (
            file_digest(selected_raw_a) if selected_raw_a is not None else None
        ),
        "optional_raw_agent_b_sha256": (
            file_digest(selected_raw_b) if selected_raw_b is not None else None
        ),
        "optional_raw_interface_variant_sha256": (
            file_digest(RAW_AGENT_B_INTERFACE_VARIANT)
            if RAW_AGENT_B_INTERFACE_VARIANT.exists()
            else None
        ),
        "raw_artifact_hashes_registered_before_assay_or_comparison": True,
    }
    chain.append("GENERATIVE_PROTOCOLS_PRECOMMITTED", precommit)

    with tempfile.TemporaryDirectory(prefix="generative-axiom-isolation-") as name:
        temporary = Path(name)
        isolated_a = temporary / "agent-a" / "artifact.json"
        isolated_b = temporary / "agent-b" / "artifact.json"
        isolated_a.parent.mkdir(parents=True)
        isolated_b.parent.mkdir(parents=True)
        _launch_generators(OBJECTIVE, CONTEXT_A, CONTEXT_B, isolated_a, isolated_b)
        artifact_a = load_json(isolated_a)
        artifact_b = load_json(isolated_b)
        if artifact_a["other_agent_artifact_visible"] or artifact_b["other_agent_artifact_visible"]:
            raise RuntimeError("a generator reported cross-artifact visibility")
        sha_a = file_digest(isolated_a)
        sha_b = file_digest(isolated_b)
        frozen_a = output_dir / f"agent_a.{sha_a[:16]}.json"
        frozen_b = output_dir / f"agent_b.{sha_b[:16]}.json"
        shutil.copyfile(isolated_a, frozen_a)
        shutil.copyfile(isolated_b, frozen_b)

        chain.append(
            "AGENT_A_LOCAL_GEOMETRY_FROZEN",
            {
                "sha256": sha_a,
                "artifact_content_id": artifact_a["artifact_content_id"],
                "disclosed_to_agent_b": False,
                "verifier_started": False,
            },
        )
        chain.append(
            "AGENT_B_LOCAL_GEOMETRY_FROZEN",
            {
                "sha256": sha_b,
                "artifact_content_id": artifact_b["artifact_content_id"],
                "disclosed_to_agent_a": False,
                "verifier_started": False,
            },
        )
        manifest = {
            "schema_version": 1,
            "causal_boundary": "both generator subprocesses exited before verifier launch",
            "files": {
                "objective": {"path": OBJECTIVE.name, "sha256": file_digest(OBJECTIVE)},
                "verifier_protocol": {
                    "path": VERIFIER_PROTOCOL.name,
                    "sha256": file_digest(VERIFIER_PROTOCOL),
                },
                "agent_a": {
                    "path": frozen_a.name,
                    "sha256": file_digest(frozen_a),
                    "artifact_content_id": artifact_a["artifact_content_id"],
                },
                "agent_b": {
                    "path": frozen_b.name,
                    "sha256": file_digest(frozen_b),
                    "artifact_content_id": artifact_b["artifact_content_id"],
                },
            },
        }
        manifest_path = output_dir / "disclosure_manifest.json"
        write_json(manifest_path, manifest)
        chain.append(
            "BOTH_ARTIFACTS_DISCLOSED_TO_VERIFIER_ONLY_AFTER_FREEZE",
            {
                "manifest_sha256": file_digest(manifest_path),
                "agent_a_sha256": sha_a,
                "agent_b_sha256": sha_b,
            },
        )

        isolated_verifier = temporary / "verifier" / "verification.json"
        isolated_verifier.parent.mkdir(parents=True)
        _run_role(
            [
                "--role",
                "verifier",
                "--objective",
                str(OBJECTIVE),
                "--verifier-protocol",
                str(VERIFIER_PROTOCOL),
                "--artifact-a",
                str(frozen_a),
                "--artifact-b",
                str(frozen_b),
                "--manifest",
                str(manifest_path),
                "--output",
                str(isolated_verifier),
            ]
        )
        verifier_sha = file_digest(isolated_verifier)
        verifier_path = output_dir / f"verifier.{verifier_sha[:16]}.json"
        shutil.copyfile(isolated_verifier, verifier_path)
        verification = load_json(verifier_path)

    post_verifier_hash_revalidation = {
        "agent_a_unchanged": file_digest(frozen_a) == sha_a,
        "agent_b_unchanged": file_digest(frozen_b) == sha_b,
        "manifest_unchanged": file_digest(manifest_path)
        == verification["immutable_manifest_sha256"],
        "verifier_copy_matches_frozen_source": file_digest(verifier_path) == verifier_sha,
    }
    post_verifier_hash_revalidation["passed"] = all(
        post_verifier_hash_revalidation.values()
    )
    if not post_verifier_hash_revalidation["passed"]:
        raise RuntimeError("a frozen artifact changed during post-freeze verification")
    chain.append(
        "POST_FREEZE_VERIFIER_RESULT_FROZEN",
        {
            "sha256": file_digest(verifier_path),
            "status": verification["status"],
            "admitted_natural_translation_count": verification[
                "admitted_natural_translation_count"
            ],
            "tokens_issued": verification["tokens_issued"],
            "post_verifier_hash_revalidation_passed": True,
        },
    )
    raw_assay = None
    if selected_raw_a is not None or selected_raw_b is not None:
        if selected_raw_a is None or selected_raw_b is None:
            raise ValueError("raw generation assay requires both --raw-agent-a and --raw-agent-b")
        raw_assay = run_raw_generation_assay(
            selected_raw_a, selected_raw_b, output_dir
        )
        chain.append(
            "OPTIONAL_RAW_GENERATION_ASSAY_FROZEN",
            {
                "sha256": file_digest(output_dir / "raw_generation_assay.json"),
                "comparison_status": raw_assay["comparison"]["status"],
                "reference_pass_dependency": False,
            },
        )
    raw_interface_variant = None
    if RAW_AGENT_A.exists() and RAW_AGENT_B_INTERFACE_VARIANT.exists():
        raw_interface_variant = run_raw_generation_assay(
            RAW_AGENT_A,
            RAW_AGENT_B_INTERFACE_VARIANT,
            output_dir,
            output_name="raw_generation_interface_variant_assay.json",
            assay_label="optional_raw_nonfinite_interface_variant_assay",
        )
        chain.append(
            "OPTIONAL_RAW_INTERFACE_VARIANT_ASSAY_FROZEN",
            {
                "sha256": file_digest(
                    output_dir / "raw_generation_interface_variant_assay.json"
                ),
                "comparison_status": raw_interface_variant["comparison"]["status"],
                "reference_pass_dependency": False,
            },
        )
    summary = {
        "schema_version": 1,
        "benchmark": "generative-axiom-geometry-isolation-v1",
        "claim_status": "EXECUTED_BOUNDED_GENERATIVE_PROXY",
        "actual_asi_or_aristotle_run": False,
        "independence_claim": (
            "subprocess and causal input separation only; no claim of epistemic, organizational, "
            "or adversarial sandbox independence"
        ),
        "causal_order": [
            "shared objective and distinct generator contexts precommitted",
            "generator A and B launched as separate subprocesses with disjoint arguments",
            "both local axiom geometries, equalities, questions, and solutions frozen",
            "content-addressed disclosure manifest frozen",
            "third verifier subprocess launched afterward",
            "all candidate T-phi-pi forms enumerated",
            "GeomEquiv then W/E/J/C/operation naturality checked",
            "frame-qualified questions and held-out transfer checked",
        ],
        "generator_artifacts": {
            "A": {"path": frozen_a.name, "sha256": file_digest(frozen_a)},
            "B": {"path": frozen_b.name, "sha256": file_digest(frozen_b)},
        },
        "disclosure_manifest": {
            "path": manifest_path.name,
            "sha256": file_digest(manifest_path),
        },
        "verifier_artifact": {
            "path": verifier_path.name,
            "sha256": file_digest(verifier_path),
        },
        "status": verification["status"],
        "comparison_interpretations": verification["comparison_interpretations"],
        "strong_classical_post_disclosure_baseline": verification[
            "strong_classical_post_disclosure_baseline"
        ],
        "admitted_natural_translation_count": verification[
            "admitted_natural_translation_count"
        ],
        "canonical_translation_selected": False,
        "post_verifier_hash_revalidation": post_verifier_hash_revalidation,
        "optional_raw_generation_assay": (
            {
                "status": raw_assay["status"],
                "comparison_status": raw_assay["comparison"]["status"],
                "path": "raw_generation_assay.json",
                "reference_pass_dependency": False,
            }
            if raw_assay is not None
            else {
                "status": "NOT_RUN_INPUTS_ABSENT",
                "reference_pass_dependency": False,
            }
        ),
        "optional_raw_interface_variant_assay": (
            {
                "status": raw_interface_variant["status"],
                "comparison_status": raw_interface_variant["comparison"]["status"],
                "path": "raw_generation_interface_variant_assay.json",
                "reference_pass_dependency": False,
            }
            if raw_interface_variant is not None
            else {
                "status": "NOT_RUN_INPUTS_ABSENT",
                "reference_pass_dependency": False,
            }
        ),
        "tokens_issued": 0,
    }
    chain.append("GENERATIVE_EXPERIMENT_SUMMARY", {"sha256": digest_value(summary)})
    summary["receipt_chain"] = chain.verify()
    write_json(output_dir / "result.json", summary)
    (output_dir / "receipts.jsonl").write_text(
        "".join(canonical_json(item) + "\n" for item in chain.items), encoding="utf-8"
    )
    return summary


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--role", choices=("agent-a", "agent-b", "verifier"))
    parser.add_argument("--objective", type=Path)
    parser.add_argument("--context", type=Path)
    parser.add_argument("--verifier-protocol", type=Path)
    parser.add_argument("--artifact-a", type=Path)
    parser.add_argument("--artifact-b", type=Path)
    parser.add_argument("--manifest", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--raw-agent-a", type=Path)
    parser.add_argument("--raw-agent-b", type=Path)
    parser.add_argument("--assert-reference", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = _parse_args()
    if args.role in {"agent-a", "agent-b"}:
        if not args.objective or not args.context or not args.output:
            raise SystemExit("agent generation requires --objective, --context, and --output")
        artifact = generate_local_artifact(args.objective, args.context)
        expected_role = "A" if args.role == "agent-a" else "B"
        if artifact["agent_role"] != expected_role:
            raise SystemExit(f"{args.role} received the wrong private context")
        write_json(args.output, artifact)
        return 0
    if args.role == "verifier":
        required = (
            args.objective,
            args.verifier_protocol,
            args.artifact_a,
            args.artifact_b,
            args.manifest,
            args.output,
        )
        if any(value is None for value in required):
            raise SystemExit("verify requires objective, protocol, artifacts, manifest, and output")
        result = verify_frozen_artifacts(
            args.objective,
            args.verifier_protocol,
            args.artifact_a,
            args.artifact_b,
            args.manifest,
        )
        write_json(args.output, result)
        return 0

    result = run_experiment(args.output_dir, args.raw_agent_a, args.raw_agent_b)
    print(json.dumps(result, indent=2, sort_keys=True))
    if args.assert_reference:
        passed = (
            result["status"] == "PASS"
            and result["admitted_natural_translation_count"] == 6
            and result["canonical_translation_selected"] is False
            and result["tokens_issued"] == 0
            and result["receipt_chain"]["ok"]
        )
        return 0 if passed else 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
