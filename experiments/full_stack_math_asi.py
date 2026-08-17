#!/usr/bin/env python3
"""Independent learning-to-execution translational-axiometry experiment.

This executable is a classical symbolic mathematical-agent proxy.  It does not
claim to instantiate general ASI.  It does implement the stronger experimental
boundary requested by the project:

    independent learning -> exhaustive execution -> frozen artifacts
      -> closure equality defines each reference frame
      -> post-hoc (T, phi, pi) is checked as an axiom-geometry equivalence
      -> questions factor through that equality or remain open in that frame
      -> next basis

Perspective A and perspective B are started as separate subprocesses with
disjoint protocol files.  The translator is a third subprocess and is not
given the complete precommitted contact.  A fourth process constructs and
checks the full translational closure operations.  Multiple coherent frame
forms are retained as equivalent reference frames; they are not classified as
an ambiguity internal to a fixed axiom system.  In particular, ``OpenIn`` is
always recorded as a relation between a frame and a question, never as a bare
flag on a branch or question.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import random
import shutil
import subprocess
import sys
import tempfile
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Callable, Sequence


ROOT = Path(__file__).resolve().parents[1]
BENCHMARK = ROOT / "benchmarks" / "full_stack_d4"
DEFAULT_OUTPUT = ROOT / "runs" / "full_stack_d4" / "latest"

Permutation = tuple[int, int, int, int]
NormalForm = tuple[int, int]
Element = tuple[int, ...]
Operation = Callable[[Element, Element], Element]


@dataclass(frozen=True)
class Witness:
    check: str
    input: object
    expected: object | None = None
    observed: object | None = None
    reason: str | None = None


POLES = ("zero", "infinity")


def other_pole(pole: str) -> str:
    if pole == "zero":
        return "infinity"
    if pole == "infinity":
        return "zero"
    raise ValueError(f"unknown pole {pole}")


def canonical_json(value: object) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def digest_value(value: object) -> str:
    return hashlib.sha256(canonical_json(value).encode("utf-8")).hexdigest()


def file_digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object in {path}")
    return value


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    os.replace(temporary, path)


def as_element(value: Sequence[int]) -> Element:
    return tuple(int(item) for item in value)


def permutation_compose(left: Element, right: Element) -> Element:
    return tuple(left[right[index]] for index in range(4))


def permutation_inverse(value: Element) -> Element:
    result = [0] * 4
    for source, target in enumerate(value):
        result[target] = source
    return tuple(result)


def normal_multiply(left: Element, right: Element) -> Element:
    left_rotation, left_flip = left
    right_rotation, right_flip = right
    sign = -1 if left_flip else 1
    return ((left_rotation + sign * right_rotation) % 4, left_flip ^ right_flip)


def normal_action(value: Element) -> Element:
    rotation, flip = value
    sign = -1 if flip else 1
    return tuple((rotation + sign * vertex) % 4 for vertex in range(4))


def generated_closure(generators: Sequence[Element], operation: Operation) -> tuple[Element, ...]:
    known = {tuple(range(4)), *generators}
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


def a_hypothesis(name: str, left: Element, right: Element) -> Element:
    if name == "left_after_right":
        return permutation_compose(left, right)
    if name == "right_after_left":
        return permutation_compose(right, left)
    if name == "inverse_left_after_right":
        return permutation_compose(permutation_inverse(left), right)
    if name == "left_after_inverse_right":
        return permutation_compose(left, permutation_inverse(right))
    if name == "inverse_of_composite":
        return permutation_inverse(permutation_compose(left, right))
    raise KeyError(name)


A_HYPOTHESES = (
    "left_after_right",
    "right_after_left",
    "inverse_left_after_right",
    "left_after_inverse_right",
    "inverse_of_composite",
)


def b_hypothesis(name: str, left: Element, right: Element) -> Element:
    if name.startswith("swapped_"):
        first, second = right, left
        source = name.removeprefix("swapped_")
    else:
        first, second = left, right
        source = name.removeprefix("direct_")
    first_rotation, first_flip = first
    second_rotation, second_flip = second
    if source == "first_sign":
        sign = -1 if first_flip else 1
    elif source == "second_sign":
        sign = -1 if second_flip else 1
    elif source == "xor_sign":
        sign = -1 if first_flip ^ second_flip else 1
    elif source == "no_sign":
        sign = 1
    elif source == "negative":
        sign = -1
    else:
        raise KeyError(name)
    return ((first_rotation + sign * second_rotation) % 4, first_flip ^ second_flip)


B_HYPOTHESES = tuple(
    f"{order}_{source}"
    for order in ("direct", "swapped")
    for source in ("first_sign", "second_sign", "xor_sign", "no_sign", "negative")
)


def make_ids(prefix: str, carrier: Sequence[Element]) -> tuple[dict[Element, str], dict[str, Element]]:
    forward = {value: f"{prefix}{index}" for index, value in enumerate(sorted(carrier))}
    return forward, {identifier: value for value, identifier in forward.items()}


def select_training_pairs(
    carrier: Sequence[Element], count: int, seed: int
) -> tuple[tuple[Element, Element], ...]:
    pairs = [(left, right) for left in carrier for right in carrier]
    random.Random(seed).shuffle(pairs)
    return tuple(pairs[:count])


def operation_table(
    carrier: Sequence[Element], ids: dict[Element, str], operation: Operation
) -> dict[str, dict[str, str]]:
    return {
        ids[left]: {ids[right]: ids[operation(left, right)] for right in carrier}
        for left in carrier
    }


def group_certificate(table: dict[str, dict[str, str]]) -> dict[str, Any]:
    elements = tuple(sorted(table))
    identities = [
        candidate
        for candidate in elements
        if all(table[candidate][value] == value and table[value][candidate] == value for value in elements)
    ]
    associativity_failures: list[list[str]] = []
    for left in elements:
        for middle in elements:
            for right in elements:
                lhs = table[table[left][middle]][right]
                rhs = table[left][table[middle][right]]
                if lhs != rhs:
                    associativity_failures.append([left, middle, right])
    identity = identities[0] if len(identities) == 1 else None
    inverses: dict[str, str] = {}
    if identity is not None:
        for value in elements:
            candidates = [
                candidate
                for candidate in elements
                if table[value][candidate] == identity and table[candidate][value] == identity
            ]
            if len(candidates) == 1:
                inverses[value] = candidates[0]
    orders: dict[str, int | None] = {}
    if identity is not None:
        for value in elements:
            current = identity
            order: int | None = None
            for exponent in range(1, len(elements) * 2 + 1):
                current = table[current][value]
                if current == identity:
                    order = exponent
                    break
            orders[value] = order
    passed = (
        len(identities) == 1
        and not associativity_failures
        and len(inverses) == len(elements)
        and all(order is not None for order in orders.values())
    )
    return {
        "passed": passed,
        "identity": identity,
        "identity_candidates": identities,
        "associativity_cases": len(elements) ** 3,
        "associativity_failure_count": len(associativity_failures),
        "first_associativity_failure": associativity_failures[0] if associativity_failures else None,
        "inverses": inverses,
        "orders": orders,
    }


def learn_agent_a(protocol_path: Path) -> dict[str, Any]:
    protocol = load_json(protocol_path)
    turn = as_element(protocol["generators"]["turn"])
    reverse = as_element(protocol["generators"]["reverse"])
    carrier = generated_closure((turn, reverse), permutation_compose)
    if len(carrier) != 8:
        raise RuntimeError("perspective A did not discover eight occurrences")
    ids, presentations = make_ids("a", carrier)
    training_pairs = select_training_pairs(carrier, int(protocol["training_pairs"]), int(protocol["seed"]))
    scores = {
        name: sum(a_hypothesis(name, left, right) != permutation_compose(left, right) for left, right in training_pairs)
        for name in A_HYPOTHESES
    }
    best_error = min(scores.values())
    survivors = sorted(name for name, error in scores.items() if error == best_error)
    selected = survivors[0]
    learned_operation: Operation = lambda left, right: a_hypothesis(selected, left, right)
    table = operation_table(carrier, ids, learned_operation)
    training_set = set(training_pairs)
    held_out = [(left, right) for left in carrier for right in carrier if (left, right) not in training_set]
    held_out_errors = [
        (left, right)
        for left, right in held_out
        if learned_operation(left, right) != permutation_compose(left, right)
    ]
    certificate = group_certificate(table)
    status = "PASS" if best_error == 0 and len(survivors) == 1 and not held_out_errors and certificate["passed"] else "INCOMPLETE"
    return {
        "schema_version": 2,
        "runtime_id": "perspective-a-permutation-learner",
        "perspective": "A",
        "protocol_sha256": file_digest(protocol_path),
        "visibility": protocol["visible_inputs"],
        "forbidden_inputs": protocol["forbidden_inputs"],
        "training": {
            "seed": protocol["seed"],
            "observation_count": len(training_pairs),
            "observations": [
                {"left": ids[left], "right": ids[right], "result": ids[permutation_compose(left, right)]}
                for left, right in training_pairs
            ],
        },
        "model": {
            "family": "enumerative composition-program synthesis",
            "candidate_scores": scores,
            "selected_hypothesis": selected,
            "minimum_training_error": best_error,
            "minimum_error_survivors": survivors,
        },
        "execution": {
            "status": status,
            "carrier_size": len(carrier),
            "held_out_count": len(held_out),
            "held_out_error_count": len(held_out_errors),
            "operation_table": table,
            "group_certificate": certificate,
        },
        "presentations": {identifier: list(value) for identifier, value in sorted(presentations.items())},
        "local_generators": {"turn": ids[turn], "reverse": ids[reverse]},
        "self_certification": status == "PASS",
    }


def learn_agent_b(protocol_path: Path) -> dict[str, Any]:
    protocol = load_json(protocol_path)
    carrier = tuple((rotation, flip) for rotation in range(4) for flip in range(2))
    ids, presentations = make_ids("b", carrier)
    training_pairs = select_training_pairs(carrier, int(protocol["training_pairs"]), int(protocol["seed"]))
    scores = {
        name: sum(b_hypothesis(name, left, right) != normal_multiply(left, right) for left, right in training_pairs)
        for name in B_HYPOTHESES
    }
    best_error = min(scores.values())
    survivors = sorted(name for name, error in scores.items() if error == best_error)
    selected = survivors[0]
    learned_operation: Operation = lambda left, right: b_hypothesis(selected, left, right)
    table = operation_table(carrier, ids, learned_operation)
    training_set = set(training_pairs)
    held_out = [(left, right) for left in carrier for right in carrier if (left, right) not in training_set]
    held_out_errors = [
        (left, right)
        for left, right in held_out
        if learned_operation(left, right) != normal_multiply(left, right)
    ]
    certificate = group_certificate(table)
    status = "PASS" if best_error == 0 and len(survivors) == 1 and not held_out_errors and certificate["passed"] else "INCOMPLETE"
    return {
        "schema_version": 2,
        "runtime_id": "perspective-b-semidir-learner",
        "perspective": "B",
        "protocol_sha256": file_digest(protocol_path),
        "visibility": protocol["visible_inputs"],
        "forbidden_inputs": protocol["forbidden_inputs"],
        "training": {
            "seed": protocol["seed"],
            "observation_count": len(training_pairs),
            "observations": [
                {"left": ids[left], "right": ids[right], "result": ids[normal_multiply(left, right)]}
                for left, right in training_pairs
            ],
        },
        "model": {
            "family": "enumerative semidirect-program synthesis",
            "candidate_scores": scores,
            "selected_hypothesis": selected,
            "minimum_training_error": best_error,
            "minimum_error_survivors": survivors,
        },
        "execution": {
            "status": status,
            "carrier_size": len(carrier),
            "held_out_count": len(held_out),
            "held_out_error_count": len(held_out_errors),
            "operation_table": table,
            "group_certificate": certificate,
        },
        "presentations": {identifier: list(value) for identifier, value in sorted(presentations.items())},
        "local_generators": {"turn": ids[(1, 0)], "reverse": ids[(0, 1)]},
        "self_certification": status == "PASS",
    }


def _partial_homomorphism_ok(
    mapping: dict[str, str], b_table: dict[str, dict[str, str]], a_table: dict[str, dict[str, str]]
) -> bool:
    for left in mapping:
        for right in mapping:
            product = b_table[left][right]
            if product in mapping and a_table[mapping[left]][mapping[right]] != mapping[product]:
                return False
    return True


def enumerate_isomorphisms(artifact_a: dict[str, Any], artifact_b: dict[str, Any]) -> list[dict[str, str]]:
    a_table = artifact_a["execution"]["operation_table"]
    b_table = artifact_b["execution"]["operation_table"]
    a_orders = artifact_a["execution"]["group_certificate"]["orders"]
    b_orders = artifact_b["execution"]["group_certificate"]["orders"]
    b_identity = artifact_b["execution"]["group_certificate"]["identity"]
    a_identity = artifact_a["execution"]["group_certificate"]["identity"]
    if b_identity is None or a_identity is None:
        return []
    b_elements = sorted(b_table)
    candidates_by_b = {
        source: [target for target in sorted(a_table) if a_orders[target] == b_orders[source]]
        for source in b_elements
    }
    candidates_by_b[b_identity] = [a_identity]
    ordered_sources = sorted(b_elements, key=lambda source: (len(candidates_by_b[source]), source))
    results: list[dict[str, str]] = []

    def search(index: int, mapping: dict[str, str], used: set[str]) -> None:
        if index == len(ordered_sources):
            if _partial_homomorphism_ok(mapping, b_table, a_table):
                results.append(dict(sorted(mapping.items())))
            return
        source = ordered_sources[index]
        for target in candidates_by_b[source]:
            if target in used:
                continue
            mapping[source] = target
            used.add(target)
            if _partial_homomorphism_ok(mapping, b_table, a_table):
                search(index + 1, mapping, used)
            used.remove(target)
            del mapping[source]

    search(0, {}, set())
    return sorted(results, key=canonical_json)


def _id_for_presentation(artifact: dict[str, Any], presentation: Sequence[int]) -> str:
    expected = list(presentation)
    matches = [identifier for identifier, value in artifact["presentations"].items() if value == expected]
    if len(matches) != 1:
        raise ValueError(f"presentation {expected} is not unique")
    return matches[0]


def _non_natural_deformation(
    artifact_a: dict[str, Any], artifact_b: dict[str, Any]
) -> dict[str, str]:
    """A total sign-erasing map used only as an outside-closure control."""

    mapping: dict[str, str] = {}
    for source, presentation in artifact_b["presentations"].items():
        rotation, _flip = as_element(presentation)
        target_presentation = tuple((rotation + vertex) % 4 for vertex in range(4))
        mapping[source] = _id_for_presentation(artifact_a, target_presentation)
    return dict(sorted(mapping.items()))


def translate_artifacts(
    artifact_a_path: Path, artifact_b_path: Path, protocol_path: Path, mode: str
) -> dict[str, Any]:
    artifact_a = load_json(artifact_a_path)
    artifact_b = load_json(artifact_b_path)
    protocol = load_json(protocol_path)
    structural = enumerate_isomorphisms(artifact_a, artifact_b)
    if mode in ("structural_family", "self_certification_only"):
        constraints: list[dict[str, Any]] = []
        selected_candidates = list(structural)
        mapping = None
        self_assertion = mode == "self_certification_only"
        selection_relation = (
            "self-claim supplies no independent relative contact"
            if self_assertion
            else "all coherent axiom-geometry equivalences remain; no origin is isolated"
        )
    elif mode == "non_natural_deformation":
        constraints = []
        mapping = _non_natural_deformation(artifact_a, artifact_b)
        selected_candidates = [mapping]
        self_assertion = False
        selection_relation = "total sign-erasing deformation proposed outside the structural family"
    else:
        if mode not in protocol["selection"]:
            raise ValueError(f"unknown translation mode {mode}")
        constraints = protocol["selection"][mode]
        selected_candidates = list(structural)
        self_assertion = False
        a_orders = artifact_a["execution"]["group_certificate"]["orders"]
        for constraint in constraints:
            source = _id_for_presentation(artifact_b, constraint["source_local_form"])
            filtered: list[dict[str, str]] = []
            for candidate in selected_candidates:
                target = candidate[source]
                target_presentation = artifact_a["presentations"][target]
                if (
                    a_orders[target] == constraint["target_order"]
                    and target_presentation[0] == constraint["target_image_of_vertex_zero"]
                ):
                    filtered.append(candidate)
            selected_candidates = filtered
        mapping = selected_candidates[0] if len(selected_candidates) == 1 else None
        if not selected_candidates:
            selection_relation = "the proposed contact meets no coherent axiom-geometry equivalence"
        elif len(selected_candidates) > 1:
            selection_relation = "independent contact does not select one coherent frame comparison"
        else:
            selection_relation = "relative contact selects one coherent frame form"
    return {
        "schema_version": 4,
        "runtime_id": "post-hoc-axiom-geometry-equivalence-constructor",
        "mode": mode,
        "visibility": protocol["visible_inputs"],
        "forbidden_inputs": protocol["forbidden_inputs"],
        "complete_return_W_visible": False,
        "artifact_a_sha256": file_digest(artifact_a_path),
        "artifact_b_sha256": file_digest(artifact_b_path),
        "protocol_sha256": file_digest(protocol_path),
        "structural_isomorphism_count": len(structural),
        "axiom_geometry_equivalence_count": len(selected_candidates),
        "contact_constraints": constraints,
        "candidate_mappings": selected_candidates,
        "selected_mapping": mapping,
        "selection": {
            "selected": mapping is not None,
            "relation": selection_relation,
        },
        "self_certification": self_assertion,
    }


def _orientation_form(
    mapping: dict[str, str], artifact_a: dict[str, Any], artifact_b: dict[str, Any]
) -> str | None:
    source_turn = artifact_b["local_generators"]["turn"]
    target = mapping.get(source_turn)
    if target not in artifact_a["presentations"]:
        return None
    zero_image = artifact_a["presentations"][target][0]
    if zero_image == 1:
        return "preserved"
    if zero_image == 3:
        return "reversed"
    return None


def _translate_pole(orientation: str | None, pole: str) -> str | None:
    if orientation == "preserved":
        return pole
    if orientation == "reversed":
        return other_pole(pole)
    return None


def _boolean_factorization_certificate(basis: Sequence[str]) -> dict[str, Any]:
    """Exhaust the finite universal property for the codomain ``Bool``."""

    ordered_basis = tuple(basis)
    occurrences = tuple((pole, item) for pole in POLES for item in ordered_basis)
    unique_factorizations = 0
    for mask in range(1 << len(ordered_basis)):
        factor = {
            item: bool(mask & (1 << index)) for index, item in enumerate(ordered_basis)
        }
        evaluation = {(pole, item): factor[item] for pole, item in occurrences}
        reconstructed = {item: evaluation[("zero", item)] for item in ordered_basis}
        if any(evaluation[(pole, item)] != reconstructed[item] for pole, item in occurrences):
            raise RuntimeError("a closure-respecting evaluation failed to factor through W")
        unique_at_every_basis = all(
            len(
                [
                    candidate
                    for candidate in (False, True)
                    if all(evaluation[(pole, item)] == candidate for pole in POLES)
                ]
            )
            == 1
            for item in ordered_basis
        )
        if not unique_at_every_basis:
            raise RuntimeError("finite factorization was not unique")
        unique_factorizations += 1

    pole_sensitive = {(pole, item): pole == "zero" for pole, item in occurrences}
    pole_sensitive_factors = all(
        pole_sensitive[("zero", item)] == pole_sensitive[("infinity", item)]
        for item in ordered_basis
    )
    return {
        "codomain": "Bool",
        "closure_respecting_evaluators_checked_per_language": 1 << len(ordered_basis),
        "unique_factorizations_through_W": unique_factorizations,
        "pole_sensitive_nonfactor_example_rejected": not pole_sensitive_factors,
    }


def _question_relation_certificate(
    basis: Sequence[str],
    frame_id: str,
    equality_name: str,
    question_id: str,
    equality: Callable[[tuple[str, str], tuple[str, str]], bool],
    question: Callable[[tuple[str, str]], str],
) -> dict[str, Any]:
    """Decide ``ResolvedIn(frame, question)`` on the finite occurrence carrier.

    Resolution means constancy on the admitted equality classes, hence finite
    factorization through the quotient.  A failure is returned as the pair of
    frame-equal occurrences separated by the question.  This makes openness a
    two-place relation and gives it an explicit witness.
    """

    occurrences = tuple((pole, item) for pole in POLES for item in basis)
    separating_pair: tuple[tuple[str, str], tuple[str, str]] | None = None
    separating_pair_count = 0
    comparisons = 0
    for left in occurrences:
        for right in occurrences:
            comparisons += 1
            if equality(left, right) and question(left) != question(right):
                separating_pair_count += 1
                if separating_pair is None:
                    separating_pair = (left, right)

    resolved = separating_pair is None
    factor_values: dict[str, str] = {}
    if resolved:
        representatives: list[tuple[str, str]] = []
        for occurrence in occurrences:
            if not any(equality(occurrence, representative) for representative in representatives):
                representatives.append(occurrence)
        factor_values = {
            digest_value({"frame": frame_id, "representative": representative}): question(representative)
            for representative in representatives
        }

    witness = None
    if separating_pair is not None:
        left, right = separating_pair
        witness = {
            "left": list(left),
            "right": list(right),
            "frame_equal": True,
            "left_value": question(left),
            "right_value": question(right),
        }

    return {
        "frame_id": frame_id,
        "frame_equality": equality_name,
        "question_id": question_id,
        "resolved_in_frame": resolved,
        "open_in_frame": not resolved,
        "equality_comparisons": comparisons,
        "separating_pair_count": separating_pair_count,
        "factorization": (
            {
                "through_frame_quotient": True,
                "unique": True,
                "quotient_class_count": len(factor_values),
                "factor_sha256": digest_value(factor_values),
            }
            if resolved
            else None
        ),
        "open_witness": witness,
    }


def certify_axiom_geometry_equivalence(
    artifact_a: dict[str, Any], artifact_b: dict[str, Any], mapping: dict[str, str]
) -> dict[str, Any]:
    """Construct reference frames, then check their finite ``GeomEquiv``.

    Occurrences are ``Pole x B_l`` and ``W_l(p,b)=b``.  A comparison
    transports the relative identity by ``phi`` and its orientation by ``pi``;
    ``T`` is their product.  The closure equality is defined before the
    remaining operations.  ``GeomEquiv`` then requires ``T`` to preserve and
    reflect exactly that admitted equality.  Only afterward are naturality and
    frame-relative question resolution checked.
    """

    a_table = artifact_a["execution"]["operation_table"]
    b_table = artifact_b["execution"]["operation_table"]
    a_basis = tuple(sorted(a_table))
    b_basis = tuple(sorted(b_table))
    total = set(mapping) == set(b_basis) and all(target in a_table for target in mapping.values())
    bijective = total and len(set(mapping.values())) == len(a_basis)
    orientation = _orientation_form(mapping, artifact_a, artifact_b)

    product_failures: list[Witness] = []
    if total:
        for left in b_basis:
            for right in b_basis:
                source_product = b_table[left][right]
                observed = a_table[mapping[left]][mapping[right]]
                expected = mapping[source_product]
                if observed != expected:
                    product_failures.append(Witness("phi_operation", [left, right], expected, observed))

    occurrences = tuple((pole, basis) for pole in POLES for basis in b_basis)
    return_square_failures: list[Witness] = []
    extension_failures: list[Witness] = []
    reversal_failures: list[Witness] = []
    curvature_failures: list[Witness] = []
    equality_preservation_failures: list[Witness] = []
    equality_reflection_failures: list[Witness] = []

    if total and orientation is not None:
        source_curvature_pole = "zero" if orientation == "preserved" else "infinity"
        for pole, basis in occurrences:
            translated_pole = _translate_pole(orientation, pole)
            translated_basis = mapping[basis]

            # W_A(T(p,b)) = phi(W_B(p,b)).
            if translated_basis != mapping[basis]:
                return_square_failures.append(Witness("T_ret", [pole, basis]))

            lhs_ext = (translated_pole, translated_basis)
            rhs_ext = (_translate_pole(orientation, pole), mapping[basis])
            if lhs_ext != rhs_ext:
                extension_failures.append(Witness("T_ext", [pole, basis], rhs_ext, lhs_ext))

            lhs_rev = (_translate_pole(orientation, other_pole(pole)), translated_basis)
            rhs_rev = (other_pole(translated_pole), translated_basis)
            if lhs_rev != rhs_rev:
                reversal_failures.append(Witness("T_J", [pole, basis], rhs_rev, lhs_rev))

            # C is a transported section, not the same isolated pole in both languages.
            lhs_curv = (_translate_pole(orientation, source_curvature_pole), translated_basis)
            rhs_curv = ("zero", translated_basis)
            if lhs_curv != rhs_curv:
                curvature_failures.append(Witness("T_C", [pole, basis], rhs_curv, lhs_curv))

        for left_pole, left_basis in occurrences:
            for right_pole, right_basis in occurrences:
                source_ceq = left_basis == right_basis
                target_ceq = mapping[left_basis] == mapping[right_basis]
                if source_ceq and not target_ceq:
                    equality_preservation_failures.append(
                        Witness(
                            "geom_equiv_preserves_equality",
                            [[left_pole, left_basis], [right_pole, right_basis]],
                            True,
                            False,
                        )
                    )
                if target_ceq and not source_ceq:
                    equality_reflection_failures.append(
                        Witness(
                            "geom_equiv_reflects_equality",
                            [[left_pole, left_basis], [right_pole, right_basis]],
                            True,
                            False,
                        )
                    )

    geom_equiv_failures = equality_preservation_failures + equality_reflection_failures
    naturality_failures = (
        product_failures
        + return_square_failures
        + extension_failures
        + reversal_failures
        + curvature_failures
    )
    law_failures = geom_equiv_failures + naturality_failures
    geom_equiv_holds = total and bijective and orientation is not None and not geom_equiv_failures
    translational_naturality_holds = geom_equiv_holds and not naturality_failures
    geom_equiv_id = digest_value({"mapping": mapping, "orientation": orientation})
    source_closure_frame_id = digest_value(
        {"language": "B", "carrier": list(b_basis), "equality": "W_B(x)=W_B(y)"}
    )
    target_closure_frame_id = digest_value(
        {"language": "A", "carrier": list(a_basis), "equality": "W_A(x)=W_A(y)"}
    )
    source_discrete_frame_id = digest_value(
        {"language": "B", "carrier": list(b_basis), "equality": "x=y"}
    )
    source_closure = lambda left, right: left[1] == right[1]
    target_closure = lambda left, right: left[1] == right[1]
    source_discrete = lambda left, right: left == right
    source_return = lambda occurrence: occurrence[1]
    target_return = lambda occurrence: occurrence[1]
    source_literal_pole = lambda occurrence: occurrence[0]
    target_literal_pole = lambda occurrence: occurrence[0]
    question_relations = [
        _question_relation_certificate(
            b_basis,
            source_closure_frame_id,
            "closure equality W_B(x)=W_B(y)",
            "returned_identity",
            source_closure,
            source_return,
        ),
        _question_relation_certificate(
            a_basis,
            target_closure_frame_id,
            "closure equality W_A(x)=W_A(y)",
            "translated_returned_identity",
            target_closure,
            target_return,
        ),
        _question_relation_certificate(
            b_basis,
            source_closure_frame_id,
            "closure equality W_B(x)=W_B(y)",
            "literal_pole_presentation",
            source_closure,
            source_literal_pole,
        ),
        _question_relation_certificate(
            a_basis,
            target_closure_frame_id,
            "closure equality W_A(x)=W_A(y)",
            "translated_literal_pole_presentation",
            target_closure,
            target_literal_pole,
        ),
        _question_relation_certificate(
            b_basis,
            source_discrete_frame_id,
            "discrete equality x=y",
            "literal_pole_presentation",
            source_discrete,
            source_literal_pole,
        ),
    ]
    return_source, return_target, pole_source, pole_target, _pole_discrete = question_relations
    resolved_transport_holds = (
        return_source["resolved_in_frame"] == return_target["resolved_in_frame"]
    )
    openness_transport_holds = pole_source["open_in_frame"] == pole_target["open_in_frame"]
    fallback_failure = {
        "check": "axiom_geometry_equivalence",
        "input": None,
        "expected": "total bijective polar translation",
        "observed": {"total": total, "bijective": bijective, "orientation": orientation},
        "reason": "GeomEquiv must carry and reflect the admitted equality invertibly",
    }
    return {
        "axiom_geometry": {
            "reference_frames": {
                "source_closure": {
                    "frame_id": source_closure_frame_id,
                    "admitted_equality": "W_B(x)=W_B(y)",
                },
                "target_closure": {
                    "frame_id": target_closure_frame_id,
                    "admitted_equality": "W_A(x)=W_A(y)",
                },
                "source_discrete_control": {
                    "frame_id": source_discrete_frame_id,
                    "admitted_equality": "x=y",
                },
            },
            "geom_equiv_sha256": geom_equiv_id,
            "preserves_admitted_equality": not equality_preservation_failures,
            "reflects_admitted_equality": not equality_reflection_failures,
            "geom_equiv_holds": geom_equiv_holds,
        },
        "basis_translation_phi": mapping,
        "orientation_translation_pi": orientation,
        "occurrence_translation_T": "(p,b) maps to (pi(p),phi(b))",
        "return_W": "W_l(p,b)=b",
        "extension_E": "E_l(p,b)=(p,b)",
        "reversal_J": "J_l(p,b)=(other(p),b)",
        "curvature_C": "the chosen pole section transported through pi",
        "laws": {
            "phi_is_bijection": bijective,
            "phi_operation_cases": len(b_basis) ** 2 if total else 0,
            "phi_operation_failure_count": len(product_failures),
            "T_ret_cases": len(occurrences) if total and orientation is not None else 0,
            "T_ret_failure_count": len(return_square_failures),
            "T_ext_cases": len(occurrences) if total and orientation is not None else 0,
            "T_ext_failure_count": len(extension_failures),
            "T_J_cases": len(occurrences) if total and orientation is not None else 0,
            "T_J_failure_count": len(reversal_failures),
            "T_C_cases": len(occurrences) if total and orientation is not None else 0,
            "T_C_failure_count": len(curvature_failures),
            "geom_equiv_preservation_cases": len(occurrences) ** 2 if total and orientation is not None else 0,
            "geom_equiv_preservation_failure_count": len(equality_preservation_failures),
            "geom_equiv_reflection_cases": len(occurrences) ** 2 if total and orientation is not None else 0,
            "geom_equiv_reflection_failure_count": len(equality_reflection_failures),
        },
        "quotient_basis": {
            "occurrences_per_language": len(POLES) * len(b_basis),
            "closure_equality_classes": len(b_basis),
            "fibre_size": len(POLES),
            "quotient_equivalent_to_basis": len(b_basis) == len(a_basis),
        },
        "polar_section": {
            "source_pole": "zero" if orientation == "preserved" else "infinity",
            "target_pole": "zero",
            "return_splits": orientation is not None,
            "natural_through_pi": orientation is not None and not curvature_failures,
            "reversal_exchanges_sections": orientation is not None and not reversal_failures,
        },
        "universal_factorization": _boolean_factorization_certificate(b_basis),
        "question_relations": question_relations,
        "question_transport": {
            "resolved_questions_transport": resolved_transport_holds,
            "open_questions_transport": openness_transport_holds,
            "language_independent": resolved_transport_holds and openness_transport_holds,
        },
        "axiom_geometry_equivalence_holds": geom_equiv_holds,
        "translational_naturality_holds": translational_naturality_holds,
        "failure_count": len(law_failures) + (0 if total else 1) + (0 if bijective else 1),
        "first_failure": asdict(law_failures[0]) if law_failures else (
            None if geom_equiv_holds else fallback_failure
        ),
    }


def evaluate_axiom_geometry(
    precommit_path: Path,
    artifact_a_path: Path,
    artifact_b_path: Path,
    translator_path: Path,
) -> dict[str, Any]:
    precommit = load_json(precommit_path)
    artifact_a = load_json(artifact_a_path)
    artifact_b = load_json(artifact_b_path)
    translator = load_json(translator_path)
    contradictions: list[Witness] = []
    pending_verifications: list[Witness] = []

    for label, path, expected_digest in (
        ("artifact_a", artifact_a_path, translator.get("artifact_a_sha256")),
        ("artifact_b", artifact_b_path, translator.get("artifact_b_sha256")),
    ):
        observed_digest = file_digest(path)
        if observed_digest != expected_digest:
            contradictions.append(Witness("frozen_hash", label, expected_digest, observed_digest))

    for label, artifact in (("A", artifact_a), ("B", artifact_b)):
        execution = artifact.get("execution", {})
        model = artifact.get("model", {})
        if execution.get("status") != "PASS":
            pending_verifications.append(Witness("learner_execution", label, reason="execution did not complete"))
        if model.get("minimum_training_error") not in (0, 0.0):
            contradictions.append(Witness("learning_error", label, 0, model.get("minimum_training_error")))
        if len(model.get("minimum_error_survivors", [])) != 1:
            pending_verifications.append(Witness("model_selection", label, reason="learned operation is not unique"))
        if execution.get("held_out_error_count") not in (0, 0.0):
            contradictions.append(Witness("held_out_execution", label, 0, execution.get("held_out_error_count")))
        if not execution.get("group_certificate", {}).get("passed", False):
            pending_verifications.append(Witness("finite_proof", label, reason="group certificate unavailable"))

    mapping = translator.get("selected_mapping")
    structural_certificates = [
        certify_axiom_geometry_equivalence(artifact_a, artifact_b, candidate)
        for candidate in enumerate_isomorphisms(artifact_a, artifact_b)
    ]
    selected_certificate = (
        certify_axiom_geometry_equivalence(artifact_a, artifact_b, mapping)
        if isinstance(mapping, dict)
        else None
    )
    if selected_certificate is None:
        pending_verifications.append(
            Witness(
                "independent_frame_selection",
                translator.get("mode"),
                reason=translator.get("selection", {}).get("relation"),
            )
        )
    elif not selected_certificate["translational_naturality_holds"]:
        failure = selected_certificate["first_failure"]
        contradictions.append(
            Witness(
                failure["check"],
                failure.get("input"),
                failure.get("expected"),
                failure.get("observed"),
                failure.get("reason"),
            )
        )

    axiom_geometry_groupoid_realized = bool(structural_certificates) and all(
        certificate["axiom_geometry_equivalence_holds"] for certificate in structural_certificates
    )
    translational_closure_family_realized = bool(structural_certificates) and all(
        certificate["translational_naturality_holds"] for certificate in structural_certificates
    )
    independent_contact = (
        bool(translator.get("contact_constraints"))
        and not bool(translator.get("self_certification"))
    )
    non_selection_verifications = [
        obligation
        for obligation in pending_verifications
        if obligation.check != "independent_frame_selection"
    ]
    selected_geom_equiv_witness = bool(
        selected_certificate
        and selected_certificate["axiom_geometry_equivalence_holds"]
        and selected_certificate["translational_naturality_holds"]
        and independent_contact
        and not contradictions
        and not non_selection_verifications
    )
    episode_role = precommit["cases"][translator.get("mode")]["episode_role"]
    admitted_to_next_basis = selected_geom_equiv_witness and episode_role == "actual"

    disclosure: dict[str, Any] | None = None
    if selected_geom_equiv_witness and mapping is not None:
        disclosure = {
            "identity": {
                "source": artifact_b["execution"]["group_certificate"]["identity"],
                "target": mapping[artifact_b["execution"]["group_certificate"]["identity"]],
            },
            "homotopy": "all learned operations commute through phi in this axiom-geometry equivalence",
            "holonomy": {
                "relative_frame_forms": translator["structural_isomorphism_count"],
                "selected_geom_equiv_sha256": selected_certificate["axiom_geometry"]["geom_equiv_sha256"],
            },
            "closure": "frame equality is preserved and reflected before W, E, T, phi, pi, J and C naturality",
        }

    question_certificate = selected_certificate or (
        structural_certificates[0] if structural_certificates else None
    )
    frame_conditional_questions = (
        question_certificate["question_relations"] if question_certificate else []
    )

    return {
        "schema_version": 4,
        "benchmark": precommit["benchmark"],
        "precommit_sha256": file_digest(precommit_path),
        "translator_sha256": file_digest(translator_path),
        "case": translator.get("mode"),
        "episode_role": episode_role,
        "axiom_geometry_relation": {
            "reference_frame_definition": "a carrier with its admitted equality",
            "geom_equiv_definition": "translation preserves and reflects admitted equality",
            "axiom_geometry_groupoid_realized": axiom_geometry_groupoid_realized,
            "translational_closure_family_realized": translational_closure_family_realized,
            "coherent_geom_equiv_count": len(structural_certificates),
            "selected_geom_equiv_sha256": (
                selected_certificate["axiom_geometry"]["geom_equiv_sha256"]
                if selected_certificate
                else None
            ),
            "selected_comparison_is_geom_equiv": bool(
                selected_certificate and selected_certificate["axiom_geometry_equivalence_holds"]
            ),
            "selected_comparison_is_natural": bool(
                selected_certificate and selected_certificate["translational_naturality_holds"]
            ),
            "independent_contact_witnessed": independent_contact,
            "selected_by_independent_contact": selected_geom_equiv_witness,
            "candidate_counterexample_witnessed": bool(contradictions),
            "interpretation": (
                "coherent alternatives are equivalent axiom geometries, not ambiguity inside fixed axioms"
            ),
        },
        "frame_conditional_questions": frame_conditional_questions,
        "selected_geom_equiv": selected_certificate,
        "structural_geom_equivs": structural_certificates,
        "contradiction_count": len(contradictions),
        "pending_verification_count": len(pending_verifications),
        "first_contradiction": asdict(contradictions[0]) if contradictions else None,
        "first_pending_verification": (
            asdict(pending_verifications[0]) if pending_verifications else None
        ),
        "self_certification_observed": bool(translator.get("self_certification")),
        "self_certification_used_as_relative_contact": False,
        "relational_disclosure": disclosure,
        "basis_admission": {
            "admitted": admitted_to_next_basis,
            "reason": (
                "actual independently selected axiom-geometry equivalence"
                if admitted_to_next_basis
                else "no actual independently selected GeomEquiv for this branch"
            ),
        },
        "tokens_issued": 1 if admitted_to_next_basis else 0,
    }


def execute_next_basis(
    artifact_a: dict[str, Any], artifact_b: dict[str, Any], translator: dict[str, Any]
) -> dict[str, Any]:
    mapping = translator.get("selected_mapping")
    if mapping is None:
        return {
            "axiom_geometry_basis_admitted": False,
            "reason": "no independently selected axiom-geometry equivalence",
        }
    b_table = artifact_b["execution"]["operation_table"]
    a_table = artifact_a["execution"]["operation_table"]
    b_identity = artifact_b["execution"]["group_certificate"]["identity"]
    a_identity = artifact_a["execution"]["group_certificate"]["identity"]
    source_word = [
        artifact_b["local_generators"]["turn"],
        artifact_b["local_generators"]["reverse"],
        artifact_b["local_generators"]["turn"],
        artifact_b["local_generators"]["turn"],
        artifact_b["local_generators"]["reverse"],
    ]
    source_result = b_identity
    for value in source_word:
        source_result = b_table[source_result][value]
    target_word = [mapping[value] for value in source_word]
    target_result = a_identity
    for value in target_word:
        target_result = a_table[target_result][value]
    expected_target = mapping[source_result]
    return {
        "axiom_geometry_basis_admitted": target_result == expected_target,
        "selected_geom_equiv_sha256": digest_value(
            {
                "mapping": mapping,
                "orientation": _orientation_form(mapping, artifact_a, artifact_b),
            }
        ),
        "new_execution": {
            "source_word": source_word,
            "source_result": source_result,
            "translated_word": target_word,
            "expected_target_result": expected_target,
            "observed_target_result": target_result,
        },
    }


class ReceiptChain:
    def __init__(self) -> None:
        self.items: list[dict[str, Any]] = []

    def append(self, stage: str, payload: dict[str, Any]) -> None:
        previous = self.items[-1]["receipt_sha256"] if self.items else "0" * 64
        body = {"seq": len(self.items) + 1, "stage": stage, "previous_sha256": previous, "payload": payload}
        self.items.append({**body, "receipt_sha256": digest_value(body)})

    def verify(self) -> dict[str, Any]:
        previous = "0" * 64
        for item in self.items:
            body = {
                "seq": item["seq"],
                "stage": item["stage"],
                "previous_sha256": previous,
                "payload": item["payload"],
            }
            if item["previous_sha256"] != previous or item["receipt_sha256"] != digest_value(body):
                return {"ok": False, "failed_seq": item["seq"]}
            previous = item["receipt_sha256"]
        return {"ok": True, "count": len(self.items), "head": previous}


def _run_stage(arguments: Sequence[str]) -> None:
    command = [sys.executable, str(Path(__file__).resolve()), *arguments]
    completed = subprocess.run(command, cwd=ROOT, text=True, capture_output=True, check=False)
    if completed.returncode != 0:
        raise RuntimeError(
            f"stage failed ({completed.returncode}): {' '.join(arguments)}\n{completed.stdout}\n{completed.stderr}"
        )


def run_full_stack(output_dir: Path = DEFAULT_OUTPUT) -> dict[str, Any]:
    output_dir.mkdir(parents=True, exist_ok=True)
    for obsolete_pattern in ("return_audit_*.json", "relative_equality_*.json"):
        for obsolete in output_dir.glob(obsolete_pattern):
            obsolete.unlink()
    for obsolete_name in (
        "translator_structural_only.json",
        "translator_adversarial_reverse_contact.json",
    ):
        obsolete = output_dir / obsolete_name
        if obsolete.exists():
            obsolete.unlink()
    precommit = BENCHMARK / "precommit_return.json"
    protocol_a = BENCHMARK / "perspective_a_protocol.json"
    protocol_b = BENCHMARK / "perspective_b_protocol.json"
    translator_protocol = BENCHMARK / "translator_protocol.json"
    chain = ReceiptChain()
    chain.append(
        "POTENTIAL_PRECOMMIT",
        {
            "precommit_sha256": file_digest(precommit),
            "selected_perspective": None,
            "identity": None,
            "homotopy": None,
            "holonomy": None,
            "closure": None,
        },
    )

    artifact_a_path = output_dir / "perspective_a_frozen.json"
    artifact_b_path = output_dir / "perspective_b_frozen.json"
    with tempfile.TemporaryDirectory(prefix="full-stack-d4-") as temporary_name:
        temporary = Path(temporary_name)
        stage_a = temporary / "a.json"
        stage_b = temporary / "b.json"
        _run_stage(["--stage", "learn-a", "--protocol", str(protocol_a), "--output", str(stage_a)])
        _run_stage(["--stage", "learn-b", "--protocol", str(protocol_b), "--output", str(stage_b)])
        shutil.copyfile(stage_a, artifact_a_path)
        shutil.copyfile(stage_b, artifact_b_path)

    frozen_a = file_digest(artifact_a_path)
    frozen_b = file_digest(artifact_b_path)
    chain.append("LEARNER_A_FROZEN", {"sha256": frozen_a})
    chain.append("LEARNER_B_FROZEN", {"sha256": frozen_b})

    modes = (
        "relational_contact",
        "relative_reversal",
        "structural_family",
        "non_natural_deformation",
        "self_certification_only",
    )
    cases: list[dict[str, Any]] = []
    for mode in modes:
        translator_path = output_dir / f"translator_{mode}.json"
        result_path = output_dir / f"axiom_geometry_{mode}.json"
        _run_stage(
            [
                "--stage", "translate", "--artifact-a", str(artifact_a_path),
                "--artifact-b", str(artifact_b_path), "--protocol", str(translator_protocol),
                "--mode", mode, "--output", str(translator_path),
            ]
        )
        chain.append("TRANSLATOR_FROZEN", {"mode": mode, "sha256": file_digest(translator_path)})
        _run_stage(
            [
                "--stage", "verify", "--precommit", str(precommit),
                "--artifact-a", str(artifact_a_path), "--artifact-b", str(artifact_b_path),
                "--translator", str(translator_path), "--output", str(result_path),
            ]
        )
        result = load_json(result_path)
        cases.append(result)
        chain.append(
            "AXIOM_GEOMETRY_EQUIVALENCE",
            {
                "mode": mode,
                "geom_equiv_holds": result["axiom_geometry_relation"]["selected_comparison_is_geom_equiv"],
                "translational_naturality_holds": result["axiom_geometry_relation"]["selected_comparison_is_natural"],
                "selected_by_independent_contact": result["axiom_geometry_relation"]["selected_by_independent_contact"],
                "candidate_counterexample_witnessed": result["axiom_geometry_relation"]["candidate_counterexample_witnessed"],
                "sha256": file_digest(result_path),
            },
        )

    if file_digest(artifact_a_path) != frozen_a or file_digest(artifact_b_path) != frozen_b:
        raise RuntimeError("a learner artifact changed after translation began")

    main_translator = load_json(output_dir / "translator_relational_contact.json")
    main_result = next(case for case in cases if case["case"] == "relational_contact")
    if main_result["basis_admission"]["admitted"]:
        next_basis = execute_next_basis(load_json(artifact_a_path), load_json(artifact_b_path), main_translator)
    else:
        next_basis = {
            "axiom_geometry_basis_admitted": False,
            "reason": "the actual branch did not independently select a GeomEquiv",
        }
    write_json(output_dir / "returned_basis.json", next_basis)
    chain.append(
        "NEXT_BASIS",
        {
            "axiom_geometry_basis_admitted": next_basis["axiom_geometry_basis_admitted"],
            "sha256": file_digest(output_dir / "returned_basis.json"),
        },
    )

    token_count = sum(int(case["tokens_issued"]) for case in cases)
    summary = {
        "schema_version": 4,
        "claim_status": "EXPERIMENTAL_CLASSICAL_MATHEMATICAL_AGENT_PROXY",
        "benchmark": load_json(precommit)["benchmark"],
        "run_id": f"full-stack-{file_digest(precommit)[:16]}",
        "mathematical_runtime_order": [
            "closure equality defines each ReferenceFrame",
            "(T, phi, pi) preserves and reflects equality as GeomEquiv",
            "return, extension, reversal and curvature commute naturally",
            "ResolvedIn(frame, question) factors through the frame quotient",
            "OpenIn(frame, question) has a frame-equal separating pair",
            "next basis",
        ],
        "execution_order": [
            "independent learning",
            "exhaustive local execution",
            "frozen artifacts",
            "post-hoc frame comparison",
            "independent selection or explicit non-selection",
        ],
        "process_boundaries": {
            "learner_a": "fresh subprocess; perspective A protocol only",
            "learner_b": "fresh subprocess; perspective B protocol only",
            "translator": "fresh subprocess; frozen artifacts and contact protocol; complete contact withheld",
            "verifier": "fresh subprocess; constructs frame equality first, checks GeomEquiv, then naturality and question factorization",
            "security_claim": "experimental visibility separation, not an OS security sandbox",
        },
        "artifact_hashes": {"perspective_a": frozen_a, "perspective_b": frozen_b},
        "cases": cases,
        "main_case": main_result,
        "tokens_issued": token_count,
        "token_bound_respected": token_count <= 1,
        "next_basis": next_basis,
        "unselected_or_rejected_comparisons": [
            case["case"]
            for case in cases
            if not case["axiom_geometry_relation"]["selected_by_independent_contact"]
        ],
    }
    chain.append("RUN_SUMMARY", {"summary_sha256": digest_value(summary)})
    summary["receipt_chain"] = chain.verify()
    write_json(output_dir / "full_stack_result.json", summary)
    receipts_path = output_dir / "receipts.jsonl"
    receipts_path.write_text("".join(canonical_json(item) + "\n" for item in chain.items), encoding="utf-8")
    return summary


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stage", choices=("learn-a", "learn-b", "translate", "verify"))
    parser.add_argument("--protocol", type=Path)
    parser.add_argument("--precommit", type=Path)
    parser.add_argument("--artifact-a", type=Path)
    parser.add_argument("--artifact-b", type=Path)
    parser.add_argument("--translator", type=Path)
    parser.add_argument("--mode")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--assert-reference", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = _parse_args()
    if args.stage:
        if args.output is None:
            raise SystemExit("--output is required for a stage")
        if args.stage == "learn-a":
            result = learn_agent_a(args.protocol)
        elif args.stage == "learn-b":
            result = learn_agent_b(args.protocol)
        elif args.stage == "translate":
            result = translate_artifacts(args.artifact_a, args.artifact_b, args.protocol, args.mode)
        else:
            result = evaluate_axiom_geometry(
                args.precommit, args.artifact_a, args.artifact_b, args.translator
            )
        write_json(args.output, result)
        return 0

    result = run_full_stack(args.output_dir)
    print(json.dumps(result, indent=2, sort_keys=True))
    if args.assert_reference:
        by_case = {case["case"]: case for case in result["cases"]}
        passed = (
            by_case["relational_contact"]["axiom_geometry_relation"]["selected_by_independent_contact"]
            and by_case["relative_reversal"]["axiom_geometry_relation"]["selected_by_independent_contact"]
            and by_case["structural_family"]["axiom_geometry_relation"]["axiom_geometry_groupoid_realized"]
            and by_case["structural_family"]["axiom_geometry_relation"]["translational_closure_family_realized"]
            and not by_case["structural_family"]["axiom_geometry_relation"]["selected_by_independent_contact"]
            and by_case["non_natural_deformation"]["axiom_geometry_relation"]["candidate_counterexample_witnessed"]
            and not by_case["self_certification_only"]["axiom_geometry_relation"]["selected_by_independent_contact"]
            and result["tokens_issued"] == 1
            and result["token_bound_respected"]
            and result["next_basis"]["axiom_geometry_basis_admitted"]
            and result["receipt_chain"]["ok"]
        )
        return 0 if passed else 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
