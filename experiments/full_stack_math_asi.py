#!/usr/bin/env python3
"""Independent learning-to-execution translational-axiometry experiment.

This executable is a classical symbolic mathematical-agent proxy.  It does not
claim to instantiate general ASI.  It does implement the stronger experimental
boundary requested by the project:

    independent learning -> exhaustive execution -> frozen artifacts
      -> post-hoc translation -> external W -> TRUE / FALSE / OPEN

Perspective A and perspective B are started as separate subprocesses with
disjoint protocol files.  The translator is a third subprocess and is not
given the complete precommitted return.  A fourth process applies that return.
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
from enum import Enum
from pathlib import Path
from typing import Any, Callable, Sequence


ROOT = Path(__file__).resolve().parents[1]
BENCHMARK = ROOT / "benchmarks" / "full_stack_d4"
DEFAULT_OUTPUT = ROOT / "runs" / "full_stack_d4" / "latest"

Permutation = tuple[int, int, int, int]
NormalForm = tuple[int, int]
Element = tuple[int, ...]
Operation = Callable[[Element, Element], Element]


class ClosureVerdict(str, Enum):
    TRUE = "TRUE"
    FALSE = "FALSE"
    OPEN = "OPEN"


@dataclass(frozen=True)
class Witness:
    check: str
    input: object
    expected: object | None = None
    observed: object | None = None
    reason: str | None = None


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
    status = "PASS" if best_error == 0 and len(survivors) == 1 and not held_out_errors and certificate["passed"] else "OPEN"
    return {
        "schema_version": 1,
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
    status = "PASS" if best_error == 0 and len(survivors) == 1 and not held_out_errors and certificate["passed"] else "OPEN"
    return {
        "schema_version": 1,
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


def translate_artifacts(
    artifact_a_path: Path, artifact_b_path: Path, protocol_path: Path, mode: str
) -> dict[str, Any]:
    artifact_a = load_json(artifact_a_path)
    artifact_b = load_json(artifact_b_path)
    protocol = load_json(protocol_path)
    structural = enumerate_isomorphisms(artifact_a, artifact_b)
    if mode == "self_certification_only":
        constraints: list[dict[str, Any]] = []
        selected_candidates: list[dict[str, str]] = []
        self_assertion = True
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
    if mode == "self_certification_only":
        unresolved_reason = "self-certification supplies no independent bridge evidence"
    elif not selected_candidates:
        unresolved_reason = "contact constraints select no structural isomorphism"
    elif len(selected_candidates) > 1:
        unresolved_reason = "multiple origin choices remain structurally admissible"
    else:
        unresolved_reason = None
    return {
        "schema_version": 1,
        "runtime_id": "post-hoc-structural-translator",
        "mode": mode,
        "visibility": protocol["visible_inputs"],
        "forbidden_inputs": protocol["forbidden_inputs"],
        "complete_return_W_visible": False,
        "artifact_a_sha256": file_digest(artifact_a_path),
        "artifact_b_sha256": file_digest(artifact_b_path),
        "protocol_sha256": file_digest(protocol_path),
        "structural_isomorphism_count": len(structural),
        "post_contact_candidate_count": len(selected_candidates),
        "contact_constraints": constraints,
        "candidate_mappings": selected_candidates,
        "selected_mapping": mapping,
        "unresolved_reason": unresolved_reason,
        "self_certification": self_assertion,
    }


def evaluate_closure(
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
    unresolved: list[Witness] = []

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
            unresolved.append(Witness("learner_execution", label, reason="execution did not complete"))
        if model.get("minimum_training_error") not in (0, 0.0):
            contradictions.append(Witness("learning_error", label, 0, model.get("minimum_training_error")))
        if len(model.get("minimum_error_survivors", [])) != 1:
            unresolved.append(Witness("model_selection", label, reason="learned operation is not unique"))
        if execution.get("held_out_error_count") not in (0, 0.0):
            contradictions.append(Witness("held_out_execution", label, 0, execution.get("held_out_error_count")))
        if not execution.get("group_certificate", {}).get("passed", False):
            unresolved.append(Witness("finite_proof", label, reason="group certificate unavailable"))

    mapping = translator.get("selected_mapping")
    if mapping is None:
        unresolved.append(
            Witness("translation", translator.get("mode"), reason=translator.get("unresolved_reason"))
        )

    completed_element_returns = 0
    completed_product_returns = 0
    if mapping is not None:
        a_presentations = artifact_a["presentations"]
        b_presentations = artifact_b["presentations"]
        for source, source_presentation in sorted(b_presentations.items()):
            target = mapping.get(source)
            if target is None or target not in a_presentations:
                unresolved.append(Witness("element_return", source, reason="mapping unavailable"))
                continue
            expected = normal_action(as_element(source_presentation))
            observed = as_element(a_presentations[target])
            completed_element_returns += 1
            if observed != expected:
                contradictions.append(Witness("element_return", source, expected, observed))

        a_table = artifact_a["execution"]["operation_table"]
        b_table = artifact_b["execution"]["operation_table"]
        for left in sorted(b_table):
            for right in sorted(b_table):
                product = b_table[left][right]
                if left not in mapping or right not in mapping or product not in mapping:
                    unresolved.append(Witness("product_return", [left, right], reason="mapping unavailable"))
                    continue
                expected = mapping[product]
                observed = a_table[mapping[left]][mapping[right]]
                completed_product_returns += 1
                if observed != expected:
                    contradictions.append(Witness("product_return", [left, right], expected, observed))

    if contradictions:
        verdict = ClosureVerdict.FALSE
    elif unresolved:
        verdict = ClosureVerdict.OPEN
    else:
        verdict = ClosureVerdict.TRUE

    disclosure: dict[str, Any] | None = None
    if verdict is ClosureVerdict.TRUE:
        disclosure = {
            "identity": {
                "source": artifact_b["execution"]["group_certificate"]["identity"],
                "target": mapping[artifact_b["execution"]["group_certificate"]["identity"]],
            },
            "homotopy": "all learned products commute through the returned bridge",
            "holonomy": {
                "structural_routes_before_contact": translator["structural_isomorphism_count"],
                "routes_after_relative_contact": translator["post_contact_candidate_count"],
            },
            "closure": "all eight element returns and all 64 ordered products agree",
        }

    return {
        "schema_version": 1,
        "benchmark": precommit["benchmark"],
        "precommit_sha256": file_digest(precommit_path),
        "translator_sha256": file_digest(translator_path),
        "case": translator.get("mode"),
        "delta_C": verdict.value,
        "coverage": {
            "completed_element_returns": completed_element_returns,
            "total_element_returns": 8,
            "completed_ordered_product_returns": completed_product_returns,
            "total_ordered_product_returns": 64,
        },
        "contradiction_count": len(contradictions),
        "unresolved_count": len(unresolved),
        "first_contradiction": asdict(contradictions[0]) if contradictions else None,
        "first_unresolved": asdict(unresolved[0]) if unresolved else None,
        "self_certification_observed": bool(translator.get("self_certification")),
        "self_certification_used_as_evidence": False,
        "disclosure_after_return": disclosure,
        "tokens_issued": 1 if verdict is ClosureVerdict.TRUE else 0,
    }


def execute_next_basis(
    artifact_a: dict[str, Any], artifact_b: dict[str, Any], translator: dict[str, Any]
) -> dict[str, Any]:
    mapping = translator.get("selected_mapping")
    if mapping is None:
        return {"status": "OPEN", "reason": "no accepted returned relation"}
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
        "status": "PASS" if target_result == expected_target else "FALSE",
        "returned_relation_sha256": digest_value(mapping),
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
        "structural_only",
        "adversarial_reverse_contact",
        "self_certification_only",
    )
    cases: list[dict[str, Any]] = []
    for mode in modes:
        translator_path = output_dir / f"translator_{mode}.json"
        result_path = output_dir / f"closure_{mode}.json"
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
            "INDEPENDENT_RETURN",
            {"mode": mode, "delta_C": result["delta_C"], "sha256": file_digest(result_path)},
        )

    if file_digest(artifact_a_path) != frozen_a or file_digest(artifact_b_path) != frozen_b:
        raise RuntimeError("a learner artifact changed after translation began")

    main_translator = load_json(output_dir / "translator_relational_contact.json")
    main_result = next(case for case in cases if case["case"] == "relational_contact")
    if main_result["delta_C"] == ClosureVerdict.TRUE.value:
        next_basis = execute_next_basis(load_json(artifact_a_path), load_json(artifact_b_path), main_translator)
    else:
        next_basis = {"status": "OPEN", "reason": "main relation did not return TRUE"}
    write_json(output_dir / "returned_basis.json", next_basis)
    chain.append("NEXT_BASIS", {"status": next_basis["status"], "sha256": file_digest(output_dir / "returned_basis.json")})

    token_count = sum(int(case["tokens_issued"]) for case in cases)
    summary = {
        "schema_version": 1,
        "claim_status": "EXPERIMENTAL_CLASSICAL_MATHEMATICAL_AGENT_PROXY",
        "benchmark": load_json(precommit)["benchmark"],
        "run_id": f"full-stack-{file_digest(precommit)[:16]}",
        "closure_relation": [
            "independent learning",
            "exhaustive local execution",
            "frozen artifacts",
            "post-hoc translation",
            "external return W",
            "TRUE/FALSE/OPEN",
            "next basis",
        ],
        "process_boundaries": {
            "learner_a": "fresh subprocess; perspective A protocol only",
            "learner_b": "fresh subprocess; perspective B protocol only",
            "translator": "fresh subprocess; frozen artifacts and contact protocol; complete W withheld",
            "verifier": "fresh subprocess; precommitted W and frozen artifacts",
            "security_claim": "experimental visibility separation, not an OS security sandbox",
        },
        "artifact_hashes": {"perspective_a": frozen_a, "perspective_b": frozen_b},
        "cases": cases,
        "main_case": main_result,
        "tokens_issued": token_count,
        "token_bound_respected": token_count <= 1,
        "next_basis": next_basis,
        "open_branches_retained": [case["case"] for case in cases if case["delta_C"] == "OPEN"],
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
            result = evaluate_closure(args.precommit, args.artifact_a, args.artifact_b, args.translator)
        write_json(args.output, result)
        return 0

    result = run_full_stack(args.output_dir)
    print(json.dumps(result, indent=2, sort_keys=True))
    if args.assert_reference:
        expected = {
            "relational_contact": "TRUE",
            "structural_only": "OPEN",
            "adversarial_reverse_contact": "FALSE",
            "self_certification_only": "OPEN",
        }
        observed = {case["case"]: case["delta_C"] for case in result["cases"]}
        passed = (
            observed == expected
            and result["tokens_issued"] == 1
            and result["token_bound_respected"]
            and result["next_basis"]["status"] == "PASS"
            and result["receipt_chain"]["ok"]
        )
        return 0 if passed else 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
