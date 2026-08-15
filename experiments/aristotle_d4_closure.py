#!/usr/bin/env python3
"""Exhaustive reference gate for the blind Aristotle D4 translation experiment.

This is not an Aristotle result.  It is the frozen, independently executable
oracle used to score later Aristotle artifacts.  The return protocol lives in
``benchmarks/d4/precommit_return.json`` and must be committed before the blind
representation and translator runs begin.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import asdict, dataclass
from enum import Enum
from pathlib import Path
from typing import Callable, Iterable


Vertex = int
Permutation = tuple[Vertex, Vertex, Vertex, Vertex]
NormalForm = tuple[int, int]
Translator = Callable[[NormalForm], Permutation | None]


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


def d4_elements() -> tuple[NormalForm, ...]:
    """The eight normal forms ``r^k s^flip``."""

    return tuple((rotation, flip) for flip in (0, 1) for rotation in range(4))


def normal_action(value: NormalForm) -> Permutation:
    """Representation B's independently fixed action on square vertices.

    ``(k, f)`` acts by ``x |-> k + (-1)^f x (mod 4)``.
    """

    rotation, flip = value
    sign = -1 if flip else 1
    return tuple((rotation + sign * vertex) % 4 for vertex in range(4))  # type: ignore[return-value]


def normal_multiply(left: NormalForm, right: NormalForm) -> NormalForm:
    """Representation B multiplication, independently specified as Z4 semidirect Z2."""

    left_rotation, left_flip = left
    right_rotation, right_flip = right
    sign = -1 if left_flip else 1
    return ((left_rotation + sign * right_rotation) % 4, left_flip ^ right_flip)


def permutation_compose(left: Permutation, right: Permutation) -> Permutation:
    """Representation A multiplication: function composition ``left after right``."""

    return tuple(left[right[vertex]] for vertex in range(4))  # type: ignore[return-value]


def correct_translator(value: NormalForm) -> Permutation:
    """The candidate bridge expected to close all eight elements."""

    return normal_action(value)


def wrong_sign_translator(value: NormalForm) -> Permutation:
    """Adversary: erase the reflection sign while pretending translation is total."""

    rotation, _flip = value
    return tuple((rotation + vertex) % 4 for vertex in range(4))  # type: ignore[return-value]


def rotations_only_translator(value: NormalForm) -> Permutation | None:
    """Partial bridge: rotations return, reflections remain unresolved."""

    _rotation, flip = value
    return normal_action(value) if flip == 0 else None


TRANSLATORS: dict[str, Translator] = {
    "candidate_correct": correct_translator,
    "adversarial_wrong_sign": wrong_sign_translator,
    "adversarial_partial": rotations_only_translator,
}


def _as_json(value: object) -> object:
    if isinstance(value, tuple):
        return [_as_json(item) for item in value]
    if isinstance(value, list):
        return [_as_json(item) for item in value]
    if isinstance(value, dict):
        return {key: _as_json(item) for key, item in value.items()}
    return value


def evaluate_translator(name: str, translator: Translator) -> dict[str, object]:
    """Compute delta_C with FALSE > OPEN > TRUE precedence.

    A witnessed contradiction is FALSE even if other inputs are unresolved.
    With no contradiction, any unresolved input is OPEN.  Only exhaustive
    agreement is TRUE.
    """

    elements = d4_elements()
    translated = {value: translator(value) for value in elements}
    contradictions: list[Witness] = []
    unresolved: list[Witness] = []
    completed_element_checks = 0
    completed_product_checks = 0

    for value in elements:
        observed = translated[value]
        expected = normal_action(value)
        if observed is None:
            unresolved.append(
                Witness("return", value, expected=expected, reason="translator undefined")
            )
            continue
        completed_element_checks += 1
        if observed != expected:
            contradictions.append(Witness("return", value, expected, observed))

    for left in elements:
        for right in elements:
            product = normal_multiply(left, right)
            left_image = translated[left]
            right_image = translated[right]
            product_image = translated[product]
            if left_image is None or right_image is None or product_image is None:
                unresolved.append(
                    Witness(
                        "multiplication",
                        (left, right),
                        reason="one or more translated factors unresolved",
                    )
                )
                continue
            completed_product_checks += 1
            observed = permutation_compose(left_image, right_image)
            if observed != product_image:
                contradictions.append(
                    Witness("multiplication", (left, right), product_image, observed)
                )

    if contradictions:
        verdict = ClosureVerdict.FALSE
    elif unresolved:
        verdict = ClosureVerdict.OPEN
    else:
        verdict = ClosureVerdict.TRUE

    return {
        "translator": name,
        "delta_C": verdict.value,
        "coverage": {
            "completed_element_returns": completed_element_checks,
            "total_element_returns": len(elements),
            "completed_ordered_products": completed_product_checks,
            "total_ordered_products": len(elements) ** 2,
        },
        "contradiction_count": len(contradictions),
        "unresolved_count": len(unresolved),
        "first_contradiction": _as_json(asdict(contradictions[0])) if contradictions else None,
        "first_unresolved": _as_json(asdict(unresolved[0])) if unresolved else None,
    }


def load_precommit(path: Path) -> tuple[dict[str, object], str]:
    raw = path.read_bytes()
    protocol = json.loads(raw)
    if protocol.get("benchmark") != "D4-blind-translation-v1":
        raise ValueError("unexpected or missing benchmark identifier")
    return protocol, hashlib.sha256(raw).hexdigest()


def run(precommit_path: Path, names: Iterable[str] = TRANSLATORS) -> dict[str, object]:
    protocol, digest = load_precommit(precommit_path)
    cases = [evaluate_translator(name, TRANSLATORS[name]) for name in names]
    return {
        "schema_version": 1,
        "claim_status": "EXPERIMENTAL_REFERENCE_FIXTURE",
        "aristotle_execution_status": "OPEN",
        "benchmark": protocol["benchmark"],
        "precommit_sha256": digest,
        "cases": cases,
    }


def _default_precommit() -> Path:
    return Path(__file__).resolve().parents[1] / "benchmarks" / "d4" / "precommit_return.json"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--precommit", type=Path, default=_default_precommit())
    parser.add_argument("--translator", choices=tuple(TRANSLATORS), action="append")
    parser.add_argument("--assert-reference", action="store_true")
    args = parser.parse_args()

    names = args.translator or list(TRANSLATORS)
    result = run(args.precommit, names)
    print(json.dumps(result, indent=2, sort_keys=True))

    if args.assert_reference:
        expected = {
            "candidate_correct": "TRUE",
            "adversarial_wrong_sign": "FALSE",
            "adversarial_partial": "OPEN",
        }
        observed = {case["translator"]: case["delta_C"] for case in result["cases"]}
        return 0 if observed == {name: expected[name] for name in names} else 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
