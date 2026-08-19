"""Bounded depth-aware reclosure of translational verification.

This control treats a question language as a frozen, ordered stream.  Equality
at depth ``n`` means that an independently supplied contact bridge can compare
all questions through that level.  A later registered question may separate
presentations without refuting their earlier, coarser equality.

It is not a model of QG, Chaitin/Kakeya, Kolmogorov complexity, or a warrant
for a frontier bridge.  It makes the depth discipline executable.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Callable


@dataclass(frozen=True)
class Form:
    name: str
    aggregate: int
    magnitude: int
    phase: int
    route: tuple[int, ...]


@dataclass(frozen=True)
class Question:
    identifier: str
    answer: Callable[[Form], object]


def schema_digest(questions: tuple[Question, ...]) -> str:
    """Receipt for the order and identity of the registered question stream."""
    payload = json.dumps([q.identifier for q in questions], separators=(",", ":")).encode()
    return hashlib.sha256(payload).hexdigest()


def evaluate(
    left: Form,
    right: Form,
    questions: tuple[Question, ...],
    *,
    bridge_available: bool,
    expected_schema_digest: str,
) -> dict[str, object]:
    """Evaluate only the pre-registered stream under a supplied bridge flag."""
    observed_digest = schema_digest(questions)
    if observed_digest != expected_schema_digest:
        return {
            "classification": "INVALID_POSTHOC_QUESTION_STREAM",
            "expected_schema_digest": expected_schema_digest,
            "observed_schema_digest": observed_digest,
        }
    if not bridge_available:
        return {
            "classification": "OPEN_BRIDGE_BOUNDARY",
            "schema_digest": observed_digest,
            "missing_datum": "shared answer correspondence and independent non-local return",
        }

    records: list[dict[str, object]] = []
    for depth, question in enumerate(questions):
        left_answer = question.answer(left)
        right_answer = question.answer(right)
        equal = left_answer == right_answer
        records.append(
            {
                "depth": depth,
                "question": question.identifier,
                "left_answer": left_answer,
                "right_answer": right_answer,
                "equal": equal,
            }
        )
        if not equal:
            return {
                "classification": "SEPARATED_AT_REGISTERED_DEPTH",
                "first_separation_depth": depth,
                "records": records,
                "schema_digest": observed_digest,
                "residue_retained": True,
            }
    return {
        "classification": "EQUAL_THROUGH_REGISTERED_DEPTH",
        "records": records,
        "schema_digest": observed_digest,
        "residue_retained": True,
    }


def run(output: Path) -> dict[str, object]:
    output.mkdir(parents=True, exist_ok=True)
    aggregate = Question("aggregate", lambda form: form.aggregate)
    magnitude = Question("magnitude", lambda form: form.magnitude)
    phase = Question("phase", lambda form: form.phase)
    route = Question("route", lambda form: form.route)

    invariant_stream = (aggregate, magnitude)
    perspectival_stream = invariant_stream + (phase,)
    route_stream = perspectival_stream + (route,)
    left = Form("left", aggregate=0, magnitude=2, phase=0, route=(1, -1))
    phase_distinct = Form("phase_distinct", aggregate=0, magnitude=2, phase=1, route=(1, -1))
    rotation_translate = Form("rotation_translate", aggregate=0, magnitude=2, phase=0, route=(1, -1))

    result = {
        "protocol": "closure_native_depth_reclosure_v1",
        "claim_boundary": "bounded registered-question control; no physical, QG, Chaitin/Kakeya, Kolmogorov, or frontier-contact claim",
        "invariant_equality": evaluate(
            left,
            phase_distinct,
            invariant_stream,
            bridge_available=True,
            expected_schema_digest=schema_digest(invariant_stream),
        ),
        "perspectival_separation": evaluate(
            left,
            phase_distinct,
            perspectival_stream,
            bridge_available=True,
            expected_schema_digest=schema_digest(perspectival_stream),
        ),
        "translation_invariant_control": evaluate(
            left,
            rotation_translate,
            invariant_stream,
            bridge_available=True,
            expected_schema_digest=schema_digest(invariant_stream),
        ),
        "missing_contact_bridge_control": evaluate(
            left,
            phase_distinct,
            perspectival_stream,
            bridge_available=False,
            expected_schema_digest=schema_digest(perspectival_stream),
        ),
        "posthoc_question_control": evaluate(
            left,
            phase_distinct,
            route_stream,
            bridge_available=True,
            expected_schema_digest=schema_digest(perspectival_stream),
        ),
    }
    (output / "closure_native_depth_reclosure.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return result


if __name__ == "__main__":
    run(Path("runs/closure_native_depth_reclosure"))
