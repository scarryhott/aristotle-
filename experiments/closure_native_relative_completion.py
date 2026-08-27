"""A bounded native test of closure as relative translational completion.

Frozen presentations are immutable receipts, not absolute identities.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any


def digest(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def freeze(presentation: dict[str, Any]) -> dict[str, Any]:
    return {"presentation": presentation, "sha256": digest(presentation)}


def verify_frozen(receipt: dict[str, Any]) -> bool:
    return receipt["sha256"] == digest(receipt["presentation"])


def evaluate(*, source: dict[str, Any], target: dict[str, Any], translation: dict[str, Any], returned: dict[str, Any]) -> dict[str, Any]:
    """Evaluate only the admitted interface plus an independent return.

    A nonzero residue is retained; it is never normalized into literal identity.
    """
    if not verify_frozen(source) or not verify_frozen(target):
        return {"status": "INVALID_FROZEN_RECEIPT"}
    source_values = source["presentation"]["overlap_values"]
    target_values = target["presentation"]["overlap_values"]
    forward, backward, admitted = translation["forward"], returned["backward"], translation["admitted_overlap"]
    preservation = all(target_values[forward[key]] == source_values[key] + translation["offset"] for key in admitted)
    recovery = all(backward[forward[key]] == key for key in admitted)
    reflection = len({forward[key] for key in admitted}) == len(admitted)
    moves_presentation = any(source_values[key] != target_values[forward[key]] for key in admitted)
    result = {
        "receipt_integrity": True,
        "absolute_full_presentation_identity_claimed": False,
        "admitted_overlap": admitted,
        "translation_preserves_relative_relation": preservation,
        "return_recovers_admitted_overlap": recovery,
        "translation_reflects_admitted_distinction": reflection,
        "round_moves_an_admitted_presentation": moves_presentation,
        "residue": returned["residue"],
        "residue_is_neutral": returned["residue"] == 0,
    }
    if not (preservation and recovery and reflection):
        result["status"] = "RELATIVE_OBSTRUCTION"
    elif not moves_presentation:
        result["status"] = "FROZEN_AXIOMETRY"
    elif result["residue_is_neutral"]:
        result["status"] = "RELATIVE_COMPLETION"
    else:
        result["status"] = "RELATIVE_COMPLETION_WITH_OPENING"
    return result


def native_cases() -> dict[str, Any]:
    overlap = ["u0", "u1"]
    # g0=0 and g1=1 do not literally glue, but a +1 translation and return
    # recover the admitted relation while leaving a registered opening.
    unglued_a = freeze({"name": "g0", "formula": "0", "overlap_values": {"u0": 0, "u1": 0}})
    unglued_b = freeze({"name": "g1", "formula": "1", "overlap_values": {"u0": 1, "u1": 1}})
    relative_gluing = evaluate(source=unglued_a, target=unglued_b, translation={"admitted_overlap": overlap, "forward": {"u0": "u0", "u1": "u1"}, "offset": 1}, returned={"backward": {"u0": "u0", "u1": "u1"}, "residue": 1})

    # f0=x and f1=x literally glue, but an independent non-reflecting return
    # collapses their positions. Literal agreement does not imply completion.
    glued_a = freeze({"name": "f0", "formula": "x", "overlap_values": {"u0": 0, "u1": 1}})
    glued_b = freeze({"name": "f1", "formula": "x", "overlap_values": {"u0": 0, "u1": 1}})
    relative_obstruction = evaluate(source=glued_a, target=glued_b, translation={"admitted_overlap": overlap, "forward": {"u0": "u0", "u1": "u1"}, "offset": 0}, returned={"backward": {"u0": "u0", "u1": "u0"}, "residue": 0})
    frozen_identity = evaluate(source=glued_a, target=glued_b, translation={"admitted_overlap": overlap, "forward": {"u0": "u0", "u1": "u1"}, "offset": 0}, returned={"backward": {"u0": "u0", "u1": "u1"}, "residue": 0})
    return {
        "protocol": "closure_native_relative_translation_v1",
        "freeze_means": "immutable provenance receipt, not absolute identity",
        "relative_gluing_of_literally_unglued_pair": relative_gluing,
        "relative_obstruction_of_literally_glued_pair": relative_obstruction,
        "frozen_identity_control": frozen_identity,
    }


def run(output: Path) -> dict[str, Any]:
    output.mkdir(parents=True, exist_ok=True)
    result = native_cases()
    (output / "closure_native_relative_completion.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return result


if __name__ == "__main__":
    run(Path("runs/closure_native_relative_completion"))
