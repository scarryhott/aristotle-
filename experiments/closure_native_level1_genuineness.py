"""Native Level-1 bridge controls for receipt-gated translational access.

The gate's receipt reading and the independent genuineness bridge are distinct
data sources.  A structurally translating gate is OPEN when the latter is not
available, and invalid when it merely reuses its own verdict as that bridge.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any


ATTEMPTS = (
    {"id": "a0", "receipt_read": True, "level1": True},
    {"id": "a1", "receipt_read": False, "level1": False},
    {"id": "a2", "receipt_read": True, "level1": True},
    {"id": "a3", "receipt_read": False, "level1": False},
)


def audit_gate(attempts: tuple[dict[str, Any], ...], *, bridge_source: str) -> dict[str, Any]:
    decisions = {attempt["id"]: attempt["receipt_read"] for attempt in attempts}
    if bridge_source == "gate_verdict":
        return {
            "status": "INVALID_SELF_CERTIFICATION",
            "bridge_source": bridge_source,
            "gate_decisions": decisions,
            "reason": "the gate verdict cannot certify the correctness of its own receipt reading",
        }
    if bridge_source == "absent":
        return {
            "status": "OPEN_NO_LEVEL1_BRIDGE",
            "bridge_source": bridge_source,
            "gate_decisions": decisions,
            "reason": "structural translation does not establish receipt genuineness",
        }
    compared = [(decisions[attempt["id"]], attempt["level1"]) for attempt in attempts]
    false_accepts = sum(decision and not genuine for decision, genuine in compared)
    false_rejects = sum(not decision and genuine for decision, genuine in compared)
    evaluated = len(compared)
    refused = sum(not decision for decision, _ in compared)
    admitted_genuine = sum(decision and genuine for decision, genuine in compared)
    return {
        "status": "LEVEL1_AUDITED",
        "bridge_source": bridge_source,
        "gate_decisions": decisions,
        "evaluated_attempt_count": evaluated,
        "false_accept_count": false_accepts,
        "false_reject_count": false_rejects,
        "calibration_error_rate": (false_accepts + false_rejects) / evaluated,
        "sorting_cost": evaluated,
        "refusal_count": refused,
        "refused_le_sorting_cost": refused <= evaluated,
        "cost_per_admitted_genuine_attempt": evaluated / admitted_genuine if admitted_genuine else None,
    }


def rubber_stamp_attempts() -> tuple[dict[str, Any], ...]:
    return tuple({**attempt, "receipt_read": True} for attempt in ATTEMPTS)


def run(output: Path) -> dict[str, Any]:
    output.mkdir(parents=True, exist_ok=True)
    result = {
        "protocol": "closure_native_level1_genuineness_v1",
        "calibrated_gate": audit_gate(ATTEMPTS, bridge_source="independent_observer"),
        "rubber_stamp_control": audit_gate(rubber_stamp_attempts(), bridge_source="independent_observer"),
        "missing_bridge_control": audit_gate(ATTEMPTS, bridge_source="absent"),
        "self_certification_control": audit_gate(ATTEMPTS, bridge_source="gate_verdict"),
        "claim_boundary": "bounded signal-audit control; no claim that the Level-1 observer identifies real-world genuineness",
    }
    (output / "closure_native_level1_genuineness.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return result


if __name__ == "__main__":
    run(Path("runs/closure_native_level1_genuineness"))
