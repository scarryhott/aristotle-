"""Bounded Level-2 audit: receipts versus independently held-out consequences.

The external outcome fixture is deliberately separate from the gate verdict.
Its absence yields OPEN; any declared dependence on the verdict invalidates the
test rather than counting as supporting evidence.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any


def audit(records: tuple[dict[str, Any], ...], *, outcome_provenance: str) -> dict[str, Any]:
    if outcome_provenance == "gate_decision":
        return {
            "status": "INVALID_OUTCOME_LEAKAGE",
            "reason": "external consequence was generated from the gate decision",
        }
    if any(record["external_outcome"] is None for record in records):
        return {
            "status": "OPEN_NO_EXTERNAL_CONSEQUENCE",
            "known_outcome_count": sum(record["external_outcome"] is not None for record in records),
        }
    compared = [(record["gate_accepts"], record["external_outcome"]) for record in records]
    false_accepts = sum(accepted and not outcome for accepted, outcome in compared)
    false_rejects = sum(not accepted and outcome for accepted, outcome in compared)
    result = {
        "status": "LEVEL2_AUDITED",
        "outcome_provenance": outcome_provenance,
        "heldout_record_count": len(records),
        "false_accept_count": false_accepts,
        "false_reject_count": false_rejects,
        "external_calibration_error_rate": (false_accepts + false_rejects) / len(records),
        "supports_level1_calibration": false_accepts == 0 and false_rejects == 0,
    }
    if false_accepts or false_rejects:
        result["classification"] = "EXTERNAL_COUNTEREXAMPLE"
    else:
        result["classification"] = "EXTERNALLY_CALIBRATED"
    return result


def run(output: Path) -> dict[str, Any]:
    output.mkdir(parents=True, exist_ok=True)
    calibrated = (
        {"id": "h0", "gate_accepts": True, "external_outcome": True},
        {"id": "h1", "gate_accepts": False, "external_outcome": False},
        {"id": "h2", "gate_accepts": True, "external_outcome": True},
        {"id": "h3", "gate_accepts": False, "external_outcome": False},
    )
    counterexample = (
        {"id": "h0", "gate_accepts": True, "external_outcome": True},
        {"id": "h1", "gate_accepts": True, "external_outcome": False},
    )
    missing = (
        {"id": "h0", "gate_accepts": True, "external_outcome": None},
        {"id": "h1", "gate_accepts": False, "external_outcome": None},
    )
    result = {
        "protocol": "closure_native_level2_external_bridge_v1",
        "calibrated_external_bridge": audit(calibrated, outcome_provenance="heldout_outcome_fixture"),
        "external_counterexample_control": audit(counterexample, outcome_provenance="heldout_outcome_fixture"),
        "missing_external_bridge_control": audit(missing, outcome_provenance="absent"),
        "outcome_leakage_control": audit(calibrated, outcome_provenance="gate_decision"),
        "claim_boundary": "bounded held-out fixture; no claim that these outcomes ground a real-world receipt",
    }
    (output / "closure_native_level2_external_bridge.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return result


if __name__ == "__main__":
    run(Path("runs/closure_native_level2_external_bridge"))
