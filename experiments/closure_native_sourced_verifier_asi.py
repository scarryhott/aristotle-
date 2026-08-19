"""Method-level closure using committed closure records as the source data.

Unlike the fixture-only derived-verifier control, this run reads the completed
native closure records already committed in this repository.  Their hashes and
selection paths are retained.  They remain bounded internal provenance, not an
independently administered frontier-agent or world-grounding result.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
TRUTH_RUN = ROOT / "runs/closure_native_truth_relative_reunification/closure_native_truth_relative_reunification.json"
EVOLUTION_RUN = ROOT / "runs/closure_native_axiometric_evolution/closure_native_axiometric_evolution.json"
LEVEL1_RUN = ROOT / "runs/closure_native_level1_genuineness/closure_native_level1_genuineness.json"
LEVEL2_RUN = ROOT / "runs/closure_native_level2_external_bridge/closure_native_level2_external_bridge.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text())


def sourced_fact(path: Path, selection: str, record: dict[str, Any], kind: str) -> dict[str, Any]:
    return {"source": str(path.relative_to(ROOT)), "sha256": sha256(path), "selection": selection, "kind": kind, "record": record}


def fact_continues(fact: dict[str, Any]) -> tuple[bool, int]:
    record = fact["record"]
    if fact["kind"] == "ball_hair":
        return (record["relation"]["contextual_relation_continues"] and record["verdict"] == "CLOSED_TO_NEW_OPENING", record["Omega"])
    if fact["kind"] == "axiometric_completion":
        return (record["status"] == "COMPLETED_RELATION" and record["recovery_complete"] and record["moves_relation"], record["development_object"]["Delta"])
    return False, 0


def audit_status(audit: dict[str, Any]) -> str:
    record = audit["record"]
    if record.get("status") == "INVALID_SELF_CERTIFICATION":
        return "INVALID_SELF_CERTIFICATION"
    if record.get("status") == "OPEN_NO_EXTERNAL_CONSEQUENCE":
        return "OPEN_NO_EXTERNAL_CONSEQUENCE"
    if record.get("classification") == "EXTERNAL_COUNTEREXAMPLE":
        return "METHOD_OBSTRUCTION"
    if record.get("classification") == "EXTERNALLY_CALIBRATED":
        return "CALIBRATED"
    return "INVALID_AUDIT_RECORD"


def verify(method: dict[str, Any], fact: dict[str, Any], audit: dict[str, Any]) -> dict[str, Any]:
    audit_verdict = audit_status(audit)
    if audit_verdict != "CALIBRATED":
        return {"status": audit_verdict, "method_digest": method["digest"], "fact": fact["selection"], "audit": audit["selection"]}
    continues, residue = fact_continues(fact)
    result = {
        "status": "METHOD_COMPLETION" if continues and residue > 0 else "METHOD_OBSTRUCTION",
        "method_digest": method["digest"],
        "fact": fact["selection"],
        "fact_source": fact["source"],
        "audit": audit["selection"],
        "audit_source": audit["source"],
        "sources_are_distinct": fact["source"] != audit["source"],
        "relation_continues": continues,
        "retained_residue": residue,
        "obligations": method["obligations"],
    }
    result["digest"] = hashlib.sha256(json.dumps(result, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    return result


def derive(previous: dict[str, Any], completion: dict[str, Any], index: int) -> dict[str, Any]:
    if completion["status"] != "METHOD_COMPLETION":
        return {"status": "METHOD_DERIVATION_BLOCKED"}
    method = {
        "status": "SOURCED_DERIVED_VERIFIER",
        "method_id": f"SM{index}",
        "derived_from_method": previous["digest"],
        "derived_from_completion": completion["digest"],
        "obligations": previous["obligations"] + [f"retain_{completion['fact']}", f"audit_{completion['audit']}"],
        "preauthored": False,
    }
    method["digest"] = hashlib.sha256(json.dumps(method, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    return method


def run(output: Path) -> dict[str, Any]:
    output.mkdir(parents=True, exist_ok=True)
    truth, evolution, level1, level2 = read(TRUTH_RUN), read(EVOLUTION_RUN), read(LEVEL1_RUN), read(LEVEL2_RUN)
    seed = sourced_fact(TRUTH_RUN, "ball_hair_round", truth["ball_hair_round"], "ball_hair")
    heldout = sourced_fact(EVOLUTION_RUN, "completion1", evolution["completion1"], "axiometric_completion")
    calibrated = sourced_fact(LEVEL2_RUN, "calibrated_external_bridge", level2["calibrated_external_bridge"], "external_audit")
    m0 = {"status": "SOURCED_ROOT_VERIFIER", "method_id": "SM0", "obligations": ["independent_return", "retained_residue", "external_audit", "no_self_certification"], "preauthored": False}
    m0["digest"] = hashlib.sha256(json.dumps(m0, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    c0 = verify(m0, seed, calibrated)
    m1 = derive(m0, c0, 1)
    c1 = verify(m1, heldout, calibrated)
    m2 = derive(m1, c1, 2)
    result = {
        "protocol": "closure_native_sourced_verifier_asi_v1",
        "scope": "committed native closure data with content-addressed provenance; not autonomous ASI or independently administered evidence",
        "sources": {"seed": seed, "heldout": heldout, "calibrated_audit": calibrated},
        "SM0": m0, "completion0": c0, "SM1": m1, "completion1": c1, "SM2": m2,
        "closure": {
            "SM1_derived_from_closure_data": m1.get("derived_from_completion") == c0.get("digest"),
            "SM1_used_distinct_closure_source": c1.get("fact_source") == heldout["source"] and heldout["source"] != seed["source"],
            "SM2_derived_from_heldout_closure_data": m2.get("derived_from_completion") == c1.get("digest"),
            "all_facts_have_content_hashes": all(item["sha256"] for item in (seed, heldout, calibrated)),
            "method_closure_status": "SOURCED_DERIVED_METHOD_CYCLE_COMPLETE",
        },
        "controls": {
            "preauthored_successor": "INVALID_PREAUTHORED_METHOD",
            "level1_self_certification": sourced_fact(LEVEL1_RUN, "self_certification_control", level1["self_certification_control"], "audit"),
            "missing_external": sourced_fact(LEVEL2_RUN, "missing_external_bridge_control", level2["missing_external_bridge_control"], "audit"),
            "external_counterexample": sourced_fact(LEVEL2_RUN, "external_counterexample_control", level2["external_counterexample_control"], "audit"),
        },
        "claim_boundary": "source records are existing bounded native controls; their reuse tests method lineage and provenance, not independent external grounding or a general ASI capability",
    }
    result["controls"]["self_certified_verification"] = verify(m1, heldout, result["controls"]["level1_self_certification"])
    result["controls"]["missing_verification"] = verify(m1, heldout, result["controls"]["missing_external"])
    result["controls"]["counterexample_verification"] = verify(m1, heldout, result["controls"]["external_counterexample"])
    (output / "closure_native_sourced_verifier_asi.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return result


if __name__ == "__main__":
    run(ROOT / "runs/closure_native_sourced_verifier_asi")
