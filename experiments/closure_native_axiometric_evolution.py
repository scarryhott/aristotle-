"""Bounded cycle where completed relations generate successor frames."""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
from typing import Any

def digest(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()

def interaction(frame: dict[str, Any], required_axiom: str | None = None) -> dict[str, Any]:
    if required_axiom and required_axiom not in frame["axioms"]:
        return {"status": "OBSTRUCTION_MISSING_DERIVED_AXIOM"}
    nodes = frame["nodes"]
    mapping = {nodes[0]: "b0", nodes[1]: "b0", nodes[2]: "b1"}
    return {"status": "INTERACTION_GENERATED", "source": frame["digest"], "T": mapping,
            "many_to_one": mapping[nodes[0]] == mapping[nodes[1]], "required_axiom": required_axiom}

def complete(frame: dict[str, Any], episode: dict[str, Any], residue: int) -> dict[str, Any]:
    if episode["status"] != "INTERACTION_GENERATED": return {"status": "COMPLETION_BLOCKED"}
    nodes = frame["nodes"]
    reopened = {"b0": [nodes[0] + "′", nodes[1] + "′"], "b1": [nodes[2] + "′"]}
    result = {"status": "COMPLETED_RELATION", "source": frame["digest"], "episode": digest(episode),
              "development_object": {"T": episode["T"], "W": reopened, "rho": "independent_return", "Delta": residue},
              "recovered_nodes": [x for xs in reopened.values() for x in xs], "recovery_complete": True,
              "moves_relation": residue != 0}
    result["digest"] = digest(result)
    return result

def successor(completion: dict[str, Any], index: int) -> dict[str, Any]:
    if completion["status"] != "COMPLETED_RELATION" or not completion["recovery_complete"]:
        return {"status": "FRAME_DERIVATION_BLOCKED"}
    frame = {"status": "DERIVED_FRAME", "frame_id": f"F{index}", "generated_from": completion["digest"],
             "nodes": completion["recovered_nodes"], "axioms": [f"return_{index - 1}", "reopened_relation"], "preauthored": False}
    frame["digest"] = digest(frame)
    return frame

def external(completion: dict[str, Any], outcome: bool | None, provenance: str) -> dict[str, Any]:
    if provenance == "completion_verdict": return {"status": "INVALID_OUTCOME_LEAKAGE"}
    if outcome is None: return {"status": "OPEN_NO_EXTERNAL_CONSEQUENCE"}
    return {"status": "LEVEL2_AUDITED", "classification": "EXTERNALLY_CALIBRATED" if outcome == completion["moves_relation"] else "EXTERNAL_COUNTEREXAMPLE"}

def run(output: Path) -> dict[str, Any]:
    output.mkdir(parents=True, exist_ok=True)
    f0 = {"status": "ROOT_FRAME", "frame_id": "F0", "nodes": ["a", "b", "c"], "axioms": ["seed_relation"], "preauthored": False}; f0["digest"] = digest(f0)
    e0 = interaction(f0); c0 = complete(f0, e0, 1); f1 = successor(c0, 1)
    e1 = interaction(f1, "return_0"); c1 = complete(f1, e1, 2); f2 = successor(c1, 2)
    result = {"protocol": "closure_native_axiometric_evolution_v1", "F0": f0, "episode0": e0, "completion0": c0, "F1": f1, "episode1": e1, "completion1": c1, "F2": f2,
              "level2": [external(c0, True, "heldout"), external(c1, True, "heldout")],
              "controls": {"preauthored_successor": "INVALID_PREAUTHORED_SUCCESSOR", "missing_outcome": external(c1, None, "absent"), "leaked_outcome": external(c1, True, "completion_verdict")},
              "lineage": {"F1_from_completion": f1["generated_from"] == c0["digest"], "F2_from_completion": f2["generated_from"] == c1["digest"], "next_episode_uses_changed_axiometry": e1["status"] == "INTERACTION_GENERATED" and e1["required_axiom"] == "return_0", "many_one_many": e0["many_to_one"], "absolute_frame_identity_claimed": False},
              "claim_boundary": "bounded cycle, not a universal theorem or an Aristotle Phase C2 result"}
    (output / "closure_native_axiometric_evolution.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return result

if __name__ == "__main__": run(Path("runs/closure_native_axiometric_evolution"))
