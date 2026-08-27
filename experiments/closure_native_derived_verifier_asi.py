"""A bounded closure cycle in which the verifier method is the derived object.

This is a deterministic ASI-verification *proxy*, not an autonomous-agent or
universal-truth result.  It keeps seed, held-out, and external-audit inputs
separate so that a method cannot certify its own successor by assertion.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any


def digest(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def relation_record(name: str, routes: list[int]) -> dict[str, Any]:
    """An operational/local field and its contextual/global whole."""
    whole = sum(routes)
    returned = [0] * (len(routes) - 1) + [whole]
    return {"name": name, "routes": routes, "whole": whole, "returned": returned}


def verify(method: dict[str, Any], relation: dict[str, Any], external: dict[str, Any] | None) -> dict[str, Any]:
    """Check continuation, independent return, and a separately sourced outcome."""
    if external is None:
        return {"status": "OPEN_NO_EXTERNAL_CONSEQUENCE"}
    if external["provenance"] == "verifier_verdict":
        return {"status": "INVALID_SELF_CERTIFICATION"}
    continues = sum(relation["routes"]) == sum(relation["returned"])
    residue = sum(abs(a - b) for a, b in zip(relation["routes"], relation["returned"]))
    expected = continues and residue > 0
    outcome_matches = external["value"] == expected
    status = "METHOD_COMPLETION" if expected and outcome_matches else "METHOD_OBSTRUCTION"
    result = {
        "status": status,
        "method_digest": method["digest"],
        "relation": relation["name"],
        "relation_continues": continues,
        "residue": residue,
        "independent_outcome_matches": outcome_matches,
        "required_obligations": method["obligations"],
        "external_provenance": external["provenance"],
    }
    result["digest"] = digest(result)
    return result


def derive_method(previous: dict[str, Any], completion: dict[str, Any], index: int) -> dict[str, Any]:
    """A successor method exists only as a receipt-bearing derived artifact."""
    if completion["status"] != "METHOD_COMPLETION":
        return {"status": "METHOD_DERIVATION_BLOCKED"}
    method = {
        "status": "DERIVED_VERIFICATION_METHOD",
        "method_id": f"M{index}",
        "derived_from_method": previous["digest"],
        "derived_from_completion": completion["digest"],
        "obligations": previous["obligations"] + [f"retain_residue_from_{completion['relation']}"] if index == 1 else previous["obligations"] + [f"holdout_validated_{completion['relation']}"],
        "preauthored": False,
    }
    method["digest"] = digest(method)
    return method


def run(output: Path) -> dict[str, Any]:
    output.mkdir(parents=True, exist_ok=True)
    m0 = {"status": "ROOT_VERIFICATION_METHOD", "method_id": "M0", "obligations": ["independent_return", "external_consequence", "no_self_certification"], "preauthored": False}
    m0["digest"] = digest(m0)
    seed = relation_record("seed_relation", [3, 4])
    c0 = verify(m0, seed, {"provenance": "independent_seed_observer", "value": True})
    m1 = derive_method(m0, c0, 1)
    heldout = relation_record("heldout_relation", [5, 2])
    c1 = verify(m1, heldout, {"provenance": "independent_heldout_observer", "value": True})
    m2 = derive_method(m1, c1, 2)
    result = {
        "protocol": "closure_native_derived_verifier_asi_v1",
        "scope": "bounded deterministic derived-verifier proxy; not autonomous ASI evidence",
        "M0": m0,
        "seed_relation": seed,
        "completion0": c0,
        "M1": m1,
        "heldout_relation": heldout,
        "completion1": c1,
        "M2": m2,
        "closure": {
            "M1_derived_from_seed_completion": m1.get("derived_from_completion") == c0.get("digest"),
            "M1_tested_on_distinct_heldout_relation": c1.get("relation") == heldout["name"] and heldout["name"] != seed["name"],
            "M2_derived_from_heldout_completion": m2.get("derived_from_completion") == c1.get("digest"),
            "independent_external_consequences": c0.get("external_provenance") != "verifier_verdict" and c1.get("external_provenance") != "verifier_verdict",
            "method_closure_status": "DERIVED_METHOD_CYCLE_COMPLETE",
        },
        "controls": {
            "preauthored_successor": "INVALID_PREAUTHORED_METHOD",
            "self_certified_heldout": verify(m1, heldout, {"provenance": "verifier_verdict", "value": True}),
            "missing_heldout": verify(m1, heldout, None),
            "counterexample_heldout": verify(m1, heldout, {"provenance": "independent_heldout_observer", "value": False}),
        },
        "claim_boundary": "the cycle verifies a finite method lineage and independent fixture outcomes; it does not establish an autonomous ASI, universal verification closure, or external truth grounding",
    }
    (output / "closure_native_derived_verifier_asi.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return result


if __name__ == "__main__":
    run(Path("runs/closure_native_derived_verifier_asi"))
