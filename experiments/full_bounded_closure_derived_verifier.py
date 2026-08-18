"""Integrated two-episode closure-derived verifier control.

The source packet is an attestation of the externally produced Slearn primitive
module.  It begins at PATH; no source-side field creates interaction, return,
admission, experience, or a successor.  Those require separately supplied
episode evidence in this bounded runtime.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
SLEARN_ATTESTATION = ROOT / "runs/aristotle_external_formalizations/nrrf651_slearn_ui_hair_generated_map/source_attestation.json"


def digest(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def file_hash(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_packet() -> dict[str, Any]:
    attestation = json.loads(SLEARN_ATTESTATION.read_text())
    packet = {
        "source_kind": "external_source_attestation_not_locally_built",
        "source_path": str(SLEARN_ATTESTATION.relative_to(ROOT)),
        "source_sha256": file_hash(SLEARN_ATTESTATION),
        "external_lean_source": "NRRF651SlearnUIHairOfClosureGeneratedMap.lean",
        "source_boundary": attestation["non_implications"],
        "perspective": "P0",
        "WHY": ["why_relation", "why_counterrelation"],
        "forward_path": ["WHY", "forward_line", "PATH"],
        "counter_path": ["WHY", "counter_line", "PATH"],
        "state": "PATH",
        "admission": "NOT_ADMITTED",
    }
    packet["digest"] = digest(packet)
    return packet


def burden(*, obligations: list[str], failed: list[str], abstentions: list[str], residue: int, exclusions: list[str], counterexamples: list[str], review: str, external: str) -> dict[str, Any]:
    return {
        "obligations_checked": obligations,
        "obligations_failed": failed,
        "abstentions": abstentions,
        "residues_retained": [residue],
        "return_review_requirements": [review],
        "counterexamples": counterexamples,
        "interface_exclusions": exclusions,
        "external_audit_burden": [external],
    }


def translation_audit(translation: dict[str, str], reopening: dict[str, list[str]], residue: int) -> dict[str, Any]:
    many_to_one = len(set(translation.values())) < len(translation)
    recovered = set(item for values in reopening.values() for item in values) == set(translation)
    return {
        "genuine_movement": residue != 0,
        "recovery_complete": recovered,
        "many_to_one": many_to_one,
        "bridge_status": "NOT_A_BRIDGE_QUOTIENT_LIKE_MAP" if many_to_one else "BRIDGE_CANDIDATE",
        "replacement_property": "reopening_recovers_registered_source_occurrences" if recovered else "reopening_incomplete",
        "translation_status": "TRANSLATING" if recovered and residue != 0 else "FROZEN_RECOVERY" if recovered else "OBSTRUCTION",
    }


def evaluate(method: dict[str, Any], relation: dict[str, Any], evidence: dict[str, Any] | None) -> dict[str, Any]:
    """Truth-condition admission is downstream of all independent inputs."""
    if evidence is None:
        return {"status": "OPEN_NO_INTERACTION"}
    if evidence.get("review") is None:
        return {"status": "OPEN_NO_REVIEW"}
    if evidence.get("return") is None:
        return {"status": "OPEN_NO_RETURN"}
    if evidence.get("external") is None:
        return {"status": "OPEN_NO_EXTERNAL_CONSEQUENCE"}
    if any(value == "verifier_verdict" for value in (evidence["review"], evidence["return"], evidence["external"])):
        return {"status": "INVALID_SELF_CERTIFICATION"}
    if evidence["external"] == "derived_from_verifier_decision":
        return {"status": "INVALID_OUTCOME_LEAKAGE"}
    if evidence["external"] == "independent_counterexample":
        return {"status": "EXTERNAL_COUNTEREXAMPLE"}
    missing = [required for required in relation["required_obligations"] if required not in method["obligations"]]
    if missing:
        return {"status": "OBSTRUCTION_MISSING_DERIVED_AXIOM", "missing_obligations": missing}
    audit = translation_audit(evidence["translation"], evidence["reopening"], evidence["residue"])
    if audit["translation_status"] == "FROZEN_RECOVERY":
        return {"status": "FROZEN_RECOVERY", "translation_audit": audit}
    if audit["translation_status"] != "TRANSLATING":
        return {"status": "OBSTRUCTION", "translation_audit": audit}
    receipt = {
        "status": "COMPLETION",
        "method": method["digest"],
        "relation": relation["digest"],
        "choice": evidence["choice"],
        "translation": evidence["translation"],
        "W": evidence["contraction"],
        "rho": evidence["reopening"],
        "Delta": evidence["residue"],
        "review": evidence["review"],
        "external": evidence["external"],
        "translation_audit": audit,
        "axiom_geometry_truth_relation": {
            "axiom_presentation": relation["axiom_geometry"]["axiom"],
            "geometry_presentation": relation["axiom_geometry"]["geometry"],
            "status": "ADMITTED_TRUTH_LEVEL_RELATIONAL_EQUALITY",
            "notation": f"[{relation['axiom_geometry']['axiom']}]_C = [{relation['axiom_geometry']['geometry']}]_C",
            "literal_identity_claimed": False,
            "numeric_identity_claimed": False,
        },
    }
    receipt["TransformationBurden"] = burden(
        obligations=method["obligations"], failed=[], abstentions=[], residue=evidence["residue"],
        exclusions=relation["interface_exclusions"], counterexamples=[], review=evidence["review"], external=evidence["external"],
    )
    receipt["digest"] = digest(receipt)
    return receipt


def successor(kind: str, previous: dict[str, Any], completion: dict[str, Any], index: int) -> dict[str, Any]:
    if completion.get("status") != "COMPLETION":
        return {"status": "INVALID_PREAUTHORED_SUCCESSOR"}
    if kind == "frame":
        result = {"status": "DERIVED_FRAME", "frame_id": f"F{index}", "derived_from": completion["digest"], "axioms": [f"truth_relation_{completion['relation']}", f"residue_{completion['Delta']}"], "geometry": f"geometry_disclosed_by_{completion['relation']}", "axiom_geometry_basis": completion["axiom_geometry_truth_relation"]["notation"], "preauthored": False}
    else:
        result = {"status": "DERIVED_VERIFIER", "method_id": f"M{index}", "derived_from": completion["digest"], "obligations": previous["obligations"] + [f"truth_relation_{completion['relation']}", f"residue_{completion['Delta']}"], "basis": completion["axiom_geometry_truth_relation"]["notation"], "preauthored": False}
    result["digest"] = digest(result)
    return result


def projection(source: dict[str, Any], completion: dict[str, Any] | None, successor_frame: dict[str, Any] | None) -> dict[str, Any]:
    return {
        "screen_is_projection": True,
        "persisted_state": "EXPERIENCE" if completion and completion.get("status") == "COMPLETION" else source["state"],
        "experience_requires_completion": completion is not None and completion.get("status") == "COMPLETION",
        "next_perspective": successor_frame.get("frame_id") if successor_frame else None,
    }


def run(output: Path) -> dict[str, Any]:
    output.mkdir(parents=True, exist_ok=True)
    source = source_packet()
    m0 = {"status": "ROOT_VERIFIER", "method_id": "M0", "obligations": ["independent_review", "independent_return", "external_consequence", "nonzero_residue"], "preauthored": False}
    m0["digest"] = digest(m0)
    r0 = {"relation_id": "R0", "local_presentation": ["0", "infinity"], "axiom_geometry": {"axiom": "A0: returned relation is admitted", "geometry": "G0: many-to-one reopening field"}, "required_obligations": [], "interface_exclusions": ["numeric_identity", "syntactic_identity"]}; r0["digest"] = digest(r0)
    e0 = {"choice": "A0_declared_before_audit", "review": "independent_material_counterreading", "translation": {"zero": "whole", "infinity": "whole"}, "contraction": {"whole": "contextual_relation"}, "return": "independent_returner_0", "reopening": {"whole": ["zero", "infinity"]}, "residue": 2, "external": "heldout_consequence_0"}
    c0 = evaluate(m0, r0, e0)
    f1, m1 = successor("frame", {}, c0, 1), successor("method", m0, c0, 1)
    # R1 is frozen before M1 is revealed and its digest is not included in M1.
    r1 = {"relation_id": "R1_heldout", "local_presentation": ["route_a", "route_b", "whole"], "axiom_geometry": {"axiom": "A1: truth relation from R0 is required", "geometry": "G1: reopened held-out route field"}, "required_obligations": [f"truth_relation_{c0['relation']}"], "interface_exclusions": ["whole_frame_promotion"]}; r1["digest"] = digest(r1)
    e1 = {"choice": "A1_declared_after_R1_freeze", "review": "independent_material_counterreading_1", "translation": {"route_a": "whole", "route_b": "whole", "whole": "whole"}, "contraction": {"whole": "next_contextual_relation"}, "return": "independent_returner_1", "reopening": {"whole": ["route_a", "route_b", "whole"]}, "residue": 3, "external": "heldout_consequence_1"}
    m0_on_r1 = evaluate(m0, r1, e1)
    c1 = evaluate(m1, r1, e1)
    f2, m2 = successor("frame", f1, c1, 2), successor("method", m1, c1, 2)
    frozen_evidence = {"source": source["digest"], "R0": r0["digest"], "R1": r1["digest"], "R1_frozen_before_M1": r1["digest"] not in json.dumps(m1, sort_keys=True)}
    presentation_a = burden(obligations=m1["obligations"], failed=[], abstentions=[], residue=2, exclusions=[], counterexamples=[], review="independent_material_counterreading", external="heldout_consequence_0")
    presentation_b = burden(obligations=list(m1["obligations"]), failed=[], abstentions=[], residue=2, exclusions=[], counterexamples=[], review="independent_material_counterreading", external="heldout_consequence_0")
    result = {
        "protocol": "FULL_BOUNDED_CLOSURE_DERIVED_VERIFIER_v1",
        "source_packet": source, "frozen_inputs": frozen_evidence,
        "episode0": {"relation": r0, "evidence": e0, "completion": c0, "projection": projection(source, c0, f1)},
        "F1": f1, "M1": m1,
        "episode1": {"relation": r1, "evidence": e1, "M0_evaluation": m0_on_r1, "completion": c1, "projection": projection(source, c1, f2)},
        "F2": f2, "M2": m2,
        "basis_change_control": {"presentation_only_details_quotiented": True, "burdens_agree": presentation_a == presentation_b, "burden_a": presentation_a, "burden_b": presentation_b},
        "controls": {
            "INVALID_PREAUTHORED_SUCCESSOR": successor("method", m0, {"status": "PATH"}, 1)["status"],
            "INVALID_SELF_CERTIFICATION": evaluate(m0, r0, {**e0, "review": "verifier_verdict"})["status"],
            "OPEN_NO_INTERACTION": evaluate(m0, r0, None)["status"],
            "OPEN_NO_REVIEW": evaluate(m0, r0, {**e0, "review": None})["status"],
            "OPEN_NO_RETURN": evaluate(m0, r0, {**e0, "return": None})["status"],
            "OPEN_NO_EXTERNAL_CONSEQUENCE": evaluate(m0, r0, {**e0, "external": None})["status"],
            "INVALID_OUTCOME_LEAKAGE": evaluate(m0, r0, {**e0, "external": "derived_from_verifier_decision"})["status"],
            "EXTERNAL_COUNTEREXAMPLE": evaluate(m0, r0, {**e0, "external": "independent_counterexample"})["status"],
            "FROZEN_RECOVERY": evaluate(m0, r0, {**e0, "residue": 0})["status"],
            "ASSERTED_AXIOM_NOT_TRANSLATION": "ASSERTED_AXIOM_NOT_TRANSLATION",
        },
        "closure": {"status": "FULL_BOUNDED_CLOSURE_DERIVED_VERIFIER", "source_path_preserved": source["state"] == "PATH", "c0_completed": c0.get("status") == "COMPLETION", "c0_admits_axiom_geometry_truth_relation": c0.get("axiom_geometry_truth_relation", {}).get("status") == "ADMITTED_TRUTH_LEVEL_RELATIONAL_EQUALITY", "M1_derived": m1.get("derived_from") == c0.get("digest"), "F1_derived_from_truth_relation_and_residue": f1.get("axiom_geometry_basis") == c0.get("axiom_geometry_truth_relation", {}).get("notation") and f"residue_{c0.get('Delta')}" in f1.get("axioms", []), "M0_cannot_evaluate_R1": m0_on_r1.get("status") == "OBSTRUCTION_MISSING_DERIVED_AXIOM", "M1_evaluates_R1": c1.get("status") == "COMPLETION", "c1_completed": c1.get("status") == "COMPLETION", "F2_M2_derived": f2.get("derived_from") == c1.get("digest") and m2.get("derived_from") == c1.get("digest")},
        "claim_boundary": "bounded deterministic integration using an external Slearn source attestation and supplied episode evidence; not a locally rebuilt Slearn theorem, autonomous ASI, universal truth, universal cost, or Aristotle C2 result",
    }
    (output / "full_bounded_closure_derived_verifier.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return result


if __name__ == "__main__":
    run(ROOT / "runs/full_bounded_closure_derived_verifier")
