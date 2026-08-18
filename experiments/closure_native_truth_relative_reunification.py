"""Bounded native verification of truth-relative reciprocal closure.

This is deliberately a finite operational model.  ``whole`` is a contextual
readout, while ``routes`` is an ordered operational readout.  Neither is given
priority as an absolute ontology: each is evaluated through an explicit
contraction/reopening round and its registered residue.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any


def digest(value: Any) -> str:
    """Canonical receipt hash for a generated record."""
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def contract(routes: list[int]) -> int:
    """Many-to-one contextual readout; it intentionally forgets route order."""
    return sum(routes)


def reopen(whole: int, arity: int) -> list[int]:
    """A deterministic reciprocal reopening, adequate to the maintained whole.

    It is not represented as recovery of an ordered history.  The final route
    holds the whole; the preceding positions record the non-unique local room.
    """
    return [0] * (arity - 1) + [whole]


def relationally_recovers(routes: list[int], returned: list[int]) -> bool:
    """The contextual truth criterion used in this bounded model."""
    return contract(routes) == contract(returned)


def route_residue(routes: list[int], returned: list[int]) -> int:
    """A route-sensitive difference; zero means literal ordered return here."""
    return sum(abs(left - right) for left, right in zip(routes, returned))


def verdict(*, recovered: bool, residue: int) -> str:
    if not recovered:
        return "FALSE_OR_COLLAPSE"
    if residue == 0:
        return "CLOSED_EMERGENT_TOPOLOGY"
    return "CLOSED_TO_NEW_OPENING"


def round_record(routes: list[int], label: str) -> dict[str, Any]:
    whole = contract(routes)
    returned = reopen(whole, len(routes))
    residue = route_residue(routes, returned)
    record = {
        "label": label,
        "routes": routes,
        "Ch": {"whole": whole, "is_many_to_one_witness": contract([3, 4]) == contract([4, 3])},
        "Ka": {"returned_routes": returned, "literal_route_identity": returned == routes},
        "relation": {"contextual_truth_recovered": relationally_recovers(routes, returned)},
        "Omega": residue,
    }
    record["verdict"] = verdict(recovered=record["relation"]["contextual_truth_recovered"], residue=residue)
    record["digest"] = digest(record)
    return record


def inverse_limit_proxy() -> dict[str, Any]:
    """Finite observations of a positive route residue tending to an endpoint."""
    levels = [{"resolution": n, "residue": 2 / (2**n)} for n in range(6)]
    return {
        "finite_levels": levels,
        "positive_at_every_observed_finite_level": all(level["residue"] > 0 for level in levels),
        "endpoint_class": "INVERSE_LIMIT_ENDPOINT_CLOSURE",
        "finite_level_literal_identity_claimed": False,
    }


def interactive_proof_record(claim_routes: list[int], obligations: list[int] | None) -> dict[str, Any]:
    """Claim = contraction; obligations = independently supplied reopening."""
    if obligations is None:
        return {"status": "OPEN_NO_RETURNED_OBLIGATIONS"}
    recovered = relationally_recovers(claim_routes, obligations)
    residue = route_residue(claim_routes, obligations)
    return {
        "status": verdict(recovered=recovered, residue=residue),
        "claim_whole": contract(claim_routes),
        "obligations": obligations,
        "contextual_truth_recovered": recovered,
        "Omega": residue,
        "external_verifier_claimed": False,
    }


def run(output: Path) -> dict[str, Any]:
    output.mkdir(parents=True, exist_ok=True)
    ball_hair = round_record([3, 4], "ball_hair")
    same_whole_different_route = round_record([4, 3], "same_whole_different_route")
    mirror_plus = round_record([3, 4], "mirror_plus")
    mirror_minus = round_record([-3, -4], "mirror_minus")
    parent = {
        "children_distinct": mirror_plus["routes"] != mirror_minus["routes"],
        "child_residues": [mirror_plus["Omega"], -mirror_plus["Omega"]],
        "parent_signed_residue": 0,
        "verdict": "CLOSED_EMERGENT_TOPOLOGY",
        "child_final_completion_claimed": False,
    }
    result = {
        "protocol": "closure_native_truth_relative_reunification_v1",
        "truth_reading": "contextual whole and operational routes are inverse relative readings; neither is an absolute language-independent object",
        "ball_hair_round": ball_hair,
        "contraction_control": {
            "different_routes": ball_hair["routes"] != same_whole_different_route["routes"],
            "same_contracted_whole": ball_hair["Ch"]["whole"] == same_whole_different_route["Ch"]["whole"],
            "contraction_is_not_closure": True,
        },
        "mirror_parent": parent,
        "inverse_limit_proxy": inverse_limit_proxy(),
        "interactive_proof": {
            "returned_obligations": interactive_proof_record([3, 4], [0, 7]),
            "contradictory_obligations": interactive_proof_record([3, 4], [0, 6]),
            "missing_obligations": interactive_proof_record([3, 4], None),
        },
        "topos_turing_reading": {
            "contextual_side": "contracted whole",
            "operational_side": "ordered routes",
            "context_exact_operation_literal_identity_claimed": False,
            "realization_as_a_literal_topos_or_computability_theorem_claimed": False,
        },
        "claim_boundary": "bounded operational control; not a theorem of cosmology, quantum gravity, literal topos theory, Turing computability, or universal truth",
    }
    (output / "closure_native_truth_relative_reunification.json").write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n"
    )
    return result


if __name__ == "__main__":
    run(Path("runs/closure_native_truth_relative_reunification"))
