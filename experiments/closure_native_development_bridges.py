"""Bounded native controls for translating development levels.

They operationalize the NRRF653 diagnosis without importing its external Lean
source: recovery is insufficient, bridges compose, and an asserted primitive
is not automatically a translated consequence.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any


def round_report(states: list[int], round_map: dict[int, int], relation: dict[int, int]) -> dict[str, Any]:
    """A round is translating only if it recovers and genuinely moves a state."""
    recovers = all(relation[round_map[state]] == relation[state] for state in states)
    moves = any(round_map[state] != state for state in states)
    return {
        "recovers_every_state_in_local_relation": recovers,
        "moves_some_presentation": moves,
        "classification": "TRANSLATING" if recovers and moves else "FROZEN_OR_NONTRANSLATING",
    }


def bridge_report() -> dict[str, Any]:
    """Two injective/reflection-preserving bridges compose to a global return."""
    level0 = [0, 1]
    bridge01 = {0: 10, 1: 11}
    bridge12 = {10: 20, 11: 21}
    return12 = {20: 0, 21: 1}
    composed = {state: bridge12[bridge01[state]] for state in level0}
    return {
        "bridge01_injective": len(set(bridge01.values())) == len(level0),
        "bridge12_injective": len(set(bridge12.values())) == len(bridge01),
        "bridge_chain": composed,
        "global_return_of_level0": {state: return12[composed[state]] for state in level0},
        "global_return_is_identity_on_earlier_level": all(return12[composed[state]] == state for state in level0),
        "absolute_carrier_identity_claimed": False,
    }


def syntactic_translation_report() -> dict[str, Any]:
    """Separate asserting a new primitive from interpreting it as a base consequence."""
    base_consequences = {"q"}
    asserted_next_axiom = "p"
    identity_substitution = {"p": "p"}
    genuine_interpretation = {"p": "q"}
    return {
        "asserted_axiom_is_derived_in_base": asserted_next_axiom in base_consequences,
        "countermodel": {"p": False, "q": True},
        "identity_substitution_is_interpretation": identity_substitution["p"] in base_consequences,
        "genuine_substitution_is_interpretation": genuine_interpretation["p"] in base_consequences,
        "translation_transfers_new_axiom_to_base_consequence": genuine_interpretation["p"] in base_consequences,
    }


def run(output: Path) -> dict[str, Any]:
    output.mkdir(parents=True, exist_ok=True)
    frozen = round_report([0, 1], {0: 0, 1: 1}, {0: 0, 1: 1})
    translating = round_report([0, 1], {0: 1, 1: 0}, {0: 0, 1: 0})
    result = {
        "protocol": "closure_native_development_bridges_v1",
        "recovery_test_blind": frozen["recovers_every_state_in_local_relation"] and translating["recovers_every_state_in_local_relation"],
        "frozen_round": frozen,
        "translating_round": translating,
        "bridge_composition": bridge_report(),
        "syntactic_axiometry": syntactic_translation_report(),
        "claim_boundary": "bounded runtime controls; not a local rebuild of NRRF653 or an audit of earlier Lean modules",
    }
    (output / "closure_native_development_bridges.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return result


if __name__ == "__main__":
    run(Path("runs/closure_native_development_bridges"))
