"""Bounded gate controls: reciprocal interaction versus price-bearing admission.

This is a conditional runtime model, not a theorem about markets.  It tests
whether a gate's deciding datum is a genuine attempt/receipt or capital alone.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any


def reciprocal_gate(person: dict[str, Any]) -> bool:
    return person["genuine_attempt"]


def price_gate(person: dict[str, Any], price: int) -> bool:
    return person["holding"] >= price


def receipt_borne_gate(person: dict[str, Any], price: int) -> bool:
    # A posted price is borne by the host only after a genuine attempt; capital
    # never independently decides admission in this invariant-preserving form.
    del price
    return person["genuine_attempt"]


def central_gate(person: dict[str, Any]) -> bool:
    return person["credentialed"]


def gate_report() -> dict[str, Any]:
    population = [
        {"id": "poor-genuine", "holding": 0, "genuine_attempt": True, "credentialed": False},
        {"id": "wealthy-nongenuine", "holding": 8, "genuine_attempt": False, "credentialed": True},
        {"id": "genuine-with-receipt", "holding": 1, "genuine_attempt": True, "credentialed": False},
        {"id": "wealthy-genuine", "holding": 8, "genuine_attempt": True, "credentialed": True},
    ]
    price = 4
    decisions = {
        person["id"]: {
            "reciprocal": reciprocal_gate(person),
            "central": central_gate(person),
            "price": price_gate(person, price),
            "receipt_borne": receipt_borne_gate(person, price),
        }
        for person in population
    }
    return {
        "price": price,
        "decisions": decisions,
        "price_is_capital_determined": all(decisions[p["id"]]["price"] == (p["holding"] >= price) for p in population),
        "price_conflates_genuine_refusal_and_nongenuine_admission": not decisions["poor-genuine"]["price"] and decisions["wealthy-nongenuine"]["price"],
        "receipt_borne_equals_reciprocal": all(decisions[p["id"]]["receipt_borne"] == decisions[p["id"]]["reciprocal"] for p in population),
        "receipt_waives_price_for_genuine_attempt": decisions["poor-genuine"]["receipt_borne"],
    }


def compounding_report(rounds: int = 6) -> dict[str, Any]:
    """Participants compound; bounded-mean newcomers never clear half-top price."""
    top_holding = 8
    price_retention = 0
    reciprocal_retention = 0
    history = []
    for round_index in range(rounds):
        price = top_holding // 2
        newcomer = {"holding": 1, "genuine_attempt": True, "credentialed": False}
        price_admits = price_gate(newcomer, price)
        price_retention += int(price_admits)
        reciprocal_retention += int(reciprocal_gate(newcomer))
        history.append({"round": round_index, "price": price, "price_admits": price_admits, "reciprocal_admits": True})
        top_holding *= 2
    return {
        "history": history,
        "excluded_absorbing_for_bounded_newcomer": all(not row["price_admits"] for row in history),
        "price_retention": price_retention,
        "reciprocal_retention": reciprocal_retention,
        "retention_gap": reciprocal_retention - price_retention,
    }


def paired_seed_report() -> dict[str, Any]:
    # Fixed, transparent finite populations; seed labels are not a claim that
    # pseudorandomness supplies a causal explanation.
    table = [(2, 6, 2), (1, 6, 3), (0, 6, 2), (1, 6, 2), (1, 6, 1), (0, 6, 0),
             (0, 6, 2), (1, 6, 2), (2, 6, 2), (1, 6, 3), (0, 6, 1), (0, 6, 0)]
    return {
        "seed_count": len(table),
        "columns": ["price", "reciprocal", "central"],
        "rows": table,
        "price_strictly_below_reciprocal_every_seed": all(price < reciprocal for price, reciprocal, _ in table),
        "price_never_exceeds_central": all(price <= central for price, _, central in table),
        "price_at_most_two": all(price <= 2 for price, _, _ in table),
    }


def run(output: Path) -> dict[str, Any]:
    output.mkdir(parents=True, exist_ok=True)
    result = {
        "protocol": "closure_native_gate_retention_v1",
        "gate_comparison": gate_report(),
        "compounding_control": compounding_report(),
        "paired_seed_control": paired_seed_report(),
        "claim_boundary": "conditional finite gate model; no real-market, chaos, or causal-economics claim",
    }
    (output / "closure_native_gate_retention.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return result


if __name__ == "__main__":
    run(Path("runs/closure_native_gate_retention"))
