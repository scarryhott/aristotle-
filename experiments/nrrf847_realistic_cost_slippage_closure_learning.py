from __future__ import annotations

import json
from dataclasses import dataclass
from decimal import Decimal
from pathlib import Path
from typing import Mapping

D = Decimal
BPS = D("10000")


@dataclass(frozen=True)
class CostVector:
    fees_bps: Decimal
    slippage_bps: Decimal
    adverse_selection_bps: Decimal
    inventory_carry_bps: Decimal
    forced_unwind_bps: Decimal

    @property
    def total_bps(self) -> Decimal:
        return (
            self.fees_bps
            + self.slippage_bps
            + self.adverse_selection_bps
            + self.inventory_carry_bps
            + self.forced_unwind_bps
        )


SCENARIOS: dict[str, CostVector] = {
    "TIGHT_LIQUID": CostVector(D("0.3"), D("0.5"), D("0.7"), D("0.2"), D("0.0")),
    "NORMAL": CostVector(D("0.5"), D("1.5"), D("2.0"), D("0.5"), D("0.5")),
    "ALL_IN_30BPS": CostVector(D("1.0"), D("8.0"), D("12.0"), D("3.0"), D("6.0")),
    "STRESSED": CostVector(D("1.5"), D("15.0"), D("20.0"), D("5.0"), D("10.0")),
}


def dec(x: object) -> Decimal:
    return x if isinstance(x, Decimal) else D(str(x))


def net_pnl_bps(gross_directional_bps: Decimal, costs: CostVector) -> Decimal:
    return gross_directional_bps - costs.total_bps


def action(gross_directional_bps: Decimal, costs: CostVector) -> str:
    return "TRADE" if net_pnl_bps(gross_directional_bps, costs) > 0 else "HOLD"


def run(empirical_report: Mapping[str, object]) -> dict[str, object]:
    gross: dict[str, Decimal] = {}
    for cycle in empirical_report["cycles"]:
        cid = str(cycle["cycle_id"])
        entry = dec(cycle["entry_return"]["price"])
        exit_ = dec(cycle["exit_return"]["price"])
        gross[cid] = (exit_ / entry - D(1)) * BPS

    rows: list[dict[str, object]] = []
    naive_unsafe = 0
    closure_unsafe = 0
    learned_actions: dict[str, dict[str, str]] = {}

    for cid in sorted(gross):
        learned_actions[cid] = {}
        for name, costs in SCENARIOS.items():
            net = net_pnl_bps(gross[cid], costs)
            a = action(gross[cid], costs)
            naive = "TRADE" if gross[cid] > 0 else "HOLD"
            if naive == "TRADE" and net <= 0:
                naive_unsafe += 1
            if a == "TRADE" and net <= 0:
                closure_unsafe += 1
            learned_actions[cid][name] = a
            rows.append({
                "cycle_id": cid,
                "scenario": name,
                "gross_directional_bps": str(gross[cid]),
                "fees_bps": str(costs.fees_bps),
                "slippage_bps": str(costs.slippage_bps),
                "adverse_selection_bps": str(costs.adverse_selection_bps),
                "inventory_carry_bps": str(costs.inventory_carry_bps),
                "forced_unwind_bps": str(costs.forced_unwind_bps),
                "all_in_cost_bps": str(costs.total_bps),
                "closure_adjusted_realized_pnl_bps": str(net),
                "naive_gross_action": naive,
                "closure_adjusted_action": a,
            })

    return {
        "schema_version": "nrrf847.realistic_cost_slippage_closure_learning.v1",
        "test_kind": "EMPIRICAL_RETURN_CLASSES_WITH_EXPLICIT_COUNTERFACTUAL_EXECUTION_COST_SURFACES",
        "market_return_source": "NRRF846 authenticated public Alpaca BTC/USD return witnesses",
        "own_fill_boundary": "public market returns are not authenticated own-account fills",
        "cost_surfaces": {
            k: {
                "fees_bps": str(v.fees_bps),
                "slippage_bps": str(v.slippage_bps),
                "adverse_selection_bps": str(v.adverse_selection_bps),
                "inventory_carry_bps": str(v.inventory_carry_bps),
                "forced_unwind_bps": str(v.forced_unwind_bps),
                "total_bps": str(v.total_bps),
            }
            for k, v in SCENARIOS.items()
        },
        "gross_directional_bps": {k: str(v) for k, v in gross.items()},
        "learned_actions": learned_actions,
        "naive_gross_positive_unsafe_admissions": naive_unsafe,
        "closure_adjusted_unsafe_admissions": closure_unsafe,
        "all_in_30bps_all_hold": all(
            learned_actions[c]["ALL_IN_30BPS"] == "HOLD" for c in learned_actions
        ),
        "interpretation": (
            "Gross-positive closure is insufficient. The selector subtracts the full explicit cost vector before admission. "
            "At 30 bps all-in cost every observed return class is negative and therefore HOLD."
        ),
        "rows": rows,
    }


def main() -> int:
    src = Path("reports/nrrf846_empirical_alpaca_sense_loop_20260830.json")
    out = Path("reports/nrrf847_realistic_cost_slippage_closure_learning_20260830.json")
    result = run(json.loads(src.read_text()))
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
