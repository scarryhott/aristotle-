from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import dataclass
from datetime import datetime
from decimal import Decimal
from pathlib import Path
from typing import Mapping, Sequence

D0 = Decimal("0")
D1 = Decimal("1")
BPS = Decimal("10000")
SCHEMA_VERSION = "nrrf846.empirical_alpaca_sense_loop.v1"


def dec(value: object) -> Decimal:
    if isinstance(value, Decimal):
        out = value
    elif isinstance(value, (str, int)):
        out = Decimal(value)
    else:
        raise TypeError("decimal values must be strings, ints, or Decimal")
    if not out.is_finite():
        raise ValueError("non-finite decimal")
    return out


def dtext(value: Decimal) -> str:
    text = format(value, "f")
    if "." in text:
        text = text.rstrip("0").rstrip(".")
    return text or "0"


def canonical(value: object) -> object:
    if isinstance(value, Decimal):
        return dtext(value)
    if isinstance(value, Mapping):
        return {str(k): canonical(v) for k, v in sorted(value.items())}
    if isinstance(value, (list, tuple)):
        return [canonical(v) for v in value]
    return value


def digest(value: object) -> str:
    data = json.dumps(canonical(value), sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(data).hexdigest()


@dataclass(frozen=True)
class Quote:
    timestamp_utc: str
    bid_price: Decimal
    bid_size: Decimal
    ask_price: Decimal
    ask_size: Decimal


@dataclass(frozen=True)
class Trade:
    timestamp_utc: str
    price: Decimal
    size: Decimal


@dataclass(frozen=True)
class TouchWitness:
    side: str
    price: Decimal
    size: Decimal
    authenticated: bool
    reason: str


@dataclass(frozen=True)
class CostVector:
    base_fee_btc: Decimal
    quote_fee_usd: Decimal
    spread_usd: Decimal
    adverse_selection_usd: Decimal
    latency_seconds: Decimal
    inventory_btc_seconds: Decimal

    def componentwise_le(self, other: "CostVector") -> bool:
        return all(a <= b for a, b in zip(self.values(), other.values()))

    def values(self) -> tuple[Decimal, ...]:
        return (
            self.base_fee_btc,
            self.quote_fee_usd,
            self.spread_usd,
            self.adverse_selection_usd,
            self.latency_seconds,
            self.inventory_btc_seconds,
        )

    def to_dict(self) -> dict[str, str]:
        return {
            "base_fee_btc": dtext(self.base_fee_btc),
            "quote_fee_usd": dtext(self.quote_fee_usd),
            "spread_usd": dtext(self.spread_usd),
            "adverse_selection_usd": dtext(self.adverse_selection_usd),
            "latency_seconds": dtext(self.latency_seconds),
            "inventory_btc_seconds": dtext(self.inventory_btc_seconds),
        }


def quote(payload: Mapping[str, object]) -> Quote:
    return Quote(
        timestamp_utc=str(payload["timestamp_utc"]),
        bid_price=dec(payload["bid_price"]),
        bid_size=dec(payload["bid_size"]),
        ask_price=dec(payload["ask_price"]),
        ask_size=dec(payload["ask_size"]),
    )


def trade(payload: Mapping[str, object]) -> Trade:
    return Trade(
        timestamp_utc=str(payload["timestamp_utc"]),
        price=dec(payload["price"]),
        size=dec(payload["size"]),
    )


def authenticate_touch(before: Quote, after: Quote, observed: Trade) -> TouchWitness:
    if observed.timestamp_utc != after.timestamp_utc:
        return TouchWitness("NONE", observed.price, observed.size, False, "timestamp_mismatch")
    if observed.price == before.bid_price:
        if before.bid_price == after.bid_price and before.bid_size - after.bid_size == observed.size:
            return TouchWitness(
                "MAKER_BUY_RETURN", observed.price, observed.size, True,
                "trade_at_bid_and_exact_displayed_bid_size_decrement",
            )
        if observed.size == before.bid_size and after.bid_price < before.bid_price:
            return TouchWitness(
                "MAKER_BUY_RETURN", observed.price, observed.size, True,
                "trade_consumed_entire_displayed_bid_level",
            )
    if observed.price == before.ask_price:
        if before.ask_price == after.ask_price and before.ask_size - after.ask_size == observed.size:
            return TouchWitness(
                "MAKER_SELL_RETURN", observed.price, observed.size, True,
                "trade_at_ask_and_exact_displayed_ask_size_decrement",
            )
        if observed.size == before.ask_size and after.ask_price > before.ask_price:
            return TouchWitness(
                "MAKER_SELL_RETURN", observed.price, observed.size, True,
                "trade_consumed_entire_displayed_ask_level",
            )
    return TouchWitness("NONE", observed.price, observed.size, False, "no_exact_return_witness")


def maker_fill(flow: Decimal, displayed_queue: Decimal, queue_fraction_ahead: Decimal, quantity: Decimal) -> bool:
    if not D0 <= queue_fraction_ahead <= D1:
        raise ValueError("queue fraction must be in [0,1]")
    return flow >= displayed_queue * queue_fraction_ahead + quantity


def simulate_cycle(cycle: Mapping[str, object], maker_rate: Decimal, taker_rate: Decimal, grid_steps: int) -> dict[str, object]:
    eb = quote(cycle["entry_before"])
    ea = quote(cycle["entry_after"])
    et = trade(cycle["entry_trade"])
    xb = quote(cycle["exit_before"])
    xa = quote(cycle["exit_after"])
    xt = trade(cycle["exit_trade"])
    quantity = dec(cycle["quantity_btc"])

    entry_witness = authenticate_touch(eb, ea, et)
    exit_witness = authenticate_touch(xb, xa, xt)
    if not entry_witness.authenticated or not exit_witness.authenticated:
        raise ValueError("empirical cycle lacks authenticated return witness")

    net_quantity = quantity * (D1 - maker_rate)
    entry_notional = quantity * eb.bid_price
    latency = dec(str((datetime.fromisoformat(xt.timestamp_utc) - datetime.fromisoformat(et.timestamp_utc)).total_seconds()))

    full_exit_gross = net_quantity * xb.ask_price
    full_exit_fee = full_exit_gross * maker_rate
    full_pnl = -entry_notional + full_exit_gross - full_exit_fee

    skipped_exit_gross = net_quantity * xb.bid_price
    skipped_exit_fee = skipped_exit_gross * taker_rate
    skipped_pnl = -entry_notional + skipped_exit_gross - skipped_exit_fee

    exit_mid = (xb.bid_price + xb.ask_price) / Decimal(2)
    adverse = max(D0, net_quantity * (eb.bid_price - exit_mid))
    base_fee = quantity * maker_rate
    full_cost = CostVector(
        base_fee_btc=base_fee,
        quote_fee_usd=full_exit_fee,
        spread_usd=D0,
        adverse_selection_usd=adverse,
        latency_seconds=latency,
        inventory_btc_seconds=net_quantity * latency,
    )
    skipped_cost = CostVector(
        base_fee_btc=base_fee,
        quote_fee_usd=skipped_exit_fee,
        spread_usd=net_quantity * (xb.ask_price - xb.bid_price),
        adverse_selection_usd=adverse,
        latency_seconds=latency,
        inventory_btc_seconds=net_quantity * latency,
    )

    entry_max_queue_ahead = et.size - quantity
    exit_max_queue_ahead = xt.size - net_quantity
    entry_fraction_threshold = entry_max_queue_ahead / eb.bid_size
    exit_fraction_threshold = exit_max_queue_ahead / xb.ask_size

    full_count = skipped_count = no_entry_count = 0
    for i in range(grid_steps + 1):
        queue_fraction = Decimal(i) / Decimal(grid_steps)
        entry_filled = maker_fill(et.size, eb.bid_size, queue_fraction, quantity)
        if not entry_filled:
            no_entry_count += 1
            continue
        exit_filled = maker_fill(xt.size, xb.ask_size, queue_fraction, net_quantity)
        if exit_filled:
            full_count += 1
        else:
            skipped_count += 1

    grid_total = grid_steps + 1
    front_full = maker_fill(et.size, eb.bid_size, D0, quantity) and maker_fill(xt.size, xb.ask_size, D0, net_quantity)

    return canonical({
        "cycle_id": cycle["cycle_id"],
        "entry_return": entry_witness.__dict__,
        "exit_return": exit_witness.__dict__,
        "quantity_btc": quantity,
        "net_quantity_after_entry_fee_btc": net_quantity,
        "entry_notional_usd": entry_notional,
        "latency_seconds": latency,
        "entry_max_queue_ahead_fraction": entry_fraction_threshold,
        "exit_max_queue_ahead_fraction": exit_fraction_threshold,
        "front_of_queue_four_sheaf_reaches_hair": front_full,
        "full_four_sheaf_path": {
            "cycle": "0->1->2->3->0",
            "relative_closure_cost": "0" if front_full else "INF",
            "economic_pnl_usd": full_pnl,
            "economic_pnl_bps": full_pnl / entry_notional * BPS,
            "cost_metavector": full_cost.to_dict(),
        },
        "skipped_passive_exit_path": {
            "cycle": "0->1->3->0",
            "relative_closure_cost": "INF",
            "economic_pnl_usd": skipped_pnl,
            "economic_pnl_bps": skipped_pnl / entry_notional * BPS,
            "cost_metavector": skipped_cost.to_dict(),
        },
        "taker_exit_cost_componentwise_dominates": full_cost.componentwise_le(skipped_cost) and full_cost.values() != skipped_cost.values(),
        "passive_exit_advantage_bps": (full_pnl - skipped_pnl) / entry_notional * BPS,
        "queue_fraction_sweep": {
            "grid_points": grid_total,
            "full_four_sheaf_count": full_count,
            "skipped_passive_exit_count": skipped_count,
            "no_maker_entry_count": no_entry_count,
            "full_four_sheaf_grid_share": Decimal(full_count) / Decimal(grid_total),
            "skipped_passive_exit_grid_share": Decimal(skipped_count) / Decimal(grid_total),
            "no_maker_entry_grid_share": Decimal(no_entry_count) / Decimal(grid_total),
            "interpretation": "sensitivity sweep over queue-ahead fractions, not a probability model",
        },
    })


def run_fixture(payload: Mapping[str, object], grid_steps: int = 10000) -> dict[str, object]:
    maker_rate = dec(payload["fees"]["maker_rate"])
    taker_rate = dec(payload["fees"]["taker_rate"])

    semantic_state = {
        "authenticated_returns": [],
        "token": digest([]),
        "form": None,
        "relative_closure_cost": "INF",
    }
    before_quote_hash = digest(semantic_state)
    for cycle in payload["cycles"]:
        _ = quote(cycle["entry_before"])
        _ = quote(cycle["exit_before"])
    after_quote_hash = digest(semantic_state)

    results = []
    for cycle in payload["cycles"]:
        result = simulate_cycle(cycle, maker_rate, taker_rate, grid_steps)
        results.append(result)
        for key in ("entry_return", "exit_return"):
            witness = result[key]
            if witness["authenticated"]:
                semantic_state["authenticated_returns"].append({
                    "cycle_id": result["cycle_id"],
                    "side": witness["side"],
                    "price": witness["price"],
                    "size": witness["size"],
                })
        if result["front_of_queue_four_sheaf_reaches_hair"]:
            semantic_state["form"] = "HAIR"
            semantic_state["relative_closure_cost"] = "0"
        semantic_state["token"] = digest(semantic_state["authenticated_returns"])

    return canonical({
        "schema_version": SCHEMA_VERSION,
        "simulation_kind": "EMPIRICAL_ALPACA_MARKET_DATA_REPLAY_WITH_COUNTERFACTUAL_ORDER_PARTICIPATION",
        "market_data_authenticated": True,
        "own_order_fills_authenticated": False,
        "quote_only_semantic_state_invariant": before_quote_hash == after_quote_hash,
        "quote_only_state_hash_before": before_quote_hash,
        "quote_only_state_hash_after": after_quote_hash,
        "authenticated_return_count": len(semantic_state["authenticated_returns"]),
        "final_semantic_state": semantic_state,
        "cycles": results,
        "claims_boundary": {
            "profitability_claim": False,
            "actual_order_submission": False,
            "actual_account_fill_receipts": False,
            "queue_sweep_is_probability_model": False,
        },
    })


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("fixture")
    parser.add_argument("--grid-steps", type=int, default=10000)
    parser.add_argument("--output")
    args = parser.parse_args(argv)
    payload = json.loads(Path(args.fixture).read_text())
    result = run_fixture(payload, args.grid_steps)
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).parent.mkdir(parents=True, exist_ok=True)
        Path(args.output).write_text(text)
    print(text, end="")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
