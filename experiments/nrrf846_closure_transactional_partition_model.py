from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import dataclass
from decimal import Decimal, ROUND_FLOOR, getcontext
from pathlib import Path
from typing import Mapping, Sequence

getcontext().prec = 80
D0 = Decimal("0")
D1 = Decimal("1")
BPS = Decimal("10000")
SCHEMA_VERSION = "nrrf846.closure_transactional_partition.v1"


def dec(x: object) -> Decimal:
    if isinstance(x, Decimal):
        return x
    if isinstance(x, float):
        raise TypeError("binary float rejected")
    return Decimal(str(x))


def canon(x: object) -> object:
    if isinstance(x, Decimal):
        return format(x, "f")
    if isinstance(x, Mapping):
        return {str(k): canon(v) for k, v in sorted(x.items(), key=lambda kv: str(kv[0]))}
    if isinstance(x, (list, tuple)):
        return [canon(v) for v in x]
    return x


def sha(x: object) -> str:
    payload = json.dumps(canon(x), sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return hashlib.sha256(payload.encode()).hexdigest()


def pow2_bucket(x: Decimal) -> int:
    if x <= 0:
        return -64
    b = 0
    y = x
    while y >= 2 and b < 64:
        y /= 2
        b += 1
    while y < 1 and b > -64:
        y *= 2
        b -= 1
    return b


@dataclass(frozen=True, order=True)
class ObservationBubble:
    spread_band_1bps: int
    imbalance_decile: int
    relative_depth_pow2: int

    @property
    def key(self) -> str:
        return f"s{self.spread_band_1bps}|i{self.imbalance_decile}|d{self.relative_depth_pow2}"

    def to_dict(self) -> dict[str, object]:
        return {
            "spread_band_1bps": self.spread_band_1bps,
            "imbalance_decile": self.imbalance_decile,
            "relative_depth_pow2": self.relative_depth_pow2,
            "key": self.key,
        }


def derive_bubble(cycle: Mapping[str, object]) -> ObservationBubble:
    """Derive the learning/token class only from information visible at entry.

    Price level itself is intentionally absent. The class uses relational quote
    geometry: spread, bid/ask size imbalance, and displayed depth relative to the
    requested transaction quantity.
    """
    q = dec(cycle["quantity_btc"])
    before = cycle["entry_before"]
    bid = dec(before["bid_price"])
    ask = dec(before["ask_price"])
    bid_size = dec(before["bid_size"])
    ask_size = dec(before["ask_size"])
    mid = (bid + ask) / 2
    spread_bps = (ask - bid) / mid * BPS
    spread_band = int(spread_bps.to_integral_value(rounding=ROUND_FLOOR))
    bid_share = bid_size / (bid_size + ask_size)
    imbalance = min(9, max(0, int((bid_share * 10).to_integral_value(rounding=ROUND_FLOOR))))
    relative_depth = (bid_size + ask_size) / q
    return ObservationBubble(spread_band, imbalance, pow2_bucket(relative_depth))


@dataclass(frozen=True)
class BubbleMemory:
    bubble: ObservationBubble
    observation_count: int
    mean_zero_fee_directional_bps: Decimal
    conservative_queue_threshold: Decimal
    evidence_hashes: tuple[str, ...]

    def to_dict(self) -> dict[str, object]:
        return canon({
            "bubble": self.bubble.to_dict(),
            "observation_count": self.observation_count,
            "mean_zero_fee_directional_bps": self.mean_zero_fee_directional_bps,
            "conservative_queue_threshold": self.conservative_queue_threshold,
            "evidence_hashes": self.evidence_hashes,
        })


@dataclass(frozen=True)
class TransactionalState:
    bubbles: Mapping[str, BubbleMemory]
    sequence: int
    evidence_chain: tuple[str, ...]

    @classmethod
    def empty(cls) -> "TransactionalState":
        return cls({}, 0, ())

    def to_dict(self) -> dict[str, object]:
        return canon({
            "schema_version": SCHEMA_VERSION,
            "sequence": self.sequence,
            "evidence_chain": self.evidence_chain,
            "bubbles": {k: v.to_dict() for k, v in sorted(self.bubbles.items())},
        })

    @property
    def state_hash(self) -> str:
        return sha(self.to_dict())

    def learn_closed_return(
        self,
        *,
        bubble: ObservationBubble,
        zero_fee_directional_bps: Decimal,
        queue_threshold: Decimal,
        evidence: Mapping[str, object],
    ) -> "TransactionalState":
        old = self.bubbles.get(bubble.key)
        evidence_hash = sha(evidence)
        if old is None:
            memory = BubbleMemory(
                bubble=bubble,
                observation_count=1,
                mean_zero_fee_directional_bps=zero_fee_directional_bps,
                conservative_queue_threshold=queue_threshold,
                evidence_hashes=(evidence_hash,),
            )
        else:
            n = old.observation_count
            mean = (old.mean_zero_fee_directional_bps * n + zero_fee_directional_bps) / (n + 1)
            memory = BubbleMemory(
                bubble=bubble,
                observation_count=n + 1,
                mean_zero_fee_directional_bps=mean,
                conservative_queue_threshold=min(old.conservative_queue_threshold, queue_threshold),
                evidence_hashes=old.evidence_hashes + (evidence_hash,),
            )
        bubbles = dict(self.bubbles)
        bubbles[bubble.key] = memory
        return TransactionalState(
            bubbles=bubbles,
            sequence=self.sequence + 1,
            evidence_chain=self.evidence_chain + (evidence_hash,),
        )


def exact_maker_maker_bps(entry: Decimal, exit_: Decimal, maker_fee_bps: Decimal) -> Decimal:
    """Alpaca credited-asset round trip: buy fee in BTC, sell fee in USD."""
    r = maker_fee_bps / BPS
    return (((D1 - r) * (D1 - r) * exit_ / entry) - D1) * BPS


def zero_fee_directional_bps(cycle: Mapping[str, object]) -> Decimal:
    entry = dec(cycle["entry_return"]["price"])
    exit_ = dec(cycle["exit_return"]["price"])
    return (exit_ / entry - D1) * BPS


def truth_for(
    cycle: Mapping[str, object], maker_fee_bps: Decimal, queue_ahead_fraction: Decimal
) -> tuple[str, Decimal, bool]:
    entry = dec(cycle["entry_return"]["price"])
    exit_ = dec(cycle["exit_return"]["price"])
    pnl_bps = exact_maker_maker_bps(entry, exit_, maker_fee_bps)
    threshold = dec(cycle["full_cycle_queue_threshold"])
    feasible = queue_ahead_fraction <= threshold
    return ("TRADE" if feasible and pnl_bps > 0 else "HOLD"), pnl_bps, feasible


def predict_for(
    state: TransactionalState,
    bubble: ObservationBubble,
    cycle: Mapping[str, object],
    maker_fee_bps: Decimal,
    queue_ahead_fraction: Decimal,
) -> tuple[str, str, Decimal | None, bool | None]:
    memory = state.bubbles.get(bubble.key)
    if memory is None:
        return "HOLD", "COLD_START_UNSEEN_BUBBLE", None, None
    entry = dec(cycle["entry_return"]["price"])
    # Translate the learned zero-fee relation into the current fee constraint
    # without importing outcomes from another bubble.
    learned_exit = entry * (D1 + memory.mean_zero_fee_directional_bps / BPS)
    predicted_bps = exact_maker_maker_bps(entry, learned_exit, maker_fee_bps)
    queue_ok = queue_ahead_fraction <= memory.conservative_queue_threshold
    action = "TRADE" if queue_ok and predicted_bps > 0 else "HOLD"
    return action, "LOCAL_BUBBLE_MEMORY", predicted_bps, queue_ok


def integrate_and_replay(
    fixture: Mapping[str, object], empirical_report: Mapping[str, object]
) -> dict[str, object]:
    fixture_cycles = {c["cycle_id"]: c for c in fixture["cycles"]}
    empirical_cycles = {c["cycle_id"]: c for c in empirical_report["cycles"]}
    fees = [dec(x) for x in (15, 12, 10, 8, 5, 2, 0)]
    queues = [dec(x) for x in ("0", "0.001", "0.002", "0.005", "0.01", "0.02")]

    state = TransactionalState.empty()
    rows: list[dict[str, object]] = []
    pass_summaries: list[dict[str, object]] = []
    prior_other_hashes: dict[str, str] = {}

    # Two passes are deliberate. First contact with each derived bubble is a
    # fail-closed cold start. The second visit tests survival/retention under the
    # same market form but every fee/queue constraint in the grid.
    for pass_index in (1, 2):
        confusion = {"tp": 0, "tn": 0, "fp": 0, "fn": 0}
        unsafe = 0
        for cycle_id in ("A", "B", "C"):
            raw = fixture_cycles[cycle_id]
            observed = empirical_cycles[cycle_id]
            bubble = derive_bubble(raw)
            before_state = state
            before_hash = state.state_hash
            existing_other = {
                k: sha(v.to_dict()) for k, v in state.bubbles.items() if k != bubble.key
            }
            for fee in fees:
                for queue in queues:
                    predicted, source, predicted_bps, predicted_queue_ok = predict_for(
                        state, bubble, observed, fee, queue
                    )
                    truth, actual_bps, actual_queue_ok = truth_for(observed, fee, queue)
                    if predicted == "TRADE" and truth == "TRADE":
                        confusion["tp"] += 1
                    elif predicted == "HOLD" and truth == "HOLD":
                        confusion["tn"] += 1
                    elif predicted == "TRADE" and truth == "HOLD":
                        confusion["fp"] += 1
                        unsafe += 1
                    else:
                        confusion["fn"] += 1
                    rows.append(canon({
                        "pass": pass_index,
                        "cycle_id": cycle_id,
                        "bubble": bubble.to_dict(),
                        "maker_fee_bps": fee,
                        "queue_ahead_fraction": queue,
                        "prediction": predicted,
                        "prediction_source": source,
                        "predicted_pnl_bps": predicted_bps,
                        "predicted_queue_feasible": predicted_queue_ok,
                        "truth": truth,
                        "actual_pnl_bps": actual_bps,
                        "actual_queue_feasible": actual_queue_ok,
                        "state_hash_before_reveal": before_hash,
                    }))

            # Reveal only after all 42 constraint predictions for this cycle.
            z = zero_fee_directional_bps(observed)
            threshold = dec(observed["full_cycle_queue_threshold"])
            evidence = {
                "cycle_id": cycle_id,
                "bubble": bubble.to_dict(),
                "authenticated_entry_return": observed["entry_return"],
                "authenticated_exit_return": observed["exit_return"],
                "zero_fee_directional_bps": z,
                "full_cycle_queue_threshold": threshold,
            }
            state = state.learn_closed_return(
                bubble=bubble,
                zero_fee_directional_bps=z,
                queue_threshold=threshold,
                evidence=evidence,
            )
            after_other = {
                k: sha(v.to_dict()) for k, v in state.bubbles.items() if k != bubble.key
            }
            if existing_other != after_other:
                raise AssertionError("learning one bubble mutated another bubble")
            prior_other_hashes.update(after_other)

        pass_summaries.append({
            "pass": pass_index,
            "confusion": confusion,
            "unsafe_admissions": unsafe,
            "positive_recall": (
                str(Decimal(confusion["tp"]) / Decimal(confusion["tp"] + confusion["fn"]))
                if confusion["tp"] + confusion["fn"] else None
            ),
        })

    total = {k: sum(p["confusion"][k] for p in pass_summaries) for k in ("tp", "tn", "fp", "fn")}
    bubbles = {cid: derive_bubble(fixture_cycles[cid]).to_dict() for cid in ("A", "B", "C")}
    distinct = len({b["key"] for b in bubbles.values()}) == 3
    second = pass_summaries[1]["confusion"]
    return canon({
        "schema_version": SCHEMA_VERSION,
        "test_kind": "EMPIRICAL_AUTHENTICATED_RETURNS_PLUS_COUNTERFACTUAL_CONSTRAINT_GRID",
        "transactional_relation": "pretrade observation -> derived bubble -> local memory -> TRADE/HOLD -> authenticated return -> exact receipt -> same-bubble update -> next state",
        "partition_inputs": ["entry spread", "entry top-book imbalance", "entry displayed depth / requested quantity"],
        "price_level_authors_partition": False,
        "lookahead": False,
        "cold_start": "HOLD",
        "passes": pass_summaries,
        "aggregate_confusion": total,
        "derived_bubbles": bubbles,
        "all_three_empirical_forms_distinct_pretrade": distinct,
        "second_visit_unsafe_admissions": second["fp"],
        "second_visit_missed_positive_states": second["fn"],
        "second_visit_positive_recall": str(Decimal(second["tp"]) / Decimal(second["tp"] + second["fn"])),
        "other_bubble_memory_immutable_on_local_update": True,
        "knowledge_evidence_count": len(state.evidence_chain),
        "final_state": state.to_dict(),
        "final_state_hash": state.state_hash,
        "verdict": {
            "global_negative_transfer_removed": second["fp"] == 0,
            "revisited_bubbles_survive_fee_queue_constraints": second["fp"] == 0 and second["fn"] == 0,
            "cold_start_claim_solved": False,
            "generalization_to_unseen_market_bubbles_established": False,
        },
        "claims_boundary": {
            "market_returns_empirical": True,
            "constraint_grid_counterfactual": True,
            "own_order_fills_authenticated": False,
            "profitability_claim": False,
        },
        "rows": rows,
    })


def main(argv: Sequence[str] | None = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--fixture", type=Path, required=True)
    p.add_argument("--empirical-report", type=Path, required=True)
    p.add_argument("--output", type=Path)
    args = p.parse_args(argv)
    fixture = json.loads(args.fixture.read_text())
    report = json.loads(args.empirical_report.read_text())
    result = integrate_and_replay(fixture, report)
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(text)
    else:
        print(text, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
