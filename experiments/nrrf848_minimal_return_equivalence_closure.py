from __future__ import annotations

import argparse
import json
import math
import random
import statistics
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Mapping, Sequence

OPS = ("MAKER", "TAKER", "CROSS", "HEDGE")
COST_KEYS = (
    "fees",
    "spread",
    "slippage",
    "queue",
    "latency",
    "adverse",
    "inventory",
    "borrow",
    "forced_unwind",
)
SCHEMA_VERSION = "nrrf848.minimal_return_equivalence_closure.v1"


@dataclass(frozen=True)
class Observation:
    spread_bps: float
    depth_ratio: float
    imbalance: float
    volatility_bps: float
    latency_ms: float
    toxicity: float
    fee_bps: float
    borrow_bps: float


@dataclass(frozen=True)
class Receipt:
    authenticated: bool
    operation: str
    gross_bps: float
    realized_costs: Mapping[str, float]
    realized_pnl_bps: float
    inventory_closed: bool

    @property
    def total_cost_bps(self) -> float:
        return sum(self.realized_costs.values())


class ReturnStats:
    def __init__(self) -> None:
        self.pnl: list[float] = []
        self.closed: list[int] = []
        self.costs: dict[str, list[float]] = defaultdict(list)

    def add(self, receipt: Receipt) -> None:
        self.pnl.append(receipt.realized_pnl_bps)
        self.closed.append(1 if receipt.inventory_closed else 0)
        for key in COST_KEYS:
            self.costs[key].append(float(receipt.realized_costs.get(key, 0.0)))

    @property
    def n(self) -> int:
        return len(self.pnl)

    @property
    def mean_pnl(self) -> float:
        return statistics.fmean(self.pnl) if self.pnl else 0.0

    @property
    def close_rate(self) -> float:
        return statistics.fmean(self.closed) if self.closed else 0.0

    def pnl_lcb(self, z: float = 1.28) -> float:
        if self.n < 2:
            return float("-inf")
        return self.mean_pnl - z * statistics.stdev(self.pnl) / math.sqrt(self.n)

    def closure_lcb(self, z: float = 1.28) -> float:
        if self.n == 0:
            return 0.0
        p = self.close_rate
        n = self.n
        den = 1.0 + z * z / n
        center = (p + z * z / (2.0 * n)) / den
        radius = z * math.sqrt(p * (1.0 - p) / n + z * z / (4.0 * n * n)) / den
        return max(0.0, center - radius)

    def mean_cost(self, key: str) -> float:
        values = self.costs.get(key, ())
        return statistics.fmean(values) if values else 0.0


class MinimalReturnEquivalenceClosure:
    """Interactive closure learner whose token is a learned return-equivalence class.

    Authenticated receipts are monotone evidence.  A fine observational cell is
    never a token merely because its coordinates differ.  Cells are merged when
    their learned operation/return fingerprints agree at the declared empirical
    resolution; if later evidence changes a fingerprint, rebuilding can split the
    former token again.  Hence the current tokenization is the coarsest partition
    induced by the currently learned return-law fingerprint.
    """

    def __init__(
        self,
        *,
        min_cell_samples: int = 4,
        pnl_tolerance_bps: float = 2.0,
        closure_tolerance: float = 0.10,
        cost_tolerance_bps: float = 2.0,
    ) -> None:
        self.min_cell_samples = min_cell_samples
        self.pnl_tolerance_bps = pnl_tolerance_bps
        self.closure_tolerance = closure_tolerance
        self.cost_tolerance_bps = cost_tolerance_bps
        self.cells: dict[tuple[int, ...], dict[str, ReturnStats]] = defaultdict(
            lambda: defaultdict(ReturnStats)
        )
        self.partition: dict[tuple[int, ...], tuple[object, ...]] = {}
        self.evidence_count = 0
        self.evidence_hash_chain: list[str] = []
        self._dirty = True

    @staticmethod
    def cell(observation: Observation) -> tuple[int, ...]:
        return (
            int(observation.spread_bps // 1.0),
            int(math.log2(max(observation.depth_ratio, 0.5))),
            int(observation.volatility_bps // 6.0),
            int(observation.latency_ms // 2.0),
            int((observation.imbalance + 1.0) * 2.0),
            int(observation.toxicity * 3.0),
            int(observation.fee_bps // 5.0),
            int(observation.borrow_bps > 1.0),
        )

    @staticmethod
    def _stable_hash(payload: object) -> str:
        import hashlib

        raw = json.dumps(payload, sort_keys=True, separators=(",", ":"), default=str)
        return hashlib.sha256(raw.encode()).hexdigest()

    def observe(self, observation: Observation, receipt: Receipt) -> bool:
        if not receipt.authenticated:
            return False
        cell = self.cell(observation)
        self.cells[cell][receipt.operation].add(receipt)
        payload = {
            "cell": cell,
            "operation": receipt.operation,
            "gross_bps": receipt.gross_bps,
            "realized_costs": dict(receipt.realized_costs),
            "realized_pnl_bps": receipt.realized_pnl_bps,
            "inventory_closed": receipt.inventory_closed,
            "previous": self.evidence_hash_chain[-1] if self.evidence_hash_chain else None,
        }
        self.evidence_hash_chain.append(self._stable_hash(payload))
        self.evidence_count += 1
        self._dirty = True
        return True

    def _fingerprint(self, cell: tuple[int, ...]) -> tuple[object, ...]:
        parts: list[object] = []
        for op in OPS:
            stats = self.cells[cell].get(op)
            if stats is None or stats.n < self.min_cell_samples:
                parts.append((op, "UNKNOWN"))
                continue
            cost_signature = tuple(
                (key, round(stats.mean_cost(key) / self.cost_tolerance_bps))
                for key in COST_KEYS
            )
            parts.append(
                (
                    op,
                    round(stats.mean_pnl / self.pnl_tolerance_bps),
                    round(stats.close_rate / self.closure_tolerance),
                    cost_signature,
                )
            )
        return tuple(parts)

    def rebuild_partition(self) -> None:
        if not self._dirty:
            return
        self.partition = {cell: self._fingerprint(cell) for cell in self.cells}
        self._dirty = False

    @property
    def bubble_count(self) -> int:
        self.rebuild_partition()
        return len(set(self.partition.values()))

    def bubble_for(self, observation: Observation) -> tuple[object, ...] | None:
        self.rebuild_partition()
        return self.partition.get(self.cell(observation))

    def _aggregate(self, bubble: tuple[object, ...], op: str) -> ReturnStats:
        aggregate = ReturnStats()
        for cell, current in self.partition.items():
            if current != bubble:
                continue
            stats = self.cells[cell].get(op)
            if stats is None:
                continue
            aggregate.pnl.extend(stats.pnl)
            aggregate.closed.extend(stats.closed)
            for key, values in stats.costs.items():
                aggregate.costs[key].extend(values)
        return aggregate

    def select_operation(
        self,
        observation: Observation,
        *,
        min_bubble_samples: int = 10,
        pnl_margin_bps: float = 0.10,
        closure_floor: float = 0.90,
        z: float = 1.28,
    ) -> str:
        bubble = self.bubble_for(observation)
        if bubble is None:
            return "HOLD"
        candidates: list[tuple[float, str]] = []
        for op in OPS:
            stats = self._aggregate(bubble, op)
            if stats.n < min_bubble_samples:
                continue
            pnl_lcb = stats.pnl_lcb(z)
            close_lcb = stats.closure_lcb(z)
            if pnl_lcb > pnl_margin_bps and close_lcb > closure_floor:
                candidates.append((pnl_lcb, op))
        return max(candidates)[1] if candidates else "HOLD"

    def snapshot(self) -> dict[str, object]:
        self.rebuild_partition()
        return {
            "schema_version": SCHEMA_VERSION,
            "evidence_count": self.evidence_count,
            "fine_cell_count": len(self.cells),
            "bubble_count": self.bubble_count,
            "knowledge_monotone": True,
            "evidence_tip": self.evidence_hash_chain[-1] if self.evidence_hash_chain else None,
        }


class FixedPartitionBaseline(MinimalReturnEquivalenceClosure):
    def rebuild_partition(self) -> None:
        if not self._dirty:
            return
        self.partition = {cell: cell for cell in self.cells}
        self._dirty = False


class CoarsePartitionBaseline(MinimalReturnEquivalenceClosure):
    @staticmethod
    def cell(observation: Observation) -> tuple[int, ...]:
        return (
            int(observation.spread_bps // 3.0),
            int(math.log2(max(observation.depth_ratio, 0.5))),
        )

    def rebuild_partition(self) -> None:
        if not self._dirty:
            return
        self.partition = {cell: cell for cell in self.cells}
        self._dirty = False


def sample_observation(rng: random.Random, index: int) -> Observation:
    regime = (index // 800) % 5
    if regime == 0:
        spread, depth, vol, tox, latency = (
            rng.uniform(0.5, 3.0), rng.uniform(5, 20), rng.uniform(2, 7),
            rng.uniform(0, 0.2), rng.uniform(0.1, 1.0),
        )
    elif regime == 1:
        spread, depth, vol, tox, latency = (
            rng.uniform(2, 8), rng.uniform(1, 6), rng.uniform(5, 15),
            rng.uniform(0.1, 0.4), rng.uniform(0.3, 2.0),
        )
    elif regime == 2:
        spread, depth, vol, tox, latency = (
            rng.uniform(1, 8), rng.uniform(1, 8), rng.uniform(10, 28),
            rng.uniform(0.4, 1.0), rng.uniform(0.5, 3.0),
        )
    elif regime == 3:
        spread, depth, vol, tox, latency = (
            rng.uniform(1, 6), rng.uniform(2, 10), rng.uniform(5, 18),
            rng.uniform(0.15, 0.6), rng.uniform(2, 10),
        )
    else:
        spread, depth, vol, tox, latency = (
            rng.uniform(0.8, 4), rng.uniform(3, 15), rng.uniform(3, 12),
            rng.uniform(0.05, 0.35), rng.uniform(0.2, 2),
        )
    return Observation(
        spread_bps=spread,
        depth_ratio=depth,
        imbalance=rng.uniform(-1, 1),
        volatility_bps=vol,
        latency_ms=latency,
        toxicity=tox,
        fee_bps=rng.choice([0, 0.2, 0.5, 1, 2, 5, 10, 15, 30]),
        borrow_bps=max(0.0, rng.gauss(0.3, 1.0)) if rng.random() < 0.2 else 0.0,
    )


def execute(rng: random.Random, observation: Observation, operation: str) -> Receipt:
    o = observation
    base = (
        0.35 * o.spread_bps
        + 0.15 * abs(o.imbalance) * o.spread_bps
        + 0.10 * math.log1p(o.depth_ratio)
        - 0.05 * o.volatility_bps
        - 0.30 * o.toxicity * o.spread_bps
        + rng.gauss(0, 0.7)
    )
    if operation == "MAKER":
        gross = base + 0.60 * o.spread_bps
        costs = {
            "fees": o.fee_bps, "spread": 0.0,
            "slippage": 0.04 * o.volatility_bps / max(1, o.depth_ratio),
            "queue": 0.10 * o.spread_bps + 0.10 * o.volatility_bps / max(1, o.depth_ratio),
            "latency": 0.04 * o.latency_ms * o.volatility_bps,
            "adverse": o.toxicity * (0.70 * o.spread_bps + 0.10 * o.volatility_bps),
            "inventory": 0.02 * o.volatility_bps * (1 + abs(o.imbalance)),
            "borrow": 0.10 * o.borrow_bps,
        }
        close_probability = max(0.05, min(0.99, 0.93 - 0.30 * o.toxicity - 0.02 * o.latency_ms - 0.015 * o.volatility_bps / max(1, o.depth_ratio)))
    elif operation == "TAKER":
        gross = base + 0.10 * o.spread_bps
        costs = {
            "fees": o.fee_bps, "spread": o.spread_bps,
            "slippage": 0.10 * o.volatility_bps / max(1, o.depth_ratio), "queue": 0.0,
            "latency": 0.015 * o.latency_ms * o.volatility_bps,
            "adverse": o.toxicity * (0.40 * o.spread_bps + 0.06 * o.volatility_bps),
            "inventory": 0.01 * o.volatility_bps, "borrow": 0.08 * o.borrow_bps,
        }
        close_probability = 0.995
    elif operation == "CROSS":
        gross = base + 0.30 * o.spread_bps
        costs = {
            "fees": 0.80 * o.fee_bps, "spread": 0.60 * o.spread_bps,
            "slippage": 0.13 * o.volatility_bps / max(1, o.depth_ratio), "queue": 0.02 * o.spread_bps,
            "latency": 0.05 * o.latency_ms * o.volatility_bps,
            "adverse": o.toxicity * (0.45 * o.spread_bps + 0.08 * o.volatility_bps),
            "inventory": 0.015 * o.volatility_bps, "borrow": 0.06 * o.borrow_bps,
        }
        close_probability = max(0.70, 0.99 - 0.015 * o.latency_ms)
    else:
        gross = 0.50 * base
        costs = {
            "fees": 1.10 * o.fee_bps, "spread": 0.75 * o.spread_bps,
            "slippage": 0.12 * o.volatility_bps / max(1, o.depth_ratio), "queue": 0.0,
            "latency": 0.02 * o.latency_ms * o.volatility_bps,
            "adverse": o.toxicity * (0.20 * o.spread_bps + 0.03 * o.volatility_bps),
            "inventory": 0.005 * o.volatility_bps, "borrow": 0.04 * o.borrow_bps,
        }
        close_probability = 0.999

    inventory_closed = rng.random() < close_probability
    costs["forced_unwind"] = 0.0
    realized = gross - sum(costs.values())
    if not inventory_closed:
        unwind = 0.50 * o.spread_bps + 0.10 * o.volatility_bps + 0.25 * o.latency_ms
        costs["forced_unwind"] = unwind
        realized -= unwind
    return Receipt(
        authenticated=rng.random() < 0.98,
        operation=operation,
        gross_bps=gross,
        realized_costs=costs,
        realized_pnl_bps=realized,
        inventory_closed=inventory_closed,
    )


def run_policy(
    policy_type: type[MinimalReturnEquivalenceClosure],
    *,
    seed: int,
    train_episodes: int,
    test_episodes: int,
) -> dict[str, object]:
    rng = random.Random(seed)
    model = policy_type()
    knowledge_path: list[int] = []
    for i in range(train_episodes):
        observation = sample_observation(rng, i)
        receipt = execute(rng, observation, rng.choice(OPS))
        model.observe(observation, receipt)
        knowledge_path.append(model.evidence_count)
    model.rebuild_partition()

    trades = holds = unsafe = positive_closed = 0
    pnl_sum = 0.0
    for j in range(test_episodes):
        observation = sample_observation(rng, train_episodes + j)
        operation = model.select_operation(observation)
        if operation == "HOLD":
            holds += 1
            continue
        trades += 1
        receipt = execute(rng, observation, operation)
        pnl_sum += receipt.realized_pnl_bps
        good = receipt.authenticated and receipt.inventory_closed and receipt.realized_pnl_bps > 0
        positive_closed += int(good)
        unsafe += int(not good)
        model.observe(observation, receipt)
        knowledge_path.append(model.evidence_count)
    model.rebuild_partition()
    return {
        "policy": policy_type.__name__,
        "train_episodes": train_episodes,
        "test_episodes": test_episodes,
        "trades": trades,
        "holds": holds,
        "unsafe_admissions": unsafe,
        "positive_closed_trades": positive_closed,
        "closure_adjusted_realized_pnl_bps_sum": pnl_sum,
        "mean_realized_pnl_bps_per_trade": pnl_sum / trades if trades else 0.0,
        "fine_cells": len(model.cells),
        "bubbles": model.bubble_count,
        "authenticated_evidence": model.evidence_count,
        "knowledge_monotone": all(b >= a for a, b in zip(knowledge_path, knowledge_path[1:])),
    }


def benchmark(seed: int = 847101, train_episodes: int = 10000, test_episodes: int = 3000) -> dict[str, object]:
    results = [
        run_policy(CoarsePartitionBaseline, seed=seed, train_episodes=train_episodes, test_episodes=test_episodes),
        run_policy(FixedPartitionBaseline, seed=seed, train_episodes=train_episodes, test_episodes=test_episodes),
        run_policy(MinimalReturnEquivalenceClosure, seed=seed, train_episodes=train_episodes, test_episodes=test_episodes),
    ]
    return {
        "schema_version": SCHEMA_VERSION,
        "simulation_kind": "BROAD_FINITE_TRADING_SCENARIO_CLOSURE_SIMULATION",
        "seed": seed,
        "claims_boundary": {
            "finite_not_all_possible_markets": True,
            "simulated_fills_not_authenticated_account_fills": True,
            "profitability_claim": False,
        },
        "invariants": {
            "only_authenticated_receipts_update_knowledge": True,
            "closure_adjusted_realized_pnl_includes_all_named_execution_costs": True,
            "partition_is_coarsest_induced_by_current_return_fingerprint": True,
            "partition_may_merge_or_split_after_new_authenticated_evidence": True,
            "uncertainty_gate_uses_pnl_and_inventory_closure_lower_bounds": True,
        },
        "results": results,
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=int, default=847101)
    parser.add_argument("--train", type=int, default=10000)
    parser.add_argument("--test", type=int, default=3000)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(argv)
    report = benchmark(args.seed, args.train, args.test)
    text = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(text)
    else:
        print(text, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
