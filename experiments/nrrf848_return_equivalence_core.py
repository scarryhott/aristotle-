from __future__ import annotations

import hashlib
import json
import math
import statistics
from collections import defaultdict
from dataclasses import dataclass
from typing import Hashable, Iterable, Mapping


@dataclass(frozen=True)
class ClosureReceipt:
    authenticated: bool
    operation: str
    gross_bps: float
    realized_costs: Mapping[str, float]
    inventory_closed: bool

    @property
    def realized_pnl_bps(self) -> float:
        return self.gross_bps - sum(float(v) for v in self.realized_costs.values())


class ReturnLaw:
    def __init__(self) -> None:
        self.pnl: list[float] = []
        self.closed: list[int] = []
        self.costs: dict[str, list[float]] = defaultdict(list)

    def add(self, receipt: ClosureReceipt) -> None:
        self.pnl.append(receipt.realized_pnl_bps)
        self.closed.append(int(receipt.inventory_closed))
        for key, value in receipt.realized_costs.items():
            self.costs[str(key)].append(float(value))

    @property
    def n(self) -> int:
        return len(self.pnl)

    @property
    def mean_pnl(self) -> float:
        return statistics.fmean(self.pnl) if self.pnl else 0.0

    @property
    def close_rate(self) -> float:
        return statistics.fmean(self.closed) if self.closed else 0.0

    def pnl_lcb(self, z: float) -> float:
        if self.n < 2:
            return float("-inf")
        return self.mean_pnl - z * statistics.stdev(self.pnl) / math.sqrt(self.n)

    def closure_lcb(self, z: float) -> float:
        if self.n == 0:
            return 0.0
        p = self.close_rate
        n = self.n
        den = 1.0 + z * z / n
        center = (p + z * z / (2.0 * n)) / den
        radius = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / den
        return max(0.0, center - radius)

    def mean_cost(self, key: str) -> float:
        values = self.costs.get(key, ())
        return statistics.fmean(values) if values else 0.0


class ReturnEquivalenceClosure:
    """Generic closure learner over arbitrary operations and arbitrary cost names.

    `cell` is any hashable pre-operation observational state.  The token/bubble is
    not the cell itself: cells are quotiented by their learned conditional return
    fingerprints.  The quotient is rebuilt after authenticated evidence, so cells
    can merge or split while the evidence set itself only grows.
    """

    def __init__(
        self,
        operations: Iterable[str],
        *,
        min_cell_samples: int = 4,
        pnl_tolerance_bps: float = 2.0,
        closure_tolerance: float = 0.10,
        cost_tolerance_bps: float = 2.0,
    ) -> None:
        self.operations = tuple(dict.fromkeys(str(op) for op in operations))
        if not self.operations:
            raise ValueError("at least one operation is required")
        self.min_cell_samples = min_cell_samples
        self.pnl_tolerance_bps = pnl_tolerance_bps
        self.closure_tolerance = closure_tolerance
        self.cost_tolerance_bps = cost_tolerance_bps
        self._laws: dict[Hashable, dict[str, ReturnLaw]] = defaultdict(lambda: defaultdict(ReturnLaw))
        self._partition: dict[Hashable, tuple[object, ...]] = {}
        self._evidence_chain: list[str] = []
        self._dirty = True

    @property
    def evidence_count(self) -> int:
        return len(self._evidence_chain)

    @property
    def evidence_tip(self) -> str | None:
        return self._evidence_chain[-1] if self._evidence_chain else None

    def observe(self, cell: Hashable, receipt: ClosureReceipt) -> bool:
        if not receipt.authenticated:
            return False
        if receipt.operation not in self.operations:
            raise ValueError(f"unknown operation: {receipt.operation}")
        self._laws[cell][receipt.operation].add(receipt)
        payload = {
            "cell": repr(cell),
            "operation": receipt.operation,
            "gross_bps": receipt.gross_bps,
            "costs": dict(sorted((str(k), float(v)) for k, v in receipt.realized_costs.items())),
            "inventory_closed": receipt.inventory_closed,
            "realized_pnl_bps": receipt.realized_pnl_bps,
            "previous": self.evidence_tip,
        }
        raw = json.dumps(payload, sort_keys=True, separators=(",", ":"))
        self._evidence_chain.append(hashlib.sha256(raw.encode()).hexdigest())
        self._dirty = True
        return True

    def _fingerprint(self, cell: Hashable) -> tuple[object, ...]:
        parts: list[object] = []
        for operation in self.operations:
            law = self._laws[cell].get(operation)
            if law is None or law.n < self.min_cell_samples:
                parts.append((operation, "UNKNOWN"))
                continue
            cost_keys = sorted(law.costs)
            cost_signature = tuple(
                (key, round(law.mean_cost(key) / self.cost_tolerance_bps))
                for key in cost_keys
            )
            parts.append(
                (
                    operation,
                    round(law.mean_pnl / self.pnl_tolerance_bps),
                    round(law.close_rate / self.closure_tolerance),
                    cost_signature,
                )
            )
        return tuple(parts)

    def rebuild(self) -> None:
        if not self._dirty:
            return
        self._partition = {cell: self._fingerprint(cell) for cell in self._laws}
        self._dirty = False

    def bubble(self, cell: Hashable) -> tuple[object, ...] | None:
        self.rebuild()
        return self._partition.get(cell)

    @property
    def bubble_count(self) -> int:
        self.rebuild()
        return len(set(self._partition.values()))

    @property
    def cell_count(self) -> int:
        return len(self._laws)

    def _aggregate(self, bubble: tuple[object, ...], operation: str) -> ReturnLaw:
        result = ReturnLaw()
        for cell, token in self._partition.items():
            if token != bubble:
                continue
            law = self._laws[cell].get(operation)
            if law is None:
                continue
            result.pnl.extend(law.pnl)
            result.closed.extend(law.closed)
            for key, values in law.costs.items():
                result.costs[key].extend(values)
        return result

    def select(
        self,
        cell: Hashable,
        *,
        min_bubble_samples: int = 10,
        pnl_margin_bps: float = 0.10,
        closure_floor: float = 0.90,
        z: float = 1.28,
    ) -> str:
        bubble = self.bubble(cell)
        if bubble is None:
            return "HOLD"
        candidates: list[tuple[float, str]] = []
        for operation in self.operations:
            law = self._aggregate(bubble, operation)
            if law.n < min_bubble_samples:
                continue
            pnl_lcb = law.pnl_lcb(z)
            closure_lcb = law.closure_lcb(z)
            if pnl_lcb > pnl_margin_bps and closure_lcb > closure_floor:
                candidates.append((pnl_lcb, operation))
        return max(candidates)[1] if candidates else "HOLD"

    def snapshot(self) -> dict[str, object]:
        self.rebuild()
        return {
            "evidence_count": self.evidence_count,
            "cell_count": self.cell_count,
            "bubble_count": self.bubble_count,
            "evidence_tip": self.evidence_tip,
            "knowledge_monotone_by_construction": True,
            "partition_rebuilds_from_authenticated_return_law": True,
        }
