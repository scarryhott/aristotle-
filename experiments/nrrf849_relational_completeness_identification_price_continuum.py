from __future__ import annotations

import hashlib
import json
import math
import statistics
from collections import defaultdict
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from typing import Iterable, Mapping, Sequence

SCHEMA_VERSION = "nrrf849.relational_completeness_identification_price_continuum.v1"


@dataclass(frozen=True)
class RelationalScenario:
    vertices: tuple[str, ...]
    base: str
    costs: Mapping[tuple[str, str], Fraction]
    social: Mapping[str, Fraction]


@dataclass(frozen=True)
class EconomicReceipt:
    authenticated: bool
    operation: str
    gross_bps: float
    realized_costs: Mapping[str, float]
    inventory_closed: bool

    @property
    def realized_pnl_bps(self) -> float:
        return self.gross_bps - sum(float(v) for v in self.realized_costs.values())


@dataclass(frozen=True)
class IdentificationClass:
    gauge: tuple[str, ...]
    social_descended: tuple[str, ...]
    price_chart: tuple[float, ...]


def edges(vertices: Sequence[str]) -> tuple[tuple[str, str], ...]:
    return tuple(product(vertices, vertices))


def translate_scenario(s: RelationalScenario, phi: Mapping[str, Fraction]) -> RelationalScenario:
    c = {(x, y): s.costs[(x, y)] + phi[y] - phi[x] for x, y in edges(s.vertices)}
    social = {x: s.social[x] + phi[x] for x in s.vertices}
    return RelationalScenario(s.vertices, s.base, c, social)


def return2(s: RelationalScenario, y: str) -> Fraction:
    return s.costs[(s.base, y)] + s.costs[(y, s.base)]


def triangle(s: RelationalScenario, x: str, y: str) -> Fraction:
    return s.costs[(s.base, x)] + s.costs[(x, y)] + s.costs[(y, s.base)]


def canonical_gauge(s: RelationalScenario) -> dict[tuple[str, str], Fraction]:
    return {(x, y): triangle(s, x, y) - return2(s, y) for x, y in edges(s.vertices)}


def completed_roundtrip_observations(s: RelationalScenario) -> tuple[str, ...]:
    values = [str(return2(s, y)) for y in s.vertices]
    values.extend(str(triangle(s, x, y)) for x, y in edges(s.vertices))
    return tuple(values)


def descended_social_relation(s: RelationalScenario) -> dict[tuple[str, str], Fraction]:
    """Social/economic relation in the same translation quotient.

    The invariant chart is (social[y]-social[x]) - (cost[x,y]-gauge[x,y]).
    Since cost-gauge is exactly the translational potential difference, this
    descends raw social coordinates through the same identification relation.
    """
    g = canonical_gauge(s)
    return {
        (x, y): (s.social[y] - s.social[x]) - (s.costs[(x, y)] - g[(x, y)])
        for x, y in edges(s.vertices)
    }


def price_chart(s: RelationalScenario) -> dict[tuple[str, str], float]:
    """Finite monotone chart of the relative cost class for executable tests.

    This is not a claim that market prices obey this formula.  It witnesses the
    architectural condition that price is a function of identified relative
    history, not of an absolute presentation.
    """
    g = canonical_gauge(s)
    return {e: 1.0 / (1.0 + abs(float(g[e]))) for e in edges(s.vertices)}


def identification_class(s: RelationalScenario) -> IdentificationClass:
    es = edges(s.vertices)
    g = canonical_gauge(s)
    social = descended_social_relation(s)
    price = price_chart(s)
    return IdentificationClass(
        gauge=tuple(str(g[e]) for e in es),
        social_descended=tuple(str(social[e]) for e in es),
        price_chart=tuple(price[e] for e in es),
    )


def relationally_identified(a: RelationalScenario, b: RelationalScenario) -> bool:
    return identification_class(a) == identification_class(b)


def relation_complete(s: RelationalScenario) -> bool:
    """Finite completeness condition for this protocol.

    Every gauge entry is reconstructible from one triangle and one return loop.
    """
    g = canonical_gauge(s)
    return all(triangle(s, x, y) - return2(s, y) == g[(x, y)] for x, y in edges(s.vertices))


class ContinuumLearner:
    def __init__(self, operations: Iterable[str]) -> None:
        self.operations = tuple(operations)
        self.memory: dict[IdentificationClass, dict[str, list[float]]] = defaultdict(lambda: defaultdict(list))
        self.closed: dict[IdentificationClass, dict[str, list[int]]] = defaultdict(lambda: defaultdict(list))
        self.cost_names: set[str] = set()
        self.evidence_chain: list[str] = []

    @staticmethod
    def _hash(payload: object) -> str:
        raw = json.dumps(payload, sort_keys=True, default=str, separators=(",", ":"))
        return hashlib.sha256(raw.encode()).hexdigest()

    @property
    def evidence_count(self) -> int:
        return len(self.evidence_chain)

    def observe(self, scenario: RelationalScenario, receipt: EconomicReceipt) -> bool:
        if not receipt.authenticated:
            return False
        cls = identification_class(scenario)
        self.memory[cls][receipt.operation].append(receipt.realized_pnl_bps)
        self.closed[cls][receipt.operation].append(1 if receipt.inventory_closed else 0)
        self.cost_names.update(receipt.realized_costs)
        payload = {
            "class": cls.gauge,
            "social": cls.social_descended,
            "operation": receipt.operation,
            "pnl": receipt.realized_pnl_bps,
            "closed": receipt.inventory_closed,
            "costs": dict(receipt.realized_costs),
            "previous": self.evidence_chain[-1] if self.evidence_chain else None,
        }
        self.evidence_chain.append(self._hash(payload))
        return True

    def choose(
        self,
        scenario: RelationalScenario,
        *,
        min_samples: int = 12,
        pnl_margin_bps: float = 0.25,
        closure_floor: float = 0.90,
        z: float = 1.28,
    ) -> str:
        cls = identification_class(scenario)
        candidates: list[tuple[float, str]] = []
        for op in self.operations:
            pnl = self.memory[cls][op]
            closed = self.closed[cls][op]
            if len(pnl) < min_samples:
                continue
            mean = statistics.fmean(pnl)
            sd = statistics.stdev(pnl) if len(pnl) > 1 else 0.0
            lcb = mean - z * sd / math.sqrt(len(pnl))
            p = statistics.fmean(closed)
            if lcb > pnl_margin_bps and p >= closure_floor:
                candidates.append((lcb, op))
        return max(candidates)[1] if candidates else "HOLD"

    def snapshot(self) -> dict[str, object]:
        return {
            "schema_version": SCHEMA_VERSION,
            "identified_classes": len(self.memory),
            "evidence_count": self.evidence_count,
            "cost_names": sorted(self.cost_names),
            "knowledge_monotone": True,
        }
