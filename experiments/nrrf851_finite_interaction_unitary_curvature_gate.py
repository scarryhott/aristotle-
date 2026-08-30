from __future__ import annotations

import math
import random
import statistics
from dataclasses import dataclass
from fractions import Fraction
from typing import Iterable, Sequence

SCHEMA_VERSION = "nrrf851.finite_interaction_unitary_curvature_gate.v1"

VERTICES = ("USD", "BTC", "ETH", "SOL", "HEDGE")
EDGES = (
    ("USD","BTC"),("BTC","USD"),("USD","ETH"),("ETH","USD"),
    ("USD","SOL"),("SOL","USD"),("BTC","ETH"),("ETH","BTC"),
    ("ETH","SOL"),("SOL","ETH"),("BTC","SOL"),("SOL","BTC"),
    ("BTC","HEDGE"),("HEDGE","USD"),("ETH","HEDGE"),("SOL","HEDGE"),
)

# Exact integral basis of ker(boundary) for the maze above.  The 12 basis
# coordinates are the independent closed hairs.  Profit on every closed flow
# is determined by its coordinates on this basis.
CYCLE_BASIS = (
    (1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0),
    (0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0),
    (0,0,0,0,1,1,0,0,0,0,0,0,0,0,0,0),
    (1,0,-1,0,0,0,1,0,0,0,0,0,0,0,0,0),
    (-1,0,1,0,0,0,0,1,0,0,0,0,0,0,0,0),
    (0,0,1,0,-1,0,0,0,1,0,0,0,0,0,0,0),
    (0,0,-1,0,1,0,0,0,0,1,0,0,0,0,0,0),
    (1,0,0,0,-1,0,0,0,0,0,1,0,0,0,0,0),
    (-1,0,0,0,1,0,0,0,0,0,0,1,0,0,0,0),
    (1,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0),
    (-1,0,1,0,0,0,0,0,0,0,0,0,-1,0,1,0),
    (-1,0,0,0,1,0,0,0,0,0,0,0,-1,0,0,1),
)
CYCLE_RANK = len(CYCLE_BASIS)


def dot(a: Sequence[Fraction | int | float], b: Sequence[Fraction | int | float]):
    return sum(x * y for x, y in zip(a, b))


def roundtrip_profit(cost: Sequence[Fraction], flow: Sequence[Fraction | int]) -> Fraction:
    return -dot(cost, flow)


def natural_form(cost: Sequence[Fraction]) -> tuple[Fraction, ...]:
    return tuple(roundtrip_profit(cost, q) for q in CYCLE_BASIS)


def translate_cost(cost: Sequence[Fraction], phi: dict[str, Fraction]) -> tuple[Fraction, ...]:
    return tuple(cost[j] + phi[y] - phi[x] for j, (x, y) in enumerate(EDGES))


def combine_flow(coefficients: Sequence[int | Fraction]) -> tuple[Fraction, ...]:
    out = [Fraction(0) for _ in EDGES]
    for a, basis in zip(coefficients, CYCLE_BASIS):
        for j, q in enumerate(basis):
            out[j] += Fraction(a) * q
    return tuple(out)


def predict_closed_flow_profit(form: Sequence[Fraction], coefficients: Sequence[int | Fraction]) -> Fraction:
    return sum(Fraction(a) * p for a, p in zip(coefficients, form))


def resolved_by_rank(coefficients: Sequence[int | Fraction], observed_rank: int) -> bool:
    return all(Fraction(coefficients[j]) == 0 for j in range(observed_rank, CYCLE_RANK))


@dataclass
class RunningHair:
    n: int = 0
    total: float = 0.0
    total_sq: float = 0.0
    closed: int = 0

    def clear(self) -> None:
        self.n = 0; self.total = 0.0; self.total_sq = 0.0; self.closed = 0

    def add(self, pnl: float, is_closed: bool) -> None:
        self.n += 1; self.total += pnl; self.total_sq += pnl * pnl; self.closed += int(is_closed)

    @property
    def mean(self) -> float:
        return self.total / self.n if self.n else 0.0

    @property
    def variance(self) -> float:
        if self.n < 2:
            return math.inf
        return max(0.0, (self.total_sq - self.total * self.total / self.n) / (self.n - 1))

    @property
    def se(self) -> float:
        return math.sqrt(self.variance / self.n) if self.n >= 2 else math.inf

    def lcb(self, z: float = 1.96) -> float:
        return self.mean - z * self.se if self.n >= 3 else -math.inf

    def closure_lcb(self, z: float = 1.64) -> float:
        if not self.n:
            return 0.0
        p = self.closed / self.n; n = self.n
        den = 1 + z*z/n
        center = (p + z*z/(2*n)) / den
        rad = z * math.sqrt(p*(1-p)/n + z*z/(4*n*n)) / den
        return max(0.0, center - rad)


class UnitaryCurvatureLearner:
    """Finite-basis closure learner.

    Knowledge is the authenticated evidence on independent closed hairs.
    Empirical freedom is the set of closed-flow coefficient vectors whose
    required basis hairs are certified and whose propagated profit LCB is
    positive.  A genuine curvature shock can reopen a coordinate without
    deleting prior evidence about the rest of the closure basis.
    """

    def __init__(self, rank: int = CYCLE_RANK) -> None:
        self.rank = rank
        self.hairs = [RunningHair() for _ in range(rank)]
        self.evidence = 0

    def certified(self, i: int, min_samples: int = 20, closure_floor: float = 0.92) -> bool:
        s = self.hairs[i]
        return s.n >= min_samples and s.closure_lcb() > closure_floor

    def observe(self, i: int, pnl: float, closed: bool, authenticated: bool = True) -> bool:
        if not authenticated:
            return False
        s = self.hairs[i]
        if s.n >= 35 and math.isfinite(s.variance):
            threshold = max(0.90, 4.5 * math.sqrt(s.variance))
            if abs(pnl - s.mean) > threshold:
                s.clear()
        s.add(pnl, closed)
        self.evidence += 1
        return True

    def predict(self, coeff: Sequence[int | float], z: float = 1.96):
        active = [i for i, a in enumerate(coeff) if a]
        if not active or any(not self.certified(i) for i in active):
            return None
        mean = sum(float(coeff[i]) * self.hairs[i].mean for i in active)
        sigma = math.sqrt(sum((abs(float(coeff[i])) * self.hairs[i].se) ** 2 for i in active))
        close = min(self.hairs[i].closure_lcb() for i in active)
        return mean, mean - z*sigma, mean + z*sigma, close

    def admit(self, coeff: Sequence[int | float], margin: float = 0.20) -> bool:
        pred = self.predict(coeff)
        return bool(pred and pred[1] > margin and pred[3] > 0.92)


def exact_regression(seed: int = 851201, environments: int = 250, flows_per_environment: int = 25) -> dict[str, int]:
    rng = random.Random(seed)
    translation_failures = 0
    prediction_failures = 0
    pointwise_changed = 0
    for _ in range(environments):
        cost = tuple(Fraction(rng.randint(-80, 80), 13) for _ in EDGES)
        phi = {v: Fraction(rng.randint(-500, 500), 17) for v in VERTICES}; phi["USD"] = Fraction(0)
        translated = translate_cost(cost, phi)
        pointwise_changed += int(cost != translated)
        form = natural_form(cost)
        translation_failures += int(form != natural_form(translated))
        for _ in range(flows_per_environment):
            coeff = tuple(rng.randint(-4, 4) for _ in range(CYCLE_RANK))
            flow = combine_flow(coeff)
            prediction_failures += int(roundtrip_profit(cost, flow) != predict_closed_flow_profit(form, coeff))
    return {
        "environments": environments,
        "closed_flows": environments * flows_per_environment,
        "pointwise_changed": pointwise_changed,
        "translation_failures": translation_failures,
        "prediction_failures": prediction_failures,
    }


def finite_rank_reach(seed: int = 851203, trials: int = 4000) -> list[dict[str, float | int]]:
    rng = random.Random(seed)
    out = []
    for k in range(CYCLE_RANK + 1):
        resolved = 0
        for _ in range(trials):
            coeff = tuple(rng.randint(-2, 2) for _ in range(CYCLE_RANK))
            resolved += int(resolved_by_rank(coeff, k))
        out.append({
            "observed_rank": k,
            "cycle_rank": CYCLE_RANK,
            "resolved_share": resolved / trials,
            "unresolved_share": 1 - resolved / trials,
            "resolved_prediction_error": 0.0,
        })
    return out
