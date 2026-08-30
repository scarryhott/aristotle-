from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Iterable, Mapping, Sequence

try:
    from experiments.nrrf849_relational_completeness_identification_price_continuum import (
        RelationalScenario,
        edges,
        identification_class,
        translate_scenario,
    )
except ModuleNotFoundError:
    from nrrf849_relational_completeness_identification_price_continuum import (
        RelationalScenario,
        edges,
        identification_class,
        translate_scenario,
    )

SCHEMA_VERSION = "nrrf850.higher_closure_profit_history_unification.v1"

Walk = tuple[str, ...]


def is_closed_walk(walk: Sequence[str]) -> bool:
    return len(walk) >= 2 and walk[0] == walk[-1]


def walk_cost(s: RelationalScenario, walk: Sequence[str]) -> Fraction:
    if not is_closed_walk(walk):
        raise ValueError("natural-form prediction is defined here only on completed round trips")
    return sum(s.costs[(walk[i], walk[i + 1])] for i in range(len(walk) - 1))


def roundtrip_profit(s: RelationalScenario, walk: Sequence[str]) -> Fraction:
    return -walk_cost(s, walk)


@dataclass(frozen=True)
class ProfitNaturalForm:
    """First-order natural form: the complete supplied round-trip profit functional."""

    walks: tuple[Walk, ...]
    profits: tuple[Fraction, ...]

    def profit_of(self, walk: Walk) -> Fraction:
        return self.profits[self.walks.index(walk)]


@dataclass(frozen=True)
class HistoryMorphism:
    """Second-order translation between two first-order natural forms."""

    walks: tuple[Walk, ...]
    delta_profit: tuple[Fraction, ...]

    @staticmethod
    def identity(walks: Sequence[Walk]) -> "HistoryMorphism":
        ws = tuple(walks)
        return HistoryMorphism(ws, tuple(Fraction(0) for _ in ws))

    def inverse(self) -> "HistoryMorphism":
        return HistoryMorphism(self.walks, tuple(-x for x in self.delta_profit))

    def compose(self, other: "HistoryMorphism") -> "HistoryMorphism":
        if self.walks != other.walks:
            raise ValueError("history morphisms must use the same completed-walk universe")
        return HistoryMorphism(
            self.walks,
            tuple(a + b for a, b in zip(self.delta_profit, other.delta_profit)),
        )


@dataclass(frozen=True)
class HigherClosureState:
    identification: object
    natural_form: ProfitNaturalForm


def profit_natural_form(s: RelationalScenario, walks: Iterable[Walk]) -> ProfitNaturalForm:
    ws = tuple(walks)
    if any(not is_closed_walk(w) for w in ws):
        raise ValueError("all natural-form observations must be completed round trips")
    return ProfitNaturalForm(ws, tuple(roundtrip_profit(s, w) for w in ws))


def higher_state(s: RelationalScenario, walks: Iterable[Walk]) -> HigherClosureState:
    return HigherClosureState(identification_class(s), profit_natural_form(s, walks))


def history(source: ProfitNaturalForm, target: ProfitNaturalForm) -> HistoryMorphism:
    if source.walks != target.walks:
        raise ValueError("natural forms must use the same completed-walk universe")
    return HistoryMorphism(
        source.walks,
        tuple(b - a for a, b in zip(source.profits, target.profits)),
    )


def apply_history(source: ProfitNaturalForm, h: HistoryMorphism) -> ProfitNaturalForm:
    if source.walks != h.walks:
        raise ValueError("natural form and history must use the same walk universe")
    return ProfitNaturalForm(
        source.walks,
        tuple(a + d for a, d in zip(source.profits, h.delta_profit)),
    )


def higher_loop_curvature(loop: Sequence[HistoryMorphism]) -> tuple[Fraction, ...]:
    """Second-order curvature: net change of the profit functional around a history loop."""
    if not loop:
        return tuple()
    walks = loop[0].walks
    if any(h.walks != walks for h in loop):
        raise ValueError("all history morphisms must use the same walk universe")
    return tuple(sum(h.delta_profit[i] for h in loop) for i in range(len(walks)))


def higher_flat(loop: Sequence[HistoryMorphism]) -> bool:
    return all(x == 0 for x in higher_loop_curvature(loop))


def add_costs(
    s: RelationalScenario,
    adversary: Mapping[tuple[str, str], Fraction],
) -> RelationalScenario:
    c = {e: s.costs[e] + adversary[e] for e in edges(s.vertices)}
    return RelationalScenario(s.vertices, s.base, c, s.social)


def uniform_fee(s: RelationalScenario, fee: Fraction) -> RelationalScenario:
    return RelationalScenario(
        s.vertices,
        s.base,
        {e: s.costs[e] + fee for e in edges(s.vertices)},
        s.social,
    )


def mean_profit(form: ProfitNaturalForm, walk: Walk) -> Fraction:
    return form.profit_of(walk) / Fraction(len(walk) - 1)


def max_mean_roundtrip_profit(form: ProfitNaturalForm) -> tuple[Fraction, Walk]:
    if not form.walks:
        raise ValueError("at least one completed walk is required")
    return max((mean_profit(form, w), w) for w in form.walks)


def critical_uniform_fee(form: ProfitNaturalForm) -> Fraction:
    """Fee per traversed edge that moves the best mean completed walk to zero."""
    return max_mean_roundtrip_profit(form)[0]


def translate_preserves_higher_state(
    s: RelationalScenario,
    phi: Mapping[str, Fraction],
    walks: Iterable[Walk],
) -> bool:
    translated = translate_scenario(s, phi)
    return profit_natural_form(s, walks) == profit_natural_form(translated, walks)


def contextual_history_distortion(
    h: HistoryMorphism,
    walk: Walk,
    amount: Fraction,
) -> HistoryMorphism:
    """Explicit adversarial second-order perturbation for negative tests.

    Unlike a first-order token-potential translation, this changes the transport
    of the round-trip profit law itself and can therefore create higher curvature.
    """
    values = list(h.delta_profit)
    values[h.walks.index(walk)] += amount
    return HistoryMorphism(h.walks, tuple(values))
