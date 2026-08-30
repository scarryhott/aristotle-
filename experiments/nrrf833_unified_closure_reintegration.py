"""NRRF833 true-unification reintegration.

This module does not add another trading strategy.  It makes fees, book state,
execution, cash/inventory accounting, learning, environmental partitioning, and
receipt memory projections of one state transition:

    X_t --Phi--> X_{t+1}

The knowledge component is extensive by construction.  New evidence can add a
natural execution form or refine a previously observed form, but it cannot erase
prior evidence or another form's learned state.  Point-prediction error remains
an empirical quantity and is deliberately *not* forced to be monotone.
"""

from __future__ import annotations

import argparse
import copy
import json
from dataclasses import dataclass
from decimal import Decimal, ROUND_FLOOR
from pathlib import Path
from typing import Mapping, Sequence

from experiments import nrrf833_fee_pricing_closure_learning as sim

D0 = Decimal("0")
D1 = Decimal("1")
SCHEMA_VERSION = "nrrf833.unified_closure.v1"


def _d(value: object) -> Decimal:
    return sim.dec(value)


def _floor_int(value: Decimal) -> int:
    return int(value.to_integral_value(rounding=ROUND_FLOOR))


def _pow2_bucket(value: Decimal) -> int:
    """Deterministic log2-like bucket without binary floating point."""
    value = _d(value)
    if value <= 0:
        return -64
    bucket = 0
    two = Decimal(2)
    while value >= two and bucket < 64:
        value /= two
        bucket += 1
    while value < D1 and bucket > -64:
        value *= two
        bucket -= 1
    return bucket


def learner_from_state(payload: Mapping[str, object]) -> sim.ClosureLearner:
    """Reconstruct exactly the mutable learner contained in a closure state."""
    return sim.ClosureLearner(
        learning_rate=_d(payload["learning_rate"]),
        base_uncertainty_bps=_d(payload["base_uncertainty_bps"]),
        taker_exit_execution_bps=_d(payload["taker_exit_execution_bps"]),
        positive_model_error_bps=_d(payload["positive_model_error_bps"]),
        absolute_model_error_bps=_d(payload["absolute_model_error_bps"]),
        signal_optimism_bps=_d(payload["signal_optimism_bps"]),
        maker_adverse_selection_bps=_d(payload["maker_adverse_selection_bps"]),
        maker_entry_alpha=_d(payload["maker_entry_alpha"]),
        maker_entry_beta=_d(payload["maker_entry_beta"]),
        maker_exit_alpha=_d(payload["maker_exit_alpha"]),
        maker_exit_beta=_d(payload["maker_exit_beta"]),
        closed_observations=int(payload["closed_observations"]),
        no_fill_observations=int(payload["no_fill_observations"]),
    )


@dataclass(frozen=True, order=True)
class NaturalExecutionForm:
    """A pre-trade partition derived only from observable execution relations.

    Human labels such as CALM/ADVERSE are intentionally absent.  The form is a
    quotient reading of venue, symbol, fee tier, spread geometry, top-depth
    capacity, and top-of-book imbalance.
    """

    venue: str
    symbol: str
    fee_tier: str
    spread_band_2bps: int
    top_depth_pow2: int
    imbalance_decile: int

    @property
    def key(self) -> str:
        return (
            f"{self.venue}|{self.symbol}|{self.fee_tier}|"
            f"s{self.spread_band_2bps}|d{self.top_depth_pow2}|i{self.imbalance_decile}"
        )

    def to_dict(self) -> dict[str, object]:
        return {
            "venue": self.venue,
            "symbol": self.symbol,
            "fee_tier": self.fee_tier,
            "spread_band_2bps": self.spread_band_2bps,
            "top_depth_pow2": self.top_depth_pow2,
            "imbalance_decile": self.imbalance_decile,
            "key": self.key,
        }


def derive_natural_form(
    *,
    episode: sim.Episode,
    schedule: sim.FeeSchedule,
    effective_volume: Decimal,
) -> NaturalExecutionForm:
    book = episode.entry_book
    tier = schedule.tier_for(effective_volume)
    spread_band = _floor_int(book.spread_bps / Decimal(2))
    top_depth_quote = (book.bids[0].quantity + book.asks[0].quantity) * book.midpoint
    depth_ratio = top_depth_quote / episode.quote_budget
    total_top = book.bids[0].quantity + book.asks[0].quantity
    bid_share = book.bids[0].quantity / total_top
    imbalance = min(9, max(0, _floor_int(bid_share * Decimal(10))))
    return NaturalExecutionForm(
        venue=book.venue,
        symbol=book.symbol,
        fee_tier=tier.name,
        spread_band_2bps=spread_band,
        top_depth_pow2=_pow2_bucket(depth_ratio),
        imbalance_decile=imbalance,
    )


@dataclass(frozen=True)
class FormMemory:
    form: NaturalExecutionForm
    learner_state: Mapping[str, object]
    evidence_hashes: tuple[str, ...]
    closed_return_count: int
    no_fill_count: int
    mean_abs_cost_error_bps: Decimal | None
    last_abs_cost_error_bps: Decimal | None

    def to_dict(self) -> dict[str, object]:
        return sim.canonicalize(
            {
                "form": self.form.to_dict(),
                "learner_state": dict(self.learner_state),
                "evidence_hashes": list(self.evidence_hashes),
                "closed_return_count": self.closed_return_count,
                "no_fill_count": self.no_fill_count,
                "mean_abs_cost_error_bps": self.mean_abs_cost_error_bps,
                "last_abs_cost_error_bps": self.last_abs_cost_error_bps,
            }
        )


@dataclass(frozen=True)
class KnowledgeLattice:
    """Persistent empirical closure memory ordered by evidence inclusion."""

    forms: Mapping[str, FormMemory]
    evidence_hashes: tuple[str, ...]

    @classmethod
    def empty(cls) -> "KnowledgeLattice":
        return cls(forms={}, evidence_hashes=())

    @property
    def form_count(self) -> int:
        return len(self.forms)

    @property
    def evidence_count(self) -> int:
        return len(self.evidence_hashes)

    def memory_for(self, form: NaturalExecutionForm) -> FormMemory | None:
        return self.forms.get(form.key)

    def precedes(self, other: "KnowledgeLattice") -> bool:
        """Closure order K_t <= K_t+1: no evidence or learned form is erased."""
        if not set(self.evidence_hashes).issubset(other.evidence_hashes):
            return False
        if not set(self.forms).issubset(other.forms):
            return False
        for key, old in self.forms.items():
            new = other.forms[key]
            if not set(old.evidence_hashes).issubset(new.evidence_hashes):
                return False
            if old.closed_return_count > new.closed_return_count:
                return False
            if old.no_fill_count > new.no_fill_count:
                return False
        return True

    def admit(
        self,
        *,
        form: NaturalExecutionForm,
        learner_state: Mapping[str, object],
        evidence_hash: str,
        receipt: sim.ClosureReceipt,
        abs_cost_error_bps: Decimal | None,
    ) -> "KnowledgeLattice":
        old = self.memory_for(form)
        old_evidence = set(old.evidence_hashes if old else ())
        new_form_evidence = tuple(sorted(old_evidence | {evidence_hash}))
        closed_increment = int(receipt.state == "CLOSED_RETURN")
        no_fill_increment = int(receipt.state == "CLOSED_NO_ENTRY_FILL")
        old_closed = old.closed_return_count if old else 0
        old_no_fill = old.no_fill_count if old else 0
        old_mean = old.mean_abs_cost_error_bps if old else None

        if abs_cost_error_bps is None:
            new_mean = old_mean
        elif old_mean is None or old_closed == 0:
            new_mean = abs_cost_error_bps
        else:
            # The current closing return is the (old_closed + 1)-th observation.
            new_mean = (
                old_mean * Decimal(old_closed) + abs_cost_error_bps
            ) / Decimal(old_closed + 1)

        memory = FormMemory(
            form=form,
            learner_state=copy.deepcopy(dict(learner_state)),
            evidence_hashes=new_form_evidence,
            closed_return_count=old_closed + closed_increment,
            no_fill_count=old_no_fill + no_fill_increment,
            mean_abs_cost_error_bps=new_mean,
            last_abs_cost_error_bps=(
                abs_cost_error_bps
                if abs_cost_error_bps is not None
                else (old.last_abs_cost_error_bps if old else None)
            ),
        )
        forms = dict(self.forms)
        forms[form.key] = memory
        all_evidence = tuple(sorted(set(self.evidence_hashes) | {evidence_hash}))
        return KnowledgeLattice(forms=forms, evidence_hashes=all_evidence)

    def to_dict(self) -> dict[str, object]:
        return sim.canonicalize(
            {
                "form_count": self.form_count,
                "evidence_count": self.evidence_count,
                "evidence_hashes": list(self.evidence_hashes),
                "forms": {key: value.to_dict() for key, value in sorted(self.forms.items())},
            }
        )


@dataclass(frozen=True)
class UnifiedClosureState:
    """One state containing the full trading/environment closure."""

    rules: sim.InstrumentRules
    schedule: sim.FeeSchedule
    global_learner_state: Mapping[str, object]
    rolling_volume_daily: Mapping[str, str]
    knowledge: KnowledgeLattice
    sequence: int
    previous_receipt_hash: str
    previous_transition_hash: str

    @classmethod
    def initial(
        cls,
        *,
        rules: sim.InstrumentRules,
        schedule: sim.FeeSchedule,
        learner: sim.ClosureLearner,
        rolling_volume: sim.Rolling30DayVolume,
    ) -> "UnifiedClosureState":
        genesis = sim.sha256_value(
            {
                "schema_version": SCHEMA_VERSION,
                "rules": rules.to_dict(),
                "schedule": schedule.to_dict(),
                "learner": learner.to_dict(),
                "rolling_volume": rolling_volume.to_dict(),
                "knowledge": KnowledgeLattice.empty().to_dict(),
            }
        )
        return cls(
            rules=rules,
            schedule=schedule,
            global_learner_state=copy.deepcopy(learner.to_dict()),
            rolling_volume_daily=copy.deepcopy(rolling_volume.to_dict()),
            knowledge=KnowledgeLattice.empty(),
            sequence=0,
            previous_receipt_hash=genesis,
            previous_transition_hash=genesis,
        )

    def rolling_volume(self) -> sim.Rolling30DayVolume:
        volume = sim.Rolling30DayVolume()
        for day_text, amount_text in self.rolling_volume_daily.items():
            volume.daily_usd[sim.date.fromisoformat(day_text)] = _d(amount_text)
        return volume

    def to_dict(self) -> dict[str, object]:
        return sim.canonicalize(
            {
                "schema_version": SCHEMA_VERSION,
                "rules": self.rules.to_dict(),
                "schedule": self.schedule.to_dict(),
                "global_learner_state": dict(self.global_learner_state),
                "rolling_volume_daily": dict(self.rolling_volume_daily),
                "knowledge": self.knowledge.to_dict(),
                "sequence": self.sequence,
                "previous_receipt_hash": self.previous_receipt_hash,
                "previous_transition_hash": self.previous_transition_hash,
            }
        )

    @property
    def state_hash(self) -> str:
        return sim.sha256_value(self.to_dict())


@dataclass(frozen=True)
class UnifiedTransition:
    sequence: int
    form: NaturalExecutionForm
    decision: sim.Decision
    receipt: sim.ClosureReceipt
    abs_cost_error_bps: Decimal | None
    used_form_memory: bool
    knowledge_extensive: bool
    state_before_hash: str
    state_after_hash: str
    previous_transition_hash: str
    transition_hash: str
    evidence_hash: str

    def to_dict(self) -> dict[str, object]:
        return sim.canonicalize(
            {
                "schema_version": SCHEMA_VERSION,
                "sequence": self.sequence,
                "form": self.form.to_dict(),
                "decision": self.decision.to_dict(),
                "receipt": self.receipt.to_dict(),
                "abs_cost_error_bps": self.abs_cost_error_bps,
                "used_form_memory": self.used_form_memory,
                "knowledge_extensive": self.knowledge_extensive,
                "state_before_hash": self.state_before_hash,
                "state_after_hash": self.state_after_hash,
                "previous_transition_hash": self.previous_transition_hash,
                "transition_hash": self.transition_hash,
                "evidence_hash": self.evidence_hash,
            }
        )


def _abs_structural_cost_error(
    decision: sim.Decision, receipt: sim.ClosureReceipt
) -> Decimal | None:
    if (
        not receipt.eligible_for_learning
        or receipt.actual_total_cost_bps is None
        or receipt.entry_fill is None
        or receipt.entry_fill.gross_quote == 0
    ):
        return None
    structural_prediction = max(
        decision.predicted_total_cost_bps - decision.uncertainty_buffer_bps,
        D0,
    )
    return abs(receipt.actual_total_cost_bps - structural_prediction)


class UnifiedClosureOperator:
    """The single trading/environment evolution operator Phi."""

    def __init__(self, *, force_route: sim.Route | None = None) -> None:
        self.force_route = force_route

    def transition(
        self, state: UnifiedClosureState, episode: sim.Episode
    ) -> tuple[UnifiedClosureState, UnifiedTransition]:
        if episode.entry_book.symbol != state.rules.symbol:
            raise sim.SimulationError("episode symbol is outside the unified state")
        if episode.entry_book.venue != state.rules.venue:
            raise sim.SimulationError("episode venue is outside the unified state")

        volume = state.rolling_volume()
        trading_day = episode.entry_book.timestamp_utc.date()
        effective_volume = volume.effective_volume(trading_day)
        form = derive_natural_form(
            episode=episode,
            schedule=state.schedule,
            effective_volume=effective_volume,
        )

        prior_memory = state.knowledge.memory_for(form)
        global_learner = learner_from_state(state.global_learner_state)
        local_learner = (
            learner_from_state(prior_memory.learner_state)
            if prior_memory is not None
            else copy.deepcopy(global_learner)
        )

        decision = local_learner.decide(
            episode=episode,
            rules=state.rules,
            schedule=state.schedule,
            effective_volume=effective_volume,
            force_route=self.force_route,
        )
        receipt = sim.execute_episode(
            episode=episode,
            decision=decision,
            rules=state.rules,
            schedule=state.schedule,
            effective_volume=effective_volume,
            previous_receipt_hash=state.previous_receipt_hash,
        )
        if not sim.verify_receipt_hash(receipt):
            raise AssertionError("unified transition produced an invalid receipt hash")

        # Two projections of one return: local natural-form memory and global
        # transfer memory.  Existing form memories are not overwritten by other
        # forms; the global learner supplies only the prior for a never-seen form.
        local_learner.update(decision, receipt)
        global_learner.update(decision, receipt)
        abs_error = _abs_structural_cost_error(decision, receipt)

        evidence_hash = sim.sha256_value(
            {
                "form": form.to_dict(),
                "episode": episode.to_dict(),
                "decision": decision.to_dict(),
                "receipt": receipt.to_dict(),
            }
        )
        knowledge = state.knowledge.admit(
            form=form,
            learner_state=local_learner.to_dict(),
            evidence_hash=evidence_hash,
            receipt=receipt,
            abs_cost_error_bps=abs_error,
        )
        extensive = state.knowledge.precedes(knowledge)
        if not extensive:
            raise AssertionError("knowledge closure contracted")

        volume.record(trading_day, sim.gross_volume_from_receipt(receipt))
        before_hash = state.state_hash
        transition_payload = {
            "schema_version": SCHEMA_VERSION,
            "sequence": state.sequence,
            "state_before_hash": before_hash,
            "previous_transition_hash": state.previous_transition_hash,
            "form": form.to_dict(),
            "evidence_hash": evidence_hash,
            "receipt_hash": receipt.receipt_hash,
            "local_learner_after": local_learner.to_dict(),
            "global_learner_after": global_learner.to_dict(),
            "knowledge_after": knowledge.to_dict(),
            "rolling_volume_after": volume.to_dict(),
        }
        transition_hash = sim.sha256_value(transition_payload)
        next_state = UnifiedClosureState(
            rules=state.rules,
            schedule=state.schedule,
            global_learner_state=copy.deepcopy(global_learner.to_dict()),
            rolling_volume_daily=copy.deepcopy(volume.to_dict()),
            knowledge=knowledge,
            sequence=state.sequence + 1,
            previous_receipt_hash=receipt.receipt_hash,
            previous_transition_hash=transition_hash,
        )
        event = UnifiedTransition(
            sequence=state.sequence,
            form=form,
            decision=decision,
            receipt=receipt,
            abs_cost_error_bps=abs_error,
            used_form_memory=prior_memory is not None,
            knowledge_extensive=extensive,
            state_before_hash=before_hash,
            state_after_hash=next_state.state_hash,
            previous_transition_hash=state.previous_transition_hash,
            transition_hash=transition_hash,
            evidence_hash=evidence_hash,
        )
        return next_state, event


def run_unified(
    *,
    episodes: Sequence[sim.Episode],
    rules: sim.InstrumentRules | None = None,
    schedule: sim.FeeSchedule | None = None,
    learner: sim.ClosureLearner | None = None,
    rolling_volume: sim.Rolling30DayVolume | None = None,
    force_route: sim.Route | None = None,
) -> tuple[list[UnifiedTransition], UnifiedClosureState, dict[str, object]]:
    if not episodes:
        raise sim.SimulationError("unified run requires at least one episode")
    rules = rules or sim.alpaca_btcusd_rules()
    schedule = schedule or sim.alpaca_crypto_fee_schedule()
    learner = learner or sim.ClosureLearner()
    rolling_volume = rolling_volume or sim.Rolling30DayVolume.seeded(
        episodes[0].entry_book.timestamp_utc.date(), D0
    )
    state = UnifiedClosureState.initial(
        rules=rules,
        schedule=schedule,
        learner=learner,
        rolling_volume=rolling_volume,
    )
    genesis_hash = state.state_hash
    operator = UnifiedClosureOperator(force_route=force_route)
    events: list[UnifiedTransition] = []
    max_residual = D0
    for episode in episodes:
        state, event = operator.transition(state, episode)
        events.append(event)
        residual = event.receipt.closure_residual_quote
        if residual is not None:
            max_residual = max(max_residual, abs(residual))

    errors = [event.abs_cost_error_bps for event in events if event.abs_cost_error_bps is not None]
    mean_error = sum(errors, D0) / Decimal(len(errors)) if errors else None
    revisits = sum(1 for event in events if event.used_form_memory)
    summary = sim.canonicalize(
        {
            "schema_version": SCHEMA_VERSION,
            "episode_count": len(events),
            "genesis_state_hash": genesis_hash,
            "final_state_hash": state.state_hash,
            "final_transition_hash": state.previous_transition_hash,
            "knowledge_form_count": state.knowledge.form_count,
            "knowledge_evidence_count": state.knowledge.evidence_count,
            "knowledge_extensive_every_transition": all(
                event.knowledge_extensive for event in events
            ),
            "form_revisit_count": revisits,
            "closed_return_count": sum(
                event.receipt.state == "CLOSED_RETURN" for event in events
            ),
            "closed_no_fill_count": sum(
                event.receipt.state == "CLOSED_NO_ENTRY_FILL" for event in events
            ),
            "hold_count": sum(event.receipt.state == "CLOSED_HOLD" for event in events),
            "mean_abs_structural_cost_error_bps": mean_error,
            "maximum_accounting_closure_residual_quote": max_residual,
            "point_prediction_error_forced_monotone": False,
            "closure_fidelity_order": "knowledge/evidence inclusion, not forced point-error monotonicity",
            "knowledge": state.knowledge.to_dict(),
        }
    )
    return events, state, summary


def _write_run(output: Path, events: Sequence[UnifiedTransition], state: UnifiedClosureState, summary: Mapping[str, object]) -> None:
    output.mkdir(parents=True, exist_ok=True)
    (output / "events.jsonl").write_text(
        "".join(json.dumps(event.to_dict(), sort_keys=True) + "\n" for event in events)
    )
    (output / "final_state.json").write_text(
        json.dumps(state.to_dict(), indent=2, sort_keys=True) + "\n"
    )
    (output / "summary.json").write_text(
        json.dumps(sim.canonicalize(summary), indent=2, sort_keys=True) + "\n"
    )


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--episodes", type=int, default=240)
    parser.add_argument("--seed", type=int, default=833)
    parser.add_argument("--quote-budget", default="20")
    parser.add_argument(
        "--output", default="runs/nrrf833_unified_closure_reintegration/latest"
    )
    args = parser.parse_args(argv)
    episodes = sim.synthetic_episodes(
        count=args.episodes,
        seed=args.seed,
        quote_budget=_d(args.quote_budget),
    )
    events, state, summary = run_unified(episodes=episodes)
    _write_run(Path(args.output), events, state, summary)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
