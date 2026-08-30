from __future__ import annotations

from dataclasses import replace
from decimal import Decimal

from experiments import nrrf833_fee_pricing_closure_learning as sim
from experiments import nrrf833_unified_closure_reintegration as unified

D = Decimal


def initial_state(episodes: list[sim.Episode]) -> unified.UnifiedClosureState:
    return unified.UnifiedClosureState.initial(
        rules=sim.alpaca_btcusd_rules(),
        schedule=sim.alpaca_crypto_fee_schedule(),
        learner=sim.ClosureLearner(),
        rolling_volume=sim.Rolling30DayVolume.seeded(
            episodes[0].entry_book.timestamp_utc.date(), D("0")
        ),
    )


def test_one_operator_closes_every_admitted_accounting_return() -> None:
    episodes = sim.synthetic_episodes(count=80, seed=833)
    events, _, summary = unified.run_unified(episodes=episodes)
    assert summary["maximum_accounting_closure_residual_quote"] == "0"
    assert all(
        event.receipt.closure_residual_quote in (None, D("0")) for event in events
    )
    assert all(sim.verify_receipt_hash(event.receipt) for event in events)


def test_knowledge_lattice_is_extensive_on_every_transition() -> None:
    episodes = sim.synthetic_episodes(count=100, seed=833)
    state = initial_state(episodes)
    operator = unified.UnifiedClosureOperator()
    previous = state.knowledge
    for index, episode in enumerate(episodes, start=1):
        state, event = operator.transition(state, episode)
        assert event.knowledge_extensive is True
        assert previous.precedes(state.knowledge)
        assert state.knowledge.evidence_count == index
        previous = state.knowledge


def test_environment_labels_do_not_define_natural_execution_forms() -> None:
    ep = sim.synthetic_episodes(count=1, seed=17)[0]
    volume = sim.Rolling30DayVolume.seeded(ep.entry_book.timestamp_utc.date(), D("0"))
    effective = volume.effective_volume(ep.entry_book.timestamp_utc.date())
    form_a = unified.derive_natural_form(
        episode=replace(ep, regime="CALM_BY_HUMAN_LABEL"),
        schedule=sim.alpaca_crypto_fee_schedule(),
        effective_volume=effective,
    )
    form_b = unified.derive_natural_form(
        episode=replace(ep, regime="ADVERSE_BY_HUMAN_LABEL"),
        schedule=sim.alpaca_crypto_fee_schedule(),
        effective_volume=effective,
    )
    assert form_a == form_b


def test_revisited_form_memory_survives_intervening_other_form() -> None:
    episodes = sim.synthetic_episodes(count=1, seed=9)
    ep_a = episodes[0]
    # Produce a second observable execution form by widening only the entry spread.
    b_entry = sim.make_book(
        mid=ep_a.entry_book.midpoint,
        spread_bps=D("18"),
        first_level_quantity=ep_a.entry_book.bids[0].quantity,
        timestamp=ep_a.entry_book.timestamp_utc,
        source="test:other-form:entry",
    )
    b_exit = sim.make_book(
        mid=ep_a.exit_book.midpoint,
        spread_bps=D("18"),
        first_level_quantity=ep_a.exit_book.bids[0].quantity,
        timestamp=ep_a.exit_book.timestamp_utc,
        source="test:other-form:exit",
    )
    ep_b = replace(ep_a, episode_id="FORM-B", entry_book=b_entry, exit_book=b_exit)
    ep_a2 = replace(ep_a, episode_id="FORM-A-RETURN")

    state = initial_state([ep_a])
    operator = unified.UnifiedClosureOperator()
    state, first = operator.transition(state, ep_a)
    memory_after_a = state.knowledge.memory_for(first.form)
    assert memory_after_a is not None

    state, second = operator.transition(state, ep_b)
    assert second.form != first.form
    retained = state.knowledge.memory_for(first.form)
    assert retained is not None
    assert retained.evidence_hashes == memory_after_a.evidence_hashes
    assert retained.learner_state == memory_after_a.learner_state

    state, third = operator.transition(state, ep_a2)
    assert third.form == first.form
    assert third.used_form_memory is True
    refined = state.knowledge.memory_for(first.form)
    assert refined is not None
    assert set(memory_after_a.evidence_hashes).issubset(refined.evidence_hashes)
    assert len(refined.evidence_hashes) == len(memory_after_a.evidence_hashes) + 1


def test_same_state_and_evidence_give_same_transition() -> None:
    ep = sim.synthetic_episodes(count=1, seed=101)[0]
    state = initial_state([ep])
    operator = unified.UnifiedClosureOperator()
    next_a, event_a = operator.transition(state, ep)
    next_b, event_b = operator.transition(state, ep)
    assert event_a.to_dict() == event_b.to_dict()
    assert next_a.to_dict() == next_b.to_dict()
    assert next_a.state_hash == next_b.state_hash


def test_unified_run_accumulates_evidence_without_claiming_monotone_point_error() -> None:
    episodes = sim.synthetic_episodes(count=120, seed=833)
    events, state, summary = unified.run_unified(episodes=episodes)
    assert summary["knowledge_extensive_every_transition"] is True
    assert summary["knowledge_evidence_count"] == 120
    assert state.knowledge.evidence_count == 120
    assert summary["point_prediction_error_forced_monotone"] is False
    assert summary["closure_fidelity_order"] == (
        "knowledge/evidence inclusion, not forced point-error monotonicity"
    )
    assert summary["form_revisit_count"] > 0
    assert any(event.used_form_memory for event in events)


def test_form_memory_counts_are_monotone_under_revisits() -> None:
    episodes = sim.synthetic_episodes(count=160, seed=833)
    state = initial_state(episodes)
    operator = unified.UnifiedClosureOperator()
    previous_counts: dict[str, tuple[int, int]] = {}
    for episode in episodes:
        state, _ = operator.transition(state, episode)
        for key, memory in state.knowledge.forms.items():
            old_closed, old_no_fill = previous_counts.get(key, (0, 0))
            assert memory.closed_return_count >= old_closed
            assert memory.no_fill_count >= old_no_fill
            previous_counts[key] = (
                memory.closed_return_count,
                memory.no_fill_count,
            )


def test_unified_state_contains_fee_price_execution_learning_and_receipt_projections() -> None:
    ep = sim.synthetic_episodes(count=1, seed=833)[0]
    state = initial_state([ep])
    next_state, event = unified.UnifiedClosureOperator().transition(state, ep)
    payload = next_state.to_dict()
    assert payload["rules"]["symbol"] == "BTC/USD"
    assert payload["schedule"]["venue"] == "ALPACA_CRYPTO"
    assert "global_learner_state" in payload
    assert payload["knowledge"]["evidence_count"] == 1
    assert next_state.previous_receipt_hash == event.receipt.receipt_hash
    assert next_state.previous_transition_hash == event.transition_hash
