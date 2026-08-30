from __future__ import annotations

import unittest
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


class TestNRRF833UnifiedClosureReintegration(unittest.TestCase):
    def test_one_operator_closes_every_admitted_accounting_return(self) -> None:
        episodes = sim.synthetic_episodes(count=80, seed=833)
        events, _, summary = unified.run_unified(episodes=episodes)
        self.assertEqual(summary["maximum_accounting_closure_residual_quote"], "0")
        self.assertTrue(
            all(event.receipt.closure_residual_quote in (None, D("0")) for event in events)
        )
        self.assertTrue(all(sim.verify_receipt_hash(event.receipt) for event in events))

    def test_knowledge_lattice_is_extensive_on_every_transition(self) -> None:
        episodes = sim.synthetic_episodes(count=100, seed=833)
        state = initial_state(episodes)
        operator = unified.UnifiedClosureOperator()
        previous = state.knowledge
        for index, episode in enumerate(episodes, start=1):
            state, event = operator.transition(state, episode)
            self.assertTrue(event.knowledge_extensive)
            self.assertTrue(previous.precedes(state.knowledge))
            self.assertEqual(state.knowledge.evidence_count, index)
            previous = state.knowledge

    def test_environment_labels_do_not_define_natural_execution_forms(self) -> None:
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
        self.assertEqual(form_a, form_b)

    def test_revisited_form_memory_survives_intervening_other_form(self) -> None:
        ep_a = sim.synthetic_episodes(count=1, seed=9)[0]
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
        self.assertIsNotNone(memory_after_a)
        assert memory_after_a is not None

        state, second = operator.transition(state, ep_b)
        self.assertNotEqual(second.form, first.form)
        retained = state.knowledge.memory_for(first.form)
        self.assertIsNotNone(retained)
        assert retained is not None
        self.assertEqual(retained.evidence_hashes, memory_after_a.evidence_hashes)
        self.assertEqual(retained.learner_state, memory_after_a.learner_state)

        state, third = operator.transition(state, ep_a2)
        self.assertEqual(third.form, first.form)
        self.assertTrue(third.used_form_memory)
        refined = state.knowledge.memory_for(first.form)
        self.assertIsNotNone(refined)
        assert refined is not None
        self.assertTrue(set(memory_after_a.evidence_hashes).issubset(refined.evidence_hashes))
        self.assertEqual(len(refined.evidence_hashes), len(memory_after_a.evidence_hashes) + 1)

    def test_same_state_and_evidence_give_same_transition(self) -> None:
        ep = sim.synthetic_episodes(count=1, seed=101)[0]
        state = initial_state([ep])
        operator = unified.UnifiedClosureOperator()
        next_a, event_a = operator.transition(state, ep)
        next_b, event_b = operator.transition(state, ep)
        self.assertEqual(event_a.to_dict(), event_b.to_dict())
        self.assertEqual(next_a.to_dict(), next_b.to_dict())
        self.assertEqual(next_a.state_hash, next_b.state_hash)

    def test_unified_run_accumulates_evidence_without_claiming_monotone_point_error(self) -> None:
        episodes = sim.synthetic_episodes(count=120, seed=833)
        events, state, summary = unified.run_unified(episodes=episodes)
        self.assertTrue(summary["knowledge_extensive_every_transition"])
        self.assertEqual(summary["knowledge_evidence_count"], 120)
        self.assertEqual(state.knowledge.evidence_count, 120)
        self.assertFalse(summary["point_prediction_error_forced_monotone"])
        self.assertEqual(
            summary["closure_fidelity_order"],
            "knowledge/evidence inclusion, not forced point-error monotonicity",
        )
        self.assertGreater(summary["form_revisit_count"], 0)
        self.assertTrue(any(event.used_form_memory for event in events))

    def test_form_memory_counts_are_monotone_under_revisits(self) -> None:
        episodes = sim.synthetic_episodes(count=160, seed=833)
        state = initial_state(episodes)
        operator = unified.UnifiedClosureOperator()
        previous_counts: dict[str, tuple[int, int]] = {}
        for episode in episodes:
            state, _ = operator.transition(state, episode)
            for key, memory in state.knowledge.forms.items():
                old_closed, old_no_fill = previous_counts.get(key, (0, 0))
                self.assertGreaterEqual(memory.closed_return_count, old_closed)
                self.assertGreaterEqual(memory.no_fill_count, old_no_fill)
                previous_counts[key] = (
                    memory.closed_return_count,
                    memory.no_fill_count,
                )

    def test_unified_state_contains_all_trading_projections(self) -> None:
        ep = sim.synthetic_episodes(count=1, seed=833)[0]
        state = initial_state([ep])
        next_state, event = unified.UnifiedClosureOperator().transition(state, ep)
        payload = next_state.to_dict()
        self.assertEqual(payload["rules"]["symbol"], "BTC/USD")
        self.assertEqual(payload["schedule"]["venue"], "ALPACA_CRYPTO")
        self.assertIn("global_learner_state", payload)
        self.assertEqual(payload["knowledge"]["evidence_count"], 1)
        self.assertEqual(next_state.previous_receipt_hash, event.receipt.receipt_hash)
        self.assertEqual(next_state.previous_transition_hash, event.transition_hash)


if __name__ == "__main__":
    unittest.main()
