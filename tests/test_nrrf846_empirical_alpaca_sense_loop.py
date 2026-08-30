from __future__ import annotations

import json
import unittest
from decimal import Decimal
from pathlib import Path

from experiments import nrrf846_empirical_alpaca_sense_loop as empirical


ROOT = Path(__file__).parents[1]
FIXTURE = ROOT / "benchmarks" / "nrrf846_empirical_alpaca_sense_loop" / "btcusd_authenticated_returns_20260830.json"
REPORT = ROOT / "reports" / "nrrf846_empirical_alpaca_sense_loop_20260830.json"


class NRRF846EmpiricalAlpacaSenseLoopTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.payload = json.loads(FIXTURE.read_text())
        cls.result = empirical.run_fixture(cls.payload, grid_steps=10000)

    def test_quote_only_prices_do_not_author_semantic_state(self) -> None:
        self.assertTrue(self.result["quote_only_semantic_state_invariant"])
        self.assertEqual(
            self.result["quote_only_state_hash_before"],
            self.result["quote_only_state_hash_after"],
        )

    def test_four_market_returns_are_authenticated_by_trade_and_exact_size_decrement(self) -> None:
        self.assertEqual(self.result["authenticated_return_count"], 4)
        for cycle in self.result["cycles"]:
            self.assertTrue(cycle["entry_return"]["authenticated"])
            self.assertEqual(cycle["entry_return"]["side"], "MAKER_BUY_RETURN")
            self.assertTrue(cycle["exit_return"]["authenticated"])
            self.assertEqual(cycle["exit_return"]["side"], "MAKER_SELL_RETURN")

    def test_full_four_sheaf_and_skipped_cycle_are_distinct(self) -> None:
        for cycle in self.result["cycles"]:
            self.assertEqual(cycle["full_four_sheaf_path"]["cycle"], "0->1->2->3->0")
            self.assertEqual(cycle["skipped_passive_exit_path"]["cycle"], "0->1->3->0")
            self.assertEqual(cycle["full_four_sheaf_path"]["relative_closure_cost"], "0")
            self.assertEqual(cycle["skipped_passive_exit_path"]["relative_closure_cost"], "INF")

    def test_taker_exit_cost_dominates_on_both_empirical_cycles(self) -> None:
        for cycle in self.result["cycles"]:
            self.assertTrue(cycle["taker_exit_cost_componentwise_dominates"])
            self.assertGreater(Decimal(cycle["passive_exit_advantage_bps"]), 0)

    def test_empirical_queue_sweep_exposes_missing_maker_sell_phase(self) -> None:
        a, b = self.result["cycles"]
        self.assertEqual(a["queue_fraction_sweep"]["full_four_sheaf_count"], 21)
        self.assertEqual(a["queue_fraction_sweep"]["skipped_passive_exit_count"], 3646)
        self.assertEqual(a["queue_fraction_sweep"]["no_maker_entry_count"], 6334)
        self.assertEqual(b["queue_fraction_sweep"]["full_four_sheaf_count"], 19)
        self.assertEqual(b["queue_fraction_sweep"]["skipped_passive_exit_count"], 474)
        self.assertEqual(b["queue_fraction_sweep"]["no_maker_entry_count"], 9508)

    def test_exit_queue_threshold_is_stricter_than_entry_on_both_cycles(self) -> None:
        for cycle in self.result["cycles"]:
            self.assertLess(
                Decimal(cycle["exit_max_queue_ahead_fraction"]),
                Decimal(cycle["entry_max_queue_ahead_fraction"]),
            )

    def test_empirical_replay_is_byte_equivalent_to_committed_report(self) -> None:
        expected = json.loads(REPORT.read_text())
        self.assertEqual(self.result, expected)

    def test_market_evidence_is_not_relabelled_as_own_fill_receipt(self) -> None:
        self.assertTrue(self.result["market_data_authenticated"])
        self.assertFalse(self.result["own_order_fills_authenticated"])
        self.assertFalse(self.result["claims_boundary"]["profitability_claim"])
        self.assertFalse(self.result["claims_boundary"]["queue_sweep_is_probability_model"])


if __name__ == "__main__":
    unittest.main()
