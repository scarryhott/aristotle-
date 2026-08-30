from __future__ import annotations

import json
import unittest
from pathlib import Path

from experiments import nrrf846_closure_transactional_partition_model as model

ROOT = Path(__file__).parents[1]
FIXTURE = ROOT / "benchmarks" / "nrrf846_empirical_alpaca_sense_loop" / "btcusd_authenticated_returns_20260830.json"
EMPIRICAL = ROOT / "reports" / "nrrf846_empirical_alpaca_sense_loop_20260830.json"


class NRRF846ClosureTransactionalPartitionModelTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.fixture = json.loads(FIXTURE.read_text())
        cls.empirical = json.loads(EMPIRICAL.read_text())
        cls.result = model.integrate_and_replay(cls.fixture, cls.empirical)

    def test_partition_is_pretrade_relational_not_price_authored(self) -> None:
        self.assertFalse(self.result["price_level_authors_partition"])
        self.assertEqual(
            self.result["partition_inputs"],
            ["entry spread", "entry top-book imbalance", "entry displayed depth / requested quantity"],
        )
        self.assertTrue(self.result["all_three_empirical_forms_distinct_pretrade"])

    def test_first_visit_fails_closed_without_cross_bubble_guess(self) -> None:
        first = self.result["passes"][0]
        self.assertEqual(first["unsafe_admissions"], 0)
        self.assertEqual(first["confusion"]["tp"], 0)
        self.assertEqual(first["confusion"]["fn"], 16)
        self.assertEqual(first["confusion"]["tn"], 110)
        self.assertEqual(first["confusion"]["fp"], 0)

    def test_second_visit_survives_all_fee_queue_constraints(self) -> None:
        second = self.result["passes"][1]
        self.assertEqual(second["confusion"]["tp"], 16)
        self.assertEqual(second["confusion"]["tn"], 110)
        self.assertEqual(second["confusion"]["fp"], 0)
        self.assertEqual(second["confusion"]["fn"], 0)
        self.assertEqual(self.result["second_visit_positive_recall"], "1")
        self.assertEqual(self.result["second_visit_unsafe_admissions"], 0)
        self.assertEqual(self.result["second_visit_missed_positive_states"], 0)

    def test_local_update_does_not_overwrite_other_bubbles(self) -> None:
        self.assertTrue(self.result["other_bubble_memory_immutable_on_local_update"])
        self.assertEqual(self.result["knowledge_evidence_count"], 6)
        self.assertEqual(len(self.result["final_state"]["bubbles"]), 3)
        for memory in self.result["final_state"]["bubbles"].values():
            self.assertEqual(memory["observation_count"], 2)
            self.assertEqual(len(memory["evidence_hashes"]), 2)

    def test_integration_removes_observed_global_negative_transfer_only_on_revisit(self) -> None:
        verdict = self.result["verdict"]
        self.assertTrue(verdict["global_negative_transfer_removed"])
        self.assertTrue(verdict["revisited_bubbles_survive_fee_queue_constraints"])
        self.assertFalse(verdict["cold_start_claim_solved"])
        self.assertFalse(verdict["generalization_to_unseen_market_bubbles_established"])

    def test_same_input_is_deterministic(self) -> None:
        again = model.integrate_and_replay(self.fixture, self.empirical)
        self.assertEqual(self.result, again)
        self.assertEqual(self.result["final_state_hash"], again["final_state_hash"])


if __name__ == "__main__":
    unittest.main()
