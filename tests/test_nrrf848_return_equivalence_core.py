from __future__ import annotations

import unittest

from experiments.nrrf848_return_equivalence_core import ClosureReceipt, ReturnEquivalenceClosure


class TestNRRF848ReturnEquivalenceCore(unittest.TestCase):
    @staticmethod
    def receipt(
        *,
        gross: float = 5.0,
        costs: dict[str, float] | None = None,
        closed: bool = True,
        authenticated: bool = True,
        operation: str = "MAKER",
    ) -> ClosureReceipt:
        return ClosureReceipt(
            authenticated=authenticated,
            operation=operation,
            gross_bps=gross,
            realized_costs=costs or {"fees": 3.0},
            inventory_closed=closed,
        )

    def test_unauthenticated_return_does_not_author_knowledge(self) -> None:
        model = ReturnEquivalenceClosure(["MAKER"])
        before = model.snapshot()
        changed = model.observe("cell-A", self.receipt(authenticated=False))
        after = model.snapshot()
        self.assertFalse(changed)
        self.assertEqual(before["evidence_count"], after["evidence_count"])
        self.assertEqual(before["evidence_tip"], after["evidence_tip"])

    def test_equivalent_return_laws_merge_cells_into_one_token(self) -> None:
        model = ReturnEquivalenceClosure(["MAKER"], min_cell_samples=4)
        for _ in range(4):
            model.observe("visual-state-A", self.receipt())
            model.observe("visual-state-B", self.receipt())
        self.assertEqual(model.cell_count, 2)
        self.assertEqual(model.bubble_count, 1)
        self.assertEqual(model.bubble("visual-state-A"), model.bubble("visual-state-B"))

    def test_new_authenticated_evidence_can_split_a_previous_token(self) -> None:
        model = ReturnEquivalenceClosure(["MAKER"], min_cell_samples=4)
        for _ in range(4):
            model.observe("A", self.receipt())
            model.observe("B", self.receipt())
        self.assertEqual(model.bubble_count, 1)
        for _ in range(4):
            model.observe(
                "B",
                self.receipt(costs={"fees": 3.0, "new_arbitrary_constraint": 12.0}),
            )
        self.assertEqual(model.bubble_count, 2)
        self.assertNotEqual(model.bubble("A"), model.bubble("B"))

    def test_arbitrary_cost_names_enter_realized_pnl(self) -> None:
        receipt = self.receipt(
            gross=10.0,
            costs={
                "fees": 1.0,
                "slippage": 2.0,
                "venue_specific_tax": 3.0,
                "unknown_future_cost": 5.0,
            },
        )
        self.assertEqual(receipt.realized_pnl_bps, -1.0)

    def test_gross_positive_but_net_negative_is_not_admitted(self) -> None:
        model = ReturnEquivalenceClosure(["MAKER"], min_cell_samples=4)
        for _ in range(30):
            model.observe(
                "A",
                self.receipt(gross=10.0, costs={"fees": 12.0}, closed=True),
            )
        self.assertEqual(model.select("A"), "HOLD")

    def test_positive_closure_adjusted_return_with_strong_closure_is_admitted(self) -> None:
        model = ReturnEquivalenceClosure(["MAKER"], min_cell_samples=4)
        for _ in range(30):
            model.observe(
                "A",
                self.receipt(gross=5.0, costs={"fees": 2.0}, closed=True),
            )
        self.assertEqual(model.select("A"), "MAKER")

    def test_positive_pnl_without_reliable_inventory_closure_is_not_admitted(self) -> None:
        model = ReturnEquivalenceClosure(["MAKER"], min_cell_samples=4)
        for i in range(40):
            model.observe(
                "A",
                self.receipt(gross=5.0, costs={"fees": 1.0}, closed=(i % 2 == 0)),
            )
        self.assertEqual(model.select("A"), "HOLD")

    def test_knowledge_is_monotone_while_partition_may_change(self) -> None:
        model = ReturnEquivalenceClosure(["MAKER"], min_cell_samples=2)
        counts = []
        for i in range(8):
            model.observe(
                "A" if i < 4 else "B",
                self.receipt(gross=5.0 + i, costs={"fees": 2.0}),
            )
            counts.append(model.evidence_count)
        self.assertEqual(counts, sorted(counts))
        self.assertEqual(model.evidence_count, 8)
        self.assertIsNotNone(model.evidence_tip)

    def test_operation_space_is_explicit_and_extensible(self) -> None:
        model = ReturnEquivalenceClosure(["MAKER", "CUSTOM_HEDGE"])
        for _ in range(30):
            model.observe(
                "A",
                self.receipt(
                    operation="CUSTOM_HEDGE",
                    gross=6.0,
                    costs={"custom_cost": 2.0},
                    closed=True,
                ),
            )
        self.assertEqual(model.select("A"), "CUSTOM_HEDGE")
        with self.assertRaises(ValueError):
            model.observe("A", self.receipt(operation="NOT_REGISTERED"))


if __name__ == "__main__":
    unittest.main()
