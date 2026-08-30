import Mathlib

namespace NRRF847

/-- A closed realized trading receipt.  The economic fields are already realized
    quantities in one quote currency.  Authentication and inventory closure are
    retained as propositions because profitability is not allowed to erase the
    transactional proof boundary. -/
structure RealizedReceipt where
  buyNotional : ℝ
  sellNotional : ℝ
  fees : ℝ
  rebates : ℝ
  inventoryCarry : ℝ
  forcedUnwindCost : ℝ
  allFillsAuthenticated : Prop
  inventoryClosed : Prop

/-- What the executions earned before explicit execution costs. -/
def grossTradingSurplus (r : RealizedReceipt) : ℝ :=
  r.sellNotional + r.rebates - r.buyNotional

/-- Every explicit realized cost that must be paid before a closure is profitable. -/
def realizedExecutionCosts (r : RealizedReceipt) : ℝ :=
  r.fees + r.inventoryCarry + r.forcedUnwindCost

/-- The decisive economic quantity: realized cash surplus after every explicit
    realized execution cost.  Structural closure itself contributes no fictitious
    profit term. -/
def closureAdjustedRealizedPnL (r : RealizedReceipt) : ℝ :=
  grossTradingSurplus r - realizedExecutionCosts r

/-- Explicit market assumptions sufficient for a profitability theorem.
    Notice that neither authentication nor closure is itself a positivity
    assumption.  Profit requires the separate economic dominance inequality. -/
structure MarketAssumptions (r : RealizedReceipt) : Prop where
  fills_authenticated : r.allFillsAuthenticated
  inventory_closed : r.inventoryClosed
  fees_nonnegative : 0 ≤ r.fees
  inventory_carry_nonnegative : 0 ≤ r.inventoryCarry
  forced_unwind_nonnegative : 0 ≤ r.forcedUnwindCost
  gross_surplus_dominates_realized_costs :
    realizedExecutionCosts r < grossTradingSurplus r

/-- The profitability theorem.  Under authenticated fills, closed inventory,
    nonnegative explicit costs, and the explicit market inequality saying the
    realized gross trading surplus exceeds all realized costs, closure-adjusted
    realized P&L is strictly positive. -/
theorem closure_adjusted_realized_pnl_positive
    (r : RealizedReceipt) (h : MarketAssumptions r) :
    0 < closureAdjustedRealizedPnL r := by
  dsimp [closureAdjustedRealizedPnL]
  exact sub_pos.mpr h.gross_surplus_dominates_realized_costs

/-- The same theorem is the network theorem when `r` is the aggregate receipt
    obtained by summing authenticated fills and realized costs across symbols. -/
theorem aggregate_network_profitability
    (networkReceipt : RealizedReceipt)
    (h : MarketAssumptions networkReceipt) :
    0 < closureAdjustedRealizedPnL networkReceipt :=
  closure_adjusted_realized_pnl_positive networkReceipt h

/-- A machine-checkable counterexample: authenticated closure alone does not
    imply profitability.  The round trip earns 1 unit gross but pays 2 in fees. -/
def closedLossReceipt : RealizedReceipt where
  buyNotional := 100
  sellNotional := 101
  fees := 2
  rebates := 0
  inventoryCarry := 0
  forcedUnwindCost := 0
  allFillsAuthenticated := True
  inventoryClosed := True

 theorem closed_authenticated_can_lose :
    closedLossReceipt.allFillsAuthenticated ∧
    closedLossReceipt.inventoryClosed ∧
    0 < grossTradingSurplus closedLossReceipt ∧
    closureAdjustedRealizedPnL closedLossReceipt < 0 := by
  constructor
  · trivial
  constructor
  · trivial
  constructor <;> norm_num [grossTradingSurplus, realizedExecutionCosts,
    closureAdjustedRealizedPnL, closedLossReceipt]

/-- Therefore no theorem may derive positive realized P&L from authentication
    and inventory closure alone. -/
theorem closure_alone_is_not_profitability :
    ∃ r : RealizedReceipt,
      r.allFillsAuthenticated ∧ r.inventoryClosed ∧
      closureAdjustedRealizedPnL r < 0 := by
  exact ⟨closedLossReceipt,
    closed_authenticated_can_lose.1,
    closed_authenticated_can_lose.2.1,
    closed_authenticated_can_lose.2.2.2⟩

end NRRF847
