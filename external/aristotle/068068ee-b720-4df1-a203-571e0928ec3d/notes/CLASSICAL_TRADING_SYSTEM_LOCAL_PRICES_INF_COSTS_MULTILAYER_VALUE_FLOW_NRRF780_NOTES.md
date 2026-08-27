# NRRF780 — A classical trading system evaluated in the relative unity of value flow

File: `NRRF780ClassicalTradingSystemLocalPricesInfCostsMultilayerValueFlow.lean`
(namespace `NRRF780`; builds with no `sorry`; every headline theorem audits to
`propext`, `Classical.choice`, `Quot.sound` only).

## The reading

> Evaluate a classical trading system inside the tokenomic relative unity of value flow, where the
> **local** readings are prices and the **inf** reading is cost, with a multilayer form for each
> aspect that makes up classical monetary transaction pricing.

The verdict: **a classical transaction carries no value of its own.** Its local (price) content
cancels identically in the value flow; what survives is exactly minus its inf (cost) reading. The
same cancellation, lifted to a system, is the loop statement of the tokenomic layer: an exact price
field has no holonomy, so a circuit returns exactly minus the friction it paid. Profit is therefore
never a property of the transactions — it is exactly a **non-exactness of the price field exceeding
the friction**, i.e. arbitrage, which is a property of the price cohomology class and not of the
trading system.

## Data

| Aspect of a classical transaction | Lean |
|---|---|
| signed size, quotes, fill, mark, fee | `Txn.qty`, `Txn.bid`, `Txn.ask`, `Txn.fill`, `Txn.mark`, `Txn.fee` |
| multilayer form (one reading per aspect) | `layer : Fin 6 → Txn → ℚ` |
| local reading (prices) | `localRead t = (qty, fill, mark, fee)` |
| inf reading (costs) | `Txn.cost t = fee + slippage t`, `Txn.slippage t = (fill − mark)·qty` |
| value flow, evaluation | `Txn.flow = mtm + cash`, `Txn.net = flow − fee` |
| price field on a network | `NRRF742.dOf p : Cochain V ℚ` |
| friction on a network | `c : Cochain V ℚ` with `SymCost`, `NonNegCost` |
| what an edge actually delivers | `tradeCochain w c i j = w i j − c i j` |
| classical P&L in time | `pnl q m c n = ∑_{i<n} (q i · (m (i+1) − m i) − c i)` |

## Results

* **The multilayer form is complete and irredundant.** `layers_complete` (agreement in all six
  layers is identity of the transaction); `layers_drop_fill_not_complete` (drop the execution layer
  and quotes no longer determine the trade). The cost layer adds nothing: `cost_layer_redundant`.
* **Local determines inf, strictly.** `inf_refines_local` (cost is a translation of the local price
  data) and `local_not_refines_inf` (the price level is not recoverable from the cost). Evaluation
  and cost carry the same translational data up to sign: `transEq_flow_cost`.
* **The evaluation identity.** `flow_eq_neg_slippage`, `net_eq_neg_cost` (`net t = − cost t`),
  `net_eq_zero_iff`, `net_nonpos_of_cost_nonneg`.
* **Relative unity.** `flow_shift`, `cost_shift`, `net_shift`, `spread_shift`: value flow is blind to
  a shift of the whole local price scale, while the price layer is not
  (`fill_not_shift_invariant`). Under a change of numéraire evaluation and cost scale together
  (`net_scale`, `cost_scale`), so only their ratio is determined:
  `flow_cost_ratio_invariant`.
* **Crossing the spread.** `buy_slippage_halfSpread`, `sell_slippage_halfSpread` (executing at the
  quote and marking at the mid costs exactly the half-spread), hence
  `crossing_trade_strictly_negative` and `crossing_sell_strictly_negative`.
* **A system of transactions.** `sysNet_eq_neg_sysCost` (`∑ net = − ∑ cost`),
  `sysNet_nonpos`, `sysNet_neg_of_charge`.
* **On a value-flow network.** `price_loop_zero` (exact prices have no holonomy — the NRRF742/743
  token statement), `classical_roundTrip_eq_neg_cost`, `classical_roundTrip_nonpos`,
  `classical_roundTrip_strict_loss` (loss at least circuit-length × per-edge charge, via
  `hol_cost_ge_len_mul`), `profitable_iff_price_exceeds_cost`, and the converse direction
  `profit_needs_arbitrage` / `profit_needs_nonexact`: a profitable circuit forces the price field to
  carry holonomy, hence to admit no global token at all.
* **In time.** `pnl_const_position` (the classical identity: position × price move − costs),
  `pnl_returning_market` (a market returning to its mark returns minus the accumulated cost),
  `pnl_returning_nonpos`, `pnl_pos_iff`.
* **Execution is a determination, not a preference.** `execRel_rigid`, `execSel_buy`,
  `execSel_sell`, `execSel_unique` — "buy at the ask, sell at the bid" is the unique admissible
  execution returned by the NRRF775 natural form selector; `selected_execution_is_crossing` closes
  the loop back to §4.

`nrrf780_answer` collects the clauses.

## Relation to earlier modules

Nothing of the tokenomic layer is restated: the loop machinery (`Net`, `hol`, `dOf`, `Glues`,
`NoArbitrage`, `hol_dOf_closed`, `noArbitrage_of_glues`) is imported from NRRF742, the
relative-equality-function language (`Refines`, `TransEq`, `Complete`, `joint`) from NRRF772, and
the natural form selector (`Constraint`, `Rigid`, `sel`) from NRRF775. NRRF780 is the *classical*
transaction read on that substrate.
