import NRRF780LocalPriceGlobalCostEquality
import NRRF783RelativePotentialClassicalFlowSupernetBridge
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Trading delta — selected local prices, derived 0-hair cost, and relative-potential P&L

This is the small active-build bridge for the authenticated Aristotle delta.  It deliberately keeps
four categories distinct:

* a quote relation determines the fill;
* the filled local price ball determines its `zeroHair` cost;
* two price levels determine a translation-invariant relative potential;
* profit evaluates that potential move after the derived costs.

Cost is therefore downstream of selection.  It is not an independent resource metric and cannot
select a fill.  The bridge imports the repository's existing closure interfaces; the full Aristotle
sources and their independent task provenance are retained as an external content-addressed
snapshot.
-/

namespace NRRFTradingDelta

/-! ## Independent category 1: relational execution -/

/-- The two directions in which a local quote can close. -/
inductive Side
  | buy
  | sell
  deriving DecidableEq, Repr

/-- The local data available before the execution relation has selected a fill. -/
structure InfPriceBall where
  qty : ℚ
  bid : ℚ
  ask : ℚ
  mark : ℚ
  fee : ℚ
  deriving DecidableEq, Repr

/-- The natural quote determined by the side; no cost or profit is an argument. -/
def selectedFill (b : InfPriceBall) : Side → ℚ
  | .buy => b.ask
  | .sell => b.bid

/-- The admissible execution relation. -/
def FillRel (b : InfPriceBall) (side : Side) (fill : ℚ) : Prop :=
  fill = selectedFill b side

/-- The quote relation has exactly one admissible fill. -/
theorem fillRel_unique (b : InfPriceBall) (side : Side) :
    ∃! fill : ℚ, FillRel b side fill := by
  exact ⟨selectedFill b side, rfl, fun y hy => hy⟩

/-- A filled local trade is a price ball together with evidence that its fill is relationally
selected. -/
structure ClosedLocalTrade where
  ball : InfPriceBall
  side : Side
  fill : ℚ
  fill_closes : FillRel ball side fill

/-- Close the price ball by its unique relational fill. -/
def close (b : InfPriceBall) (side : Side) : ClosedLocalTrade :=
  ⟨b, side, selectedFill b side, rfl⟩

@[simp] theorem close_fill (b : InfPriceBall) (side : Side) :
    (close b side).fill = selectedFill b side :=
  rfl

/-! ## Independent category 2: the 0-hair translated from the filled infinity ball -/

/-- Slippage is derived from the selected local fill relative to the local mark. -/
def slippage (t : ClosedLocalTrade) : ℚ :=
  (t.fill - t.ball.mark) * t.ball.qty

/-- The 0-hair: the whole local friction translated from the filled price ball. -/
def zeroHair (t : ClosedLocalTrade) : ℚ :=
  t.ball.fee + slippage t

/-- Value at the mark after the local execution. -/
def netAtMark (t : ClosedLocalTrade) : ℚ :=
  (t.ball.mark - t.fill) * t.ball.qty - t.ball.fee

/-- The local levels cancel: a single selected execution evaluates to minus its derived hair. -/
theorem netAtMark_eq_neg_zeroHair (t : ClosedLocalTrade) :
    netAtMark t = -zeroHair t := by
  simp only [netAtMark, zeroHair, slippage]
  ring

/-- The existing local-price/global-equality interface instantiated by the derived 0-hair. -/
def costInterface : NRRF780Local.PriceCostInterface ClosedLocalTrade ℚ where
  complete := zeroHair

/-- The cost equality contains its derivation from the filled local price ball. -/
def completedCost (t : ClosedLocalTrade) :
    NRRF780Local.LocalPriceGlobalCost costInterface where
  localPrice := t
  globalCostEqual := zeroHair t
  completion := rfl

theorem completedCost_is_translation (t : ClosedLocalTrade) :
    costInterface.complete (completedCost t).localPrice =
      (completedCost t).globalCostEqual :=
  (completedCost t).cost_is_global_equal

/-- The generic classical-flow interface is obtained from the derived trade, rather than by
supplying an unrelated cost scalar. -/
def asClassicalFlow (t : ClosedLocalTrade) (cost_nonnegative : 0 ≤ zeroHair t) :
    NRRF783.ClassicalFlow ℚ where
  priceMove := 0
  cost := zeroHair t
  net := netAtMark t
  cost_nonnegative := cost_nonnegative
  net_eq_priceMove_sub_cost := by
    rw [netAtMark_eq_neg_zeroHair]
    exact (zero_sub _).symm

@[simp] theorem asClassicalFlow_cost (t : ClosedLocalTrade) (h : 0 ≤ zeroHair t) :
    (asClassicalFlow t h).cost = zeroHair t :=
  rfl

/-! ## Translational truth of the two independent categories -/

/-- Re-express every local price level by the same translation. -/
def shiftBall (c : ℚ) (b : InfPriceBall) : InfPriceBall :=
  ⟨b.qty, b.bid + c, b.ask + c, b.mark + c, b.fee⟩

theorem selectedFill_shift (c : ℚ) (b : InfPriceBall) (side : Side) :
    selectedFill (shiftBall c b) side = selectedFill b side + c := by
  cases side <;> rfl

/-- Transport a closed trade along the same change of local price level. -/
def shiftTrade (c : ℚ) (t : ClosedLocalTrade) : ClosedLocalTrade where
  ball := shiftBall c t.ball
  side := t.side
  fill := t.fill + c
  fill_closes := by
    rw [FillRel, selectedFill_shift]
    exact congrArg (· + c) t.fill_closes

/-- The derived cost is translational truth: shifting all local levels changes no 0-hair. -/
@[simp] theorem zeroHair_shift (c : ℚ) (t : ClosedLocalTrade) :
    zeroHair (shiftTrade c t) = zeroHair t := by
  simp only [zeroHair, slippage, shiftTrade, shiftBall]
  ring

/-- The relative potential is independently derived from two completed local levels. -/
def relativePotential (entry exit : ℚ) : ℚ :=
  exit - entry

/-- It too is translational truth: a common change of level is invisible. -/
@[simp] theorem relativePotential_shift (c entry exit : ℚ) :
    relativePotential (entry + c) (exit + c) = relativePotential entry exit := by
  simp only [relativePotential]
  ring

/-! ## Independent category 3: temporal assessment after selection and cost translation -/

/-- A temporal assessment.  Every cost-bearing leg is already a closed local trade, so the
accumulated cost is derived rather than supplied as an independent sequence. -/
structure TemporalClosure where
  qty : ℚ
  entryMark : ℚ
  exitMark : ℚ
  legs : List ClosedLocalTrade

namespace TemporalClosure

/-- Total 0-hair translated from all selected local legs. -/
def accumulatedHair (t : TemporalClosure) : ℚ :=
  (t.legs.map zeroHair).sum

/-- P&L is relative-potential movement less the derived accumulated hair. -/
def net (t : TemporalClosure) : ℚ :=
  t.qty * relativePotential t.entryMark t.exitMark - t.accumulatedHair

theorem net_eq_potential_sub_hair (t : TemporalClosure) :
    t.net = t.qty * relativePotential t.entryMark t.exitMark - t.accumulatedHair :=
  rfl

/-- Profit is assessed only after all three upstream translations have completed. -/
theorem profitable_iff_potential_exceeds_hair (t : TemporalClosure) :
    0 < t.net ↔
      t.accumulatedHair < t.qty * relativePotential t.entryMark t.exitMark := by
  rw [net, sub_pos]

/-- Simultaneously translate every price presentation. -/
def shift (c : ℚ) (t : TemporalClosure) : TemporalClosure :=
  ⟨t.qty, t.entryMark + c, t.exitMark + c, t.legs.map (shiftTrade c)⟩

@[simp] theorem accumulatedHair_shift (c : ℚ) (t : TemporalClosure) :
    (t.shift c).accumulatedHair = t.accumulatedHair := by
  change (List.map zeroHair (List.map (shiftTrade c) t.legs)).sum =
    (List.map zeroHair t.legs).sum
  induction t.legs with
  | nil => rfl
  | cons leg rest ih =>
      simp only [List.map_cons, List.sum_cons, zeroHair_shift, ih]

/-- The full temporal evaluation is invariant under the same translation. -/
@[simp] theorem net_shift (c : ℚ) (t : TemporalClosure) :
    (t.shift c).net = t.net := by
  change t.qty * relativePotential (t.entryMark + c) (t.exitMark + c) -
      (t.shift c).accumulatedHair =
    t.qty * relativePotential t.entryMark t.exitMark - t.accumulatedHair
  rw [relativePotential_shift, accumulatedHair_shift]

/-- If the relative potential closes to zero, nonnegative derived hair cannot produce profit. -/
theorem returning_nonpositive (t : TemporalClosure)
    (returned : relativePotential t.entryMark t.exitMark = 0)
    (hair_nonnegative : ∀ leg ∈ t.legs, 0 ≤ zeroHair leg) :
    t.net ≤ 0 := by
  have total_nonnegative : 0 ≤ t.accumulatedHair := by
    have hsum : ∀ legs : List ClosedLocalTrade,
        (∀ leg ∈ legs, 0 ≤ zeroHair leg) →
          0 ≤ (legs.map zeroHair).sum := by
      intro legs hlegs
      induction legs with
      | nil => simp
      | cons leg rest ih =>
          simp only [List.map_cons, List.sum_cons]
          exact add_nonneg
            (hlegs leg (by simp))
            (ih (fun other hother => hlegs other (by simp [hother])))
    exact hsum t.legs hair_nonnegative
  rw [net, returned, mul_zero, zero_sub]
  exact neg_nonpos.mpr total_nonnegative

end TemporalClosure

/-! ## Collected incremental closure -/

/-- The small active theorem linking the independently derived categories without identifying
them definitionally. -/
theorem trading_delta_closure
    (b : InfPriceBall) (side : Side) (t : TemporalClosure) :
    (∃! fill : ℚ, FillRel b side fill) ∧
    netAtMark (close b side) = -zeroHair (close b side) ∧
    costInterface.complete (completedCost (close b side)).localPrice =
      (completedCost (close b side)).globalCostEqual ∧
    (∀ c : ℚ, zeroHair (shiftTrade c (close b side)) = zeroHair (close b side)) ∧
    (∀ c : ℚ,
      relativePotential (t.entryMark + c) (t.exitMark + c) =
        relativePotential t.entryMark t.exitMark) ∧
    (0 < t.net ↔
      t.accumulatedHair < t.qty * relativePotential t.entryMark t.exitMark) :=
  ⟨fillRel_unique b side,
    netAtMark_eq_neg_zeroHair (close b side),
    completedCost_is_translation (close b side),
    fun c => zeroHair_shift c (close b side),
    fun c => relativePotential_shift c t.entryMark t.exitMark,
    t.profitable_iff_potential_exceeds_hair⟩

#print axioms NRRFTradingDelta.fillRel_unique
#print axioms NRRFTradingDelta.netAtMark_eq_neg_zeroHair
#print axioms NRRFTradingDelta.zeroHair_shift
#print axioms NRRFTradingDelta.TemporalClosure.profitable_iff_potential_exceeds_hair
#print axioms NRRFTradingDelta.trading_delta_closure

end NRRFTradingDelta
