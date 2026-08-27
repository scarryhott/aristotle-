import NRRFTradingFullClosureNaturalFormIntegration

/-!
# Trading receipt derivation from local observations

This module closes the boundary between exchange observations and the already verified temporal
trading closure.  It deliberately separates the two moments of the construction:

* an `OpenReceipt` contains one immutable local quote and derives its entry fill without an exit,
  a future return, or a profit value;
* a `ClosedReceipt` adds a later quote from the same source, venue, and instrument, and only then
  derives the temporal potential, both zero-hair costs, and P&L.

The quote source, venue, instrument, sequence, and observation time remain part of the receipt.
The numerical validity condition is local (`bid ≤ mark ≤ ask`).  Costs are not independent input
metrics: fees are observed terms, while spread/slippage hair is translated from the uniquely
selected fills.  The resulting temporal object passes directly into the representation-free
natural-form closure of `NRRFTradingFullClosureNaturalFormIntegration`.
-/

namespace NRRFTradingReceipt

open NRRFTradingDelta
open NRRFTradingFullClosure

/-! ## Immutable local pricing sections -/

/-- One source-identified local quote observation. -/
structure QuoteObservation where
  source : String
  venue : String
  instrument : String
  sequence : Nat
  observedAt : Nat
  bid : ℚ
  ask : ℚ
  mark : ℚ
  quote_ordered : bid ≤ mark ∧ mark ≤ ask

namespace QuoteObservation

/-- Read a local quote as the price ball expected by the closure interface. -/
def ball (o : QuoteObservation) (qty fee : ℚ) : InfPriceBall :=
  ⟨qty, o.bid, o.ask, o.mark, fee⟩

/-- A common change of price level preserves the observation's non-price provenance. -/
def shift (c : ℚ) (o : QuoteObservation) : QuoteObservation where
  source := o.source
  venue := o.venue
  instrument := o.instrument
  sequence := o.sequence
  observedAt := o.observedAt
  bid := o.bid + c
  ask := o.ask + c
  mark := o.mark + c
  quote_ordered := by
    constructor <;> linarith [o.quote_ordered.1, o.quote_ordered.2]

@[simp] theorem ball_shift (c qty fee : ℚ) (o : QuoteObservation) :
    (o.shift c).ball qty fee = shiftBall c (o.ball qty fee) :=
  rfl

end QuoteObservation

/-! ## Entry closes before any future assessment exists -/

/-- Economic orientation of the completed two-leg receipt. -/
inductive Orientation
  | long
  | short
  deriving DecidableEq, Repr

def Orientation.entrySide : Orientation → Side
  | .long => .buy
  | .short => .sell

def Orientation.exitSide : Orientation → Side
  | .long => .sell
  | .short => .buy

def Orientation.entryQty (orientation : Orientation) (magnitude : ℚ) : ℚ :=
  match orientation with
  | .long => magnitude
  | .short => -magnitude

def Orientation.exitQty (orientation : Orientation) (magnitude : ℚ) : ℚ :=
  -orientation.entryQty magnitude

/-- An open receipt has no exit observation and therefore no profit field. -/
structure OpenReceipt where
  entry : QuoteObservation
  orientation : Orientation
  magnitude : ℚ
  magnitude_positive : 0 < magnitude
  entryFee : ℚ
  entry_fee_nonnegative : 0 ≤ entryFee

namespace OpenReceipt

/-- The entry ball is formed from the entry observation alone. -/
def entryBall (o : OpenReceipt) : InfPriceBall :=
  o.entry.ball (o.orientation.entryQty o.magnitude) o.entryFee

/-- The entry relation selects its own unique fill.  No future datum is in the type. -/
def entryTrade (o : OpenReceipt) : ClosedLocalTrade :=
  close o.entryBall o.orientation.entrySide

theorem entry_fill_unique (o : OpenReceipt) :
    ∃! fill : ℚ, FillRel o.entryBall o.orientation.entrySide fill :=
  fillRel_unique _ _

private theorem entryHair_nonnegative_data
    (entry : QuoteObservation) (orientation : Orientation)
    (magnitude : ℚ) (magnitude_positive : 0 < magnitude)
    (entryFee : ℚ) (entry_fee_nonnegative : 0 ≤ entryFee) :
    0 ≤ zeroHair
      (close (entry.ball (orientation.entryQty magnitude) entryFee)
        orientation.entrySide) := by
  cases orientation with
  | long =>
      change 0 ≤ entryFee + (entry.ask - entry.mark) * magnitude
      exact add_nonneg entry_fee_nonnegative
        (mul_nonneg (sub_nonneg.mpr entry.quote_ordered.2)
          (le_of_lt magnitude_positive))
  | short =>
      change 0 ≤ entryFee + (entry.bid - entry.mark) * (-magnitude)
      rw [show (entry.bid - entry.mark) * (-magnitude) =
          (entry.mark - entry.bid) * magnitude by ring]
      exact add_nonneg entry_fee_nonnegative
        (mul_nonneg (sub_nonneg.mpr entry.quote_ordered.1)
          (le_of_lt magnitude_positive))

/-- The derived entry hair is nonnegative from the quote ordering, positive magnitude, and fee. -/
theorem entryHair_nonnegative (o : OpenReceipt) : 0 ≤ zeroHair o.entryTrade := by
  exact entryHair_nonnegative_data o.entry o.orientation o.magnitude
    o.magnitude_positive o.entryFee o.entry_fee_nonnegative

end OpenReceipt

/-! ## A later compatible observation completes the temporal receipt -/

/-- The exit can close the open receipt only on the same identified stream and strictly later
sequence, without reversing observed time. -/
structure ClosedReceipt where
  openReceipt : OpenReceipt
  exit : QuoteObservation
  exitFee : ℚ
  exit_fee_nonnegative : 0 ≤ exitFee
  same_source : exit.source = openReceipt.entry.source
  same_venue : exit.venue = openReceipt.entry.venue
  same_instrument : exit.instrument = openReceipt.entry.instrument
  sequence_forward : openReceipt.entry.sequence < exit.sequence
  time_forward : openReceipt.entry.observedAt ≤ exit.observedAt

namespace ClosedReceipt

/-- The exit ball uses the opposite signed quantity and opposite quote side. -/
def exitBall (r : ClosedReceipt) : InfPriceBall :=
  r.exit.ball
    (r.openReceipt.orientation.exitQty r.openReceipt.magnitude)
    r.exitFee

def exitTrade (r : ClosedReceipt) : ClosedLocalTrade :=
  close r.exitBall r.openReceipt.orientation.exitSide

theorem exit_fill_unique (r : ClosedReceipt) :
    ∃! fill : ℚ,
      FillRel r.exitBall r.openReceipt.orientation.exitSide fill :=
  fillRel_unique _ _

/-- Altering or extending the future cannot alter an already selected entry. -/
theorem entry_selection_no_future (r s : ClosedReceipt)
    (same_open : r.openReceipt = s.openReceipt) :
    r.openReceipt.entryTrade = s.openReceipt.entryTrade := by
  rw [same_open]

private theorem exitHair_nonnegative_data
    (exit : QuoteObservation) (orientation : Orientation)
    (magnitude : ℚ) (magnitude_positive : 0 < magnitude)
    (exitFee : ℚ) (exit_fee_nonnegative : 0 ≤ exitFee) :
    0 ≤ zeroHair
      (close (exit.ball (orientation.exitQty magnitude) exitFee)
        orientation.exitSide) := by
  cases orientation with
  | long =>
      change 0 ≤ exitFee + (exit.bid - exit.mark) * (-magnitude)
      rw [show (exit.bid - exit.mark) * (-magnitude) =
          (exit.mark - exit.bid) * magnitude by ring]
      exact add_nonneg exit_fee_nonnegative
        (mul_nonneg (sub_nonneg.mpr exit.quote_ordered.1)
          (le_of_lt magnitude_positive))
  | short =>
      change 0 ≤ exitFee + (exit.ask - exit.mark) * (-(-magnitude))
      rw [neg_neg]
      exact add_nonneg exit_fee_nonnegative
        (mul_nonneg (sub_nonneg.mpr exit.quote_ordered.2)
          (le_of_lt magnitude_positive))

/-- Exit hair is likewise derived and nonnegative. -/
theorem exitHair_nonnegative (r : ClosedReceipt) : 0 ≤ zeroHair r.exitTrade := by
  exact exitHair_nonnegative_data r.exit r.openReceipt.orientation
    r.openReceipt.magnitude r.openReceipt.magnitude_positive
    r.exitFee r.exit_fee_nonnegative

/-- The only bridge into temporal assessment.  Both legs are already relationally closed. -/
def temporal (r : ClosedReceipt) : TemporalClosure where
  qty := r.openReceipt.orientation.entryQty r.openReceipt.magnitude
  entryMark := r.openReceipt.entry.mark
  exitMark := r.exit.mark
  legs := [r.openReceipt.entryTrade, r.exitTrade]

@[simp] theorem accumulatedHair_temporal (r : ClosedReceipt) :
    r.temporal.accumulatedHair =
      zeroHair r.openReceipt.entryTrade + zeroHair r.exitTrade := by
  simp [temporal, TemporalClosure.accumulatedHair]

/-- Exact realized P&L: relative mark movement minus the two independently derived hairs. -/
theorem net_eq_relativePotential_sub_hairs (r : ClosedReceipt) :
    r.temporal.net =
      r.openReceipt.orientation.entryQty r.openReceipt.magnitude *
          relativePotential r.openReceipt.entry.mark r.exit.mark -
        (zeroHair r.openReceipt.entryTrade + zeroHair r.exitTrade) := by
  simp [temporal, TemporalClosure.net, TemporalClosure.accumulatedHair]

/-- Profit is an assessment of the completed receipt, not a selector of either fill. -/
theorem profitable_iff_relativePotential_exceeds_hairs (r : ClosedReceipt) :
    0 < r.temporal.net ↔
      zeroHair r.openReceipt.entryTrade + zeroHair r.exitTrade <
        r.openReceipt.orientation.entryQty r.openReceipt.magnitude *
          relativePotential r.openReceipt.entry.mark r.exit.mark := by
  rw [net_eq_relativePotential_sub_hairs, sub_pos]

/-- If the later mark returns to the entry mark, a valid receipt cannot be profitable. -/
theorem returning_nonpositive (r : ClosedReceipt)
    (returned : r.exit.mark = r.openReceipt.entry.mark) :
    r.temporal.net ≤ 0 := by
  apply NRRFTradingDelta.TemporalClosure.returning_nonpositive
  · change relativePotential r.openReceipt.entry.mark r.exit.mark = 0
    rw [relativePotential, returned, sub_self]
  · intro leg hleg
    simp only [temporal, List.mem_cons] at hleg
    rcases hleg with rfl | hleg
    · exact r.openReceipt.entryHair_nonnegative
    · rcases hleg with rfl | hleg
      · exact r.exitHair_nonnegative
      · simp at hleg

/-- The representation-free natural form preserves the receipt's derived costs and P&L. -/
theorem naturalForm_preserves_assessment (r : ClosedReceipt) :
    (naturalForm r.temporal).accumulatedHair = r.temporal.accumulatedHair ∧
    (naturalForm r.temporal).net = r.temporal.net :=
  ⟨accumulatedHair_naturalForm _, net_naturalForm _⟩

/-- Every admissible closure derivation is forced to return the same natural receipt. -/
theorem derivation_forced (D : ClosureDerivation) (r : ClosedReceipt) :
    D.derive r.temporal = naturalForm r.temporal :=
  D.derive_eq _

/-! ## Collected observation-to-closure derivation -/

theorem live_receipt_derivation (D : ClosureDerivation) (r : ClosedReceipt) :
    (∃! entryFill : ℚ,
      FillRel r.openReceipt.entryBall r.openReceipt.orientation.entrySide entryFill) ∧
    (∃! exitFill : ℚ,
      FillRel r.exitBall r.openReceipt.orientation.exitSide exitFill) ∧
    0 ≤ zeroHair r.openReceipt.entryTrade ∧
    0 ≤ zeroHair r.exitTrade ∧
    r.temporal.net =
      r.openReceipt.orientation.entryQty r.openReceipt.magnitude *
          relativePotential r.openReceipt.entry.mark r.exit.mark -
        (zeroHair r.openReceipt.entryTrade + zeroHair r.exitTrade) ∧
    (0 < r.temporal.net ↔
      zeroHair r.openReceipt.entryTrade + zeroHair r.exitTrade <
        r.openReceipt.orientation.entryQty r.openReceipt.magnitude *
          relativePotential r.openReceipt.entry.mark r.exit.mark) ∧
    D.derive r.temporal = naturalForm r.temporal ∧
    (naturalForm r.temporal).net = r.temporal.net :=
  ⟨r.openReceipt.entry_fill_unique,
    r.exit_fill_unique,
    r.openReceipt.entryHair_nonnegative,
    r.exitHair_nonnegative,
    r.net_eq_relativePotential_sub_hairs,
    r.profitable_iff_relativePotential_exceeds_hairs,
    r.derivation_forced D,
    net_naturalForm _⟩

end ClosedReceipt

#print axioms NRRFTradingReceipt.OpenReceipt.entry_fill_unique
#print axioms NRRFTradingReceipt.ClosedReceipt.entry_selection_no_future
#print axioms NRRFTradingReceipt.ClosedReceipt.net_eq_relativePotential_sub_hairs
#print axioms NRRFTradingReceipt.ClosedReceipt.returning_nonpositive
#print axioms NRRFTradingReceipt.ClosedReceipt.live_receipt_derivation

end NRRFTradingReceipt
