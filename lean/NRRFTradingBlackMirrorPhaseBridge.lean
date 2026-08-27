import NRRF801BlackMirrorRelativeTranslationOneToOneClosureUnitaryCurvature
import NRRFTradingLiveObservationReceiptDerivation

/-!
# Trading bridge for the NRRF801 black-mirror phase

This module connects the verified receipt boundary to the recovered NRRF800/801 ball--hair
construction without turning that construction into an unproved price predictor.

The receipt remains the source of price, derived hair/cost, temporal potential, and P&L.  A
`PhaseReading` adds one explicitly supplied local reading in `ZMod 4`.  Reversing the economic
orientation and negating that phase is exactly the NRRF801 black mirror.  It is deliberately a
reading, not a time-reversed receipt: the receipt's source identity and forward chronology are
never rewritten.

The load-bearing negative result is `receipt_does_not_select_phase`: every phase can accompany the
same verified receipt.  Therefore neither profit nor cost may be used to manufacture an NRRF801
phase.  A running adapter must derive the phase from local observations and separately test mirror
coherence and the full one-to-one continuity conditions.
-/

namespace NRRFTradingBlackMirror

open NRRF800 NRRF801
open NRRFTradingDelta NRRFTradingFullClosure NRRFTradingReceipt

/-! ## Reciprocal orientation as the hand translation -/

/-- The long/short orientation read as the right/left hand of the phase interface. -/
def orientationHand : Orientation → Hand
  | .long => .right
  | .short => .left

/-- The reciprocal economic reading.  This changes no receipt chronology. -/
def mirrorOrientation : Orientation → Orientation
  | .long => .short
  | .short => .long

@[simp] theorem mirrorOrientation_mirror (o : Orientation) :
    mirrorOrientation (mirrorOrientation o) = o := by
  cases o <;> rfl

@[simp] theorem orientationHand_mirror (o : Orientation) :
    orientationHand (mirrorOrientation o) = (orientationHand o).inv := by
  cases o <;> rfl

/-! ## A phase is an explicit local reading -/

/-- One orientation/phase presentation of the market interface. -/
structure PhaseReading where
  orientation : Orientation
  phase : Ball
  deriving DecidableEq, Repr

namespace PhaseReading

/-- Translate the trading presentation into the existing NRRF801 life carrier. -/
def toLife (r : PhaseReading) : Life := ⟨orientationHand r.orientation, r.phase⟩

/-- Reciprocal presentation: reverse orientation and reflect the phase. -/
def reciprocal (r : PhaseReading) : PhaseReading := ⟨mirrorOrientation r.orientation, -r.phase⟩

@[simp] theorem reciprocal_reciprocal (r : PhaseReading) : r.reciprocal.reciprocal = r := by
  cases r with
  | mk o b => simp [reciprocal]

/-- The reciprocal trading presentation is literally the NRRF801 black mirror. -/
@[simp] theorem toLife_reciprocal (r : PhaseReading) :
    r.reciprocal.toLife = blackMirror r.toLife := by
  cases r with
  | mk o b => simp [reciprocal, toLife, blackMirror]

theorem toLife_injective : Function.Injective toLife := by
  intro a b h
  cases a with
  | mk ao ap =>
      cases b with
      | mk bo bp =>
          cases ao <;> cases bo <;> simp [toLife, orientationHand] at h ⊢ <;> exact h

/-- Two independently supplied readings close as a reciprocal pair. -/
def MirrorCoherent (actual potential : PhaseReading) : Prop :=
  potential = actual.reciprocal

theorem mirrorCoherent_iff_life (actual potential : PhaseReading) :
    MirrorCoherent actual potential ↔ potential.toLife = blackMirror actual.toLife := by
  constructor
  · intro h
    rw [h, toLife_reciprocal]
  · intro h
    apply toLife_injective
    rw [toLife_reciprocal]
    exact h

end PhaseReading

/-! ## The receipt and phase remain distinct layers -/

/-- A verified closed receipt accompanied by an explicitly derived market phase. -/
structure PhasedReceipt where
  receipt : ClosedReceipt
  phase : Ball

namespace PhasedReceipt

def reading (r : PhasedReceipt) : PhaseReading :=
  ⟨r.receipt.openReceipt.orientation, r.phase⟩

/-- The receipt retains the already-proved representation-free trading natural form. -/
def naturalTrade (r : PhasedReceipt) : TemporalClosure :=
  naturalForm r.receipt.temporal

@[simp] theorem naturalTrade_net (r : PhasedReceipt) :
    r.naturalTrade.net = r.receipt.temporal.net :=
  net_naturalForm _

@[simp] theorem naturalTrade_hair (r : PhasedReceipt) :
    r.naturalTrade.accumulatedHair = r.receipt.temporal.accumulatedHair :=
  accumulatedHair_naturalForm _

/-- Changing only the phase cannot alter the trade, cost, or P&L natural form. -/
theorem same_receipt_same_naturalTrade (a b : PhasedReceipt) (h : a.receipt = b.receipt) :
    a.naturalTrade = b.naturalTrade := by
  simp [naturalTrade, h]

/-- The exact interface gap: a verified receipt admits every phase as an additional reading. -/
theorem every_phase_accompanies (r : ClosedReceipt) (b : Ball) :
    ∃ p : PhasedReceipt, p.receipt = r ∧ p.phase = b :=
  ⟨⟨r, b⟩, rfl, rfl⟩

/-- Consequently the receipt closure itself does not select an NRRF801 phase. -/
theorem receipt_does_not_select_phase (r : ClosedReceipt) :
    ∃ p q : PhasedReceipt,
      p.receipt = r ∧ q.receipt = r ∧ p.naturalTrade = q.naturalTrade ∧ p.phase ≠ q.phase := by
  let p : PhasedReceipt := ⟨r, 0⟩
  let q : PhasedReceipt := ⟨r, 1⟩
  refine ⟨p, q, rfl, rfl, rfl, ?_⟩
  change (0 : Ball) ≠ 1
  decide

end PhasedReceipt

/-! ## What a running system must admit before using continuum language -/

/-- A candidate phase evolution together with the actual NRRF801 continuity evidence. -/
structure AdmittedPhaseEvolution where
  evolve : Ball → Ball
  continuous : OneToOneContinuity evolve

/-- An admitted evolution is forced to be a translation; this fact is tested, not assumed. -/
theorem AdmittedPhaseEvolution.forced_translation (e : AdmittedPhaseEvolution) :
    ∃ c : Ball, ∀ b, e.evolve b = b + c :=
  (oneToOneContinuity_iff_translation e.evolve).1 e.continuous

/-- The bridge's complete statement: reciprocal readings are exactly the black mirror, receipt
assessment is phase-independent, and a continuum evolution must separately carry its evidence. -/
theorem nrrf801_trading_bridge (r : ClosedReceipt) (x y : PhaseReading)
    (hxy : x.MirrorCoherent y) (e : AdmittedPhaseEvolution) :
    y.toLife = blackMirror x.toLife ∧
    (naturalForm r.temporal).net = r.temporal.net ∧
    (naturalForm r.temporal).accumulatedHair = r.temporal.accumulatedHair ∧
    (∃ p q : PhasedReceipt,
      p.receipt = r ∧ q.receipt = r ∧ p.naturalTrade = q.naturalTrade ∧ p.phase ≠ q.phase) ∧
    ∃ c : Ball, ∀ b, e.evolve b = b + c :=
  ⟨(x.mirrorCoherent_iff_life y).1 hxy,
    net_naturalForm _,
    accumulatedHair_naturalForm _,
    PhasedReceipt.receipt_does_not_select_phase r,
    e.forced_translation⟩

#print axioms NRRFTradingBlackMirror.PhaseReading.toLife_reciprocal
#print axioms NRRFTradingBlackMirror.PhasedReceipt.receipt_does_not_select_phase
#print axioms NRRFTradingBlackMirror.nrrf801_trading_bridge

end NRRFTradingBlackMirror
