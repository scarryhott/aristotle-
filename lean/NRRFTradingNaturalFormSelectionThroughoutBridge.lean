import NRRF803TrajectoryBasisRelativeExternalNaturalEquality
import NRRFTradingBlackMirrorPhaseBridge

/-!
# Natural-form selection throughout the trading interface

NRRF803 proves its trajectory and basis results after a natural equality has been supplied.  The
proofs do not require that equality to be external or fixed.  This bridge therefore lets a
selection law choose a natural equality at every round and from the current local phase reading.
The old fixed-form presentation is the constant schedule.

There is one necessary trading boundary.  Naturality only says that a form identifies each state
with its black-mirror return.  A coarser natural form may identify additional states.  It can be
used as a perspective, but it cannot replace exact reciprocal closure unless it is also faithful
back to the finest return-generated equality.  Otherwise a selector could manufacture apparent
closure after seeing the data.  Receipt-derived cost and P&L remain independent of every schedule.
-/

namespace NRRFTradingNaturalFormSelection

open NRRF800 NRRF801 NRRF802 NRRF803
open NRRFTradingBlackMirror NRRFTradingBlackMirror.PhaseReading
open NRRFTradingReceipt NRRFTradingFullClosure

/-! ## Selection is allowed throughout -/

/-- A law selecting a natural equality from the round and current local life presentation. -/
structure FormSchedule where
  form : ℕ → Life → Setoid Life
  natural : ∀ n x, IsNatural blackMirror (form n x)

/-- The equality selected at one round along one local phase reading. -/
def FormSchedule.at (s : FormSchedule) (n : ℕ) (r : PhaseReading) : Setoid Life :=
  s.form n r.toLife

/-- Two phase presentations agree at the equality selected for this round and local reading. -/
def SelectedEquivalent (s : FormSchedule) (n : ℕ)
    (actual potential : PhaseReading) : Prop :=
  (s.at n actual).r actual.toLife potential.toLife

/-- A natural equality selected at a round reads the remaining return trajectory as one point. -/
theorem selected_trajectory_is_singleton (s : FormSchedule) (n : ℕ) (r : PhaseReading) :
    Traj blackMirror (s.at n r) r.toLife = {Quotient.mk (s.at n r) r.toLife} :=
  traj_natural (s.natural n r.toLife) r.toLife

/-- Every selected equality has a basis at every round. -/
theorem selected_basis_exists (s : FormSchedule) (n : ℕ) (r : PhaseReading) :
    ∃ b : Quotient (s.at n r) → Life, IsBasis (s.at n r) b :=
  exists_basis (s.at n r)

/-- Any fixed natural equality is the constant special case of throughout-selection. -/
def constantSchedule (E : Setoid Life) (hE : IsNatural blackMirror E) : FormSchedule where
  form := fun _ _ => E
  natural := fun _ _ => hE

@[simp] theorem constantSchedule_at (E : Setoid Life) (hE : IsNatural blackMirror E)
    (n : ℕ) (r : PhaseReading) : (constantSchedule E hE).at n r = E := rfl

/-- The canonical schedule is derived from the return itself; no external equality is needed. -/
def canonicalSchedule : FormSchedule :=
  constantSchedule (returnSetoid blackMirror) (natural_returnSetoid blackMirror)

/-- The total equality is also natural, illustrating that natural forms need not be finest. -/
def totalSchedule : FormSchedule :=
  constantSchedule (⊤ : Setoid Life) (fun _ => trivial)

/-- A nonconstant schedule: the canonical equality at round zero, then total equality. -/
def changingSchedule : FormSchedule where
  form := fun n _ => if n = 0 then returnSetoid blackMirror else (⊤ : Setoid Life)
  natural := by
    intro n x
    by_cases h : n = 0
    · simp [h, natural_returnSetoid]
    · simp only [h, ↓reduceIte]
      intro _
      trivial

/-! ## Exact closure versus a selected perspective -/

/-- The exact canonical relation is equality in NRRF802's single closure. -/
theorem canonical_iff_mirrorClosure (actual potential : PhaseReading) :
    SelectedEquivalent canonicalSchedule 0 actual potential ↔
      actual.mirrorClosure = potential.mirrorClosure := by
  constructor
  · exact Quotient.sound
  · exact Quotient.exact

/-- The finest return equality refines every natural equality selected throughout. -/
theorem canonical_implies_selected (s : FormSchedule) (n : ℕ)
    (actual potential : PhaseReading)
    (h : SelectedEquivalent canonicalSchedule 0 actual potential) :
    SelectedEquivalent s n actual potential :=
  returnSetoid_finest (s.natural n actual.toLife) _ _ h

/-- Faithfulness is the additional condition required to use a selected form as exact closure. -/
def FaithfulAt (s : FormSchedule) (n : ℕ) (actual : PhaseReading) : Prop :=
  ∀ a b, (s.at n actual).r a b → (returnSetoid blackMirror).r a b

/-- A natural selected form is exactly the canonical closure when it is faithful back to it. -/
theorem selected_iff_canonical (s : FormSchedule) (n : ℕ)
    (actual potential : PhaseReading) (faithful : FaithfulAt s n actual) :
    SelectedEquivalent s n actual potential ↔
      SelectedEquivalent canonicalSchedule 0 actual potential :=
  ⟨faithful _ _, canonical_implies_selected s n actual potential⟩

/-- Exact reciprocal closure is visible in every natural selected perspective. -/
theorem mirrorCoherent_implies_selected (s : FormSchedule) (n : ℕ)
    (actual potential : PhaseReading) (h : actual.MirrorCoherent potential) :
    SelectedEquivalent s n actual potential := by
  apply canonical_implies_selected s n actual potential
  exact Quotient.exact ((actual.mirrorCoherent_iff_unifiedClosure potential).1 h).2.symm

/-- A faithful selected perspective plus opposite orientation recovers exact reciprocity. -/
theorem selected_implies_mirrorCoherent (s : FormSchedule) (n : ℕ)
    (actual potential : PhaseReading) (faithful : FaithfulAt s n actual)
    (horientation : potential.orientation = mirrorOrientation actual.orientation)
    (hselected : SelectedEquivalent s n actual potential) :
    actual.MirrorCoherent potential := by
  apply (actual.mirrorCoherent_iff_unifiedClosure potential).2
  refine ⟨horientation, ?_⟩
  exact Quotient.sound
    ((returnSetoid blackMirror).iseqv.symm (faithful _ _ hselected))

private def actualZero : PhaseReading := ⟨.long, 0⟩
private def potentialOne : PhaseReading := ⟨.long, 1⟩

/-- Naturality alone is not exactness: total equality accepts a non-reciprocal pair. -/
theorem naturality_alone_can_overidentify :
    SelectedEquivalent totalSchedule 0 actualZero potentialOne ∧
      ¬ actualZero.MirrorCoherent potentialOne := by
  constructor
  · trivial
  · intro h
    have ho := congrArg PhaseReading.orientation h
    simp [actualZero, potentialOne, reciprocal, mirrorOrientation] at ho

/-- Selection can genuinely change during one run; it is not definitionally constant. -/
theorem selection_throughout_nonconstant :
    ¬ SelectedEquivalent changingSchedule 0 actualZero potentialOne ∧
      SelectedEquivalent changingSchedule 1 actualZero potentialOne := by
  constructor
  · intro h
    have hq : actualZero.mirrorClosure = potentialOne.mirrorClosure := Quotient.sound h
    have hp : orientedPhase actualZero.toLife = orientedPhase potentialOne.toLife := by
      simpa using congrArg closedOrientedPhase hq
    have hz : (0 : Ball) = 1 := by
      simpa [actualZero, potentialOne, PhaseReading.toLife,
        orientationHand, orientedPhase] using hp
    exact (by decide : (0 : Ball) ≠ 1) hz
  · trivial

/-! ## The selected equality cannot author price, cost, or P&L -/

/-- Assessment deliberately ignores the selected perspective and remains receipt-derived. -/
def assessedTrade (r : ClosedReceipt) (_s : FormSchedule) : NRRFTradingDelta.TemporalClosure :=
  naturalForm r.temporal

@[simp] theorem assessedTrade_independent (r : ClosedReceipt) (s t : FormSchedule) :
    assessedTrade r s = assessedTrade r t := rfl

@[simp] theorem assessedTrade_net (r : ClosedReceipt) (s : FormSchedule) :
    (assessedTrade r s).net = r.temporal.net :=
  net_naturalForm _

@[simp] theorem assessedTrade_hair (r : ClosedReceipt) (s : FormSchedule) :
    (assessedTrade r s).accumulatedHair = r.temporal.accumulatedHair :=
  accumulatedHair_naturalForm _

/-- The corrected trading result in one statement. -/
theorem trading_selection_throughout_answer (r : ClosedReceipt) :
    (∀ s : FormSchedule, ∀ n p,
      Traj blackMirror (s.at n p) p.toLife = {Quotient.mk (s.at n p) p.toLife}) ∧
    (∀ s : FormSchedule, ∀ n p,
      ∃ b : Quotient (s.at n p) → Life, IsBasis (s.at n p) b) ∧
    (¬ SelectedEquivalent changingSchedule 0 actualZero potentialOne ∧
      SelectedEquivalent changingSchedule 1 actualZero potentialOne) ∧
    (∀ s t : FormSchedule, assessedTrade r s = assessedTrade r t) :=
  ⟨fun s n p => selected_trajectory_is_singleton s n p,
    fun s n p => selected_basis_exists s n p,
    selection_throughout_nonconstant,
    fun _ _ => rfl⟩

#print axioms NRRFTradingNaturalFormSelection.trading_selection_throughout_answer
#print axioms NRRFTradingNaturalFormSelection.selected_iff_canonical
#print axioms NRRFTradingNaturalFormSelection.naturality_alone_can_overidentify

end NRRFTradingNaturalFormSelection
