import NRRFTradingNaturalFormSelectionThroughoutBridge

/-!
# Life action/potential with global hair as the trading executor

This module gives the trading interface the action rule requested by the user.  It does not assume
Turing completeness.  The already-defined life loop supplies two explicit continuations:

* `ballReturn` is the actual/action continuation;
* `hairReturn` is the inverse potential continuation.

The trading translation is equally explicit.  `actionPotential` is the position-weighted relative
price potential, `globalHair` is the accumulated 0-hair derived from every closed local leg, and
`globalHairExecutor` acts exactly when the potential strictly exceeds that global hair.  Thus the
executor is not an external profit rule: it is the existing P&L closure equation read as an action.

For a life presentation, execution additionally requires the supplied potential presentation to
close as the black mirror of the actual presentation.  Neither phase closure alone nor positive
potential before hair can execute.  The result is an execution *verdict*; authenticated exchange
authority remains a separate boundary.
-/

namespace NRRFTradingLifeExecutor

open NRRF800 NRRF801
open NRRFTradingDelta NRRFTradingDelta.TemporalClosure
open NRRFTradingReceipt
open NRRFTradingBlackMirror NRRFTradingBlackMirror.PhaseReading

/-! ## The global-hair executor -/

/-- The action emitted by the relational executor. -/
inductive Verdict
  | hold
  | act
  deriving DecidableEq, Repr

/-- Potential available to action before accumulated global hair is returned. -/
def actionPotential (t : TemporalClosure) : ℚ :=
  t.qty * relativePotential t.entryMark t.exitMark

/-- The derived global hair across every closed local leg. -/
def globalHair (t : TemporalClosure) : ℚ :=
  t.accumulatedHair

/-- Global hair executes exactly when the action potential strictly returns beyond it. -/
def globalHairExecutor (t : TemporalClosure) : Verdict :=
  if globalHair t < actionPotential t then .act else .hold

theorem globalHairExecutor_act_iff (t : TemporalClosure) :
    globalHairExecutor t = .act ↔ globalHair t < actionPotential t := by
  unfold globalHairExecutor
  by_cases h : globalHair t < actionPotential t <;> simp [h]

theorem globalHairExecutor_hold_iff (t : TemporalClosure) :
    globalHairExecutor t = .hold ↔ actionPotential t ≤ globalHair t := by
  unfold globalHairExecutor
  by_cases h : globalHair t < actionPotential t
  · simp [h, not_le_of_gt h]
  · simp [h, le_of_not_gt h]

/-- The executor is exactly the existing completed-profit equation, not a new metric. -/
theorem globalHairExecutor_act_iff_profitable (t : TemporalClosure) :
    globalHairExecutor t = .act ↔ 0 < t.net := by
  rw [globalHairExecutor_act_iff, profitable_iff_potential_exceeds_hair]
  rfl

/-- Global hair and action potential are both invariant under a common price translation. -/
@[simp] theorem globalHair_shift (c : ℚ) (t : TemporalClosure) :
    globalHair (t.shift c) = globalHair t :=
  accumulatedHair_shift c t

@[simp] theorem actionPotential_shift (c : ℚ) (t : TemporalClosure) :
    actionPotential (t.shift c) = actionPotential t := by
  simp [actionPotential, TemporalClosure.shift]

/-- Consequently the executor belongs to translational truth rather than an absolute price level. -/
@[simp] theorem globalHairExecutor_shift (c : ℚ) (t : TemporalClosure) :
    globalHairExecutor (t.shift c) = globalHairExecutor t := by
  simp [globalHairExecutor]

/-! ## Actual life, inverse potential, and execution -/

/-- One completed trading receipt with its supplied actual and potential life presentations. -/
structure LifeInput where
  receipt : ClosedReceipt
  action : PhaseReading
  potential : PhaseReading

/-- The potential closes the life input precisely when it is the action's black mirror. -/
def LifeInput.Closes (x : LifeInput) : Prop :=
  x.action.MirrorCoherent x.potential

instance (x : LifeInput) : Decidable x.Closes :=
  inferInstanceAs (Decidable (x.potential = x.action.reciprocal))

/-- The actual continuation is the ball return. -/
def LifeInput.actionRun (x : LifeInput) (n : ℕ) : Life :=
  ballReturn^[n] x.action.toLife

/-- The potential continuation is the inverse hair return. -/
def LifeInput.potentialRun (x : LifeInput) (n : ℕ) : Life :=
  hairReturn^[n] x.potential.toLife

@[simp] theorem LifeInput.actionRun_four (x : LifeInput) : x.actionRun 4 = x.action.toLife := by
  simpa [actionRun] using congrFun ballReturn_period x.action.toLife

@[simp] theorem LifeInput.potentialRun_four (x : LifeInput) :
    x.potentialRun 4 = x.potential.toLife := by
  simpa [potentialRun] using congrFun hairReturn_period x.potential.toLife

theorem LifeInput.closes_iff_blackMirror (x : LifeInput) :
    x.Closes ↔ x.potential.toLife = blackMirror x.action.toLife :=
  x.action.mirrorCoherent_iff_life x.potential

/-- The life executor: close action with inverse potential, then let global hair decide. -/
def lifeExecutor (x : LifeInput) : Verdict :=
  if x.Closes then globalHairExecutor x.receipt.temporal else .hold

theorem lifeExecutor_act_iff (x : LifeInput) :
    lifeExecutor x = .act ↔ x.Closes ∧ 0 < x.receipt.temporal.net := by
  unfold lifeExecutor
  by_cases h : x.Closes
  · simp [h, globalHairExecutor_act_iff_profitable]
  · simp [h]

/-- Phase closure alone cannot execute a nonprofitable receipt. -/
theorem closed_nonprofitable_holds (x : LifeInput) (closed : x.Closes)
    (nonprofitable : x.receipt.temporal.net ≤ 0) : lifeExecutor x = .hold := by
  rw [show lifeExecutor x = if x.Closes then globalHairExecutor x.receipt.temporal else .hold by rfl,
    if_pos closed]
  apply (globalHairExecutor_hold_iff _).2
  apply sub_nonpos.mp
  simpa [actionPotential, globalHair, TemporalClosure.net] using nonprofitable

/-- Positive receipt potential cannot execute when action and inverse potential do not close. -/
theorem profitable_unclosed_holds (x : LifeInput) (openLife : ¬ x.Closes) :
    lifeExecutor x = .hold := by
  simp [lifeExecutor, openLife]

/-- Global hair on an authenticated receipt is exactly the two independently derived local hairs. -/
theorem receipt_globalHair_eq (x : LifeInput) :
    globalHair x.receipt.temporal =
      zeroHair x.receipt.openReceipt.entryTrade + zeroHair x.receipt.exitTrade := by
  exact x.receipt.accumulatedHair_temporal

/-- Collected statement: the two life continuations close in four, and execution is exactly
black-mirror closure plus completed positive flow beyond global hair. -/
theorem life_action_potential_global_hair_answer (x : LifeInput) :
    x.actionRun 4 = x.action.toLife ∧
    x.potentialRun 4 = x.potential.toLife ∧
    (x.Closes ↔ x.potential.toLife = blackMirror x.action.toLife) ∧
    (lifeExecutor x = .act ↔
      x.Closes ∧ globalHair x.receipt.temporal < actionPotential x.receipt.temporal) := by
  refine ⟨x.actionRun_four, x.potentialRun_four, x.closes_iff_blackMirror, ?_⟩
  rw [lifeExecutor_act_iff]
  apply and_congr_right
  intro _
  simpa [globalHair, actionPotential] using
    x.receipt.temporal.profitable_iff_potential_exceeds_hair

#print axioms NRRFTradingLifeExecutor.globalHairExecutor_act_iff_profitable
#print axioms NRRFTradingLifeExecutor.lifeExecutor_act_iff
#print axioms NRRFTradingLifeExecutor.life_action_potential_global_hair_answer

end NRRFTradingLifeExecutor
