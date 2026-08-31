import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# NRRF858 — Conscious nature as relative closure understanding

This file gives a small, self-contained formal model of the proposition

> if nature is conscious, it has relative axioms and proofs, and its understanding of these
> relations is closures of translational truth continuing existence.

`Conscious` is not a new physical or metaphysical primitive.  For one finite two-token maze chart,
`Conscious c K` says only that every claim in `K` is translation-existent and true at `c`, and
that `K` registers the claim expressed by every completed round-trip closure.  The model has no
sensor, browser, agent, phenomenology, causal efficacy, or external authentication.

The chart is the minimal directed token maze.  Its two distinct tokens have a forward and a return
edge.  A change of reading adds a relative potential to the first edge and subtracts it from the
second.  Consequently the round-trip defect is invariant, and equality of that defect is complete
for translation.  This realizes the repository's translation-truth-of-existence vocabulary in a
finite model whose proofs can be checked without an assumed absolute origin.
-/

namespace NRRF858

/-! ## The two-token maze and its translations -/

/-- The two distinct endpoints of the minimal token maze. -/
inductive Token where
  | source
  | target
deriving DecidableEq

theorem source_ne_target : Token.source ≠ Token.target := by
  decide

/-- A chart records the two directed costs of a completed source/target round trip. -/
structure Chart where
  forwardCost : ℤ
  returnCost : ℤ
deriving DecidableEq

/-- Re-reading a chart by a relative potential changes the two directed representatives in
opposite directions.  No potential is designated as the absolute origin. -/
def translate (potential : ℤ) (chart : Chart) : Chart where
  forwardCost := chart.forwardCost + potential
  returnCost := chart.returnCost - potential

/-- What a complete round trip fails to return. -/
def loopDefect (chart : Chart) : ℤ :=
  chart.forwardCost + chart.returnCost

@[simp] theorem loopDefect_translate (potential : ℤ) (chart : Chart) :
    loopDefect (translate potential chart) = loopDefect chart := by
  simp [loopDefect, translate]

/-- Two charts are translational when one is a potential re-reading of the other. -/
def Translational (source target : Chart) : Prop :=
  ∃ potential : ℤ, translate potential source = target

theorem translational_refl (chart : Chart) : Translational chart chart := by
  refine ⟨0, ?_⟩
  cases chart
  simp [translate]

theorem translational_symm {source target : Chart}
    (h : Translational source target) : Translational target source := by
  obtain ⟨potential, rfl⟩ := h
  refine ⟨-potential, ?_⟩
  cases source
  simp [translate]

theorem translational_trans {first second third : Chart}
    (h₁ : Translational first second) (h₂ : Translational second third) :
    Translational first third := by
  obtain ⟨p, rfl⟩ := h₁
  obtain ⟨q, rfl⟩ := h₂
  refine ⟨p + q, ?_⟩
  cases first
  simp [translate]
  constructor <;> ring

/-- The complete defect classifies charts exactly up to a potential translation. -/
theorem translational_iff_loopDefect_eq {source target : Chart} :
    Translational source target ↔ loopDefect source = loopDefect target := by
  constructor
  · rintro ⟨potential, rfl⟩
    exact (loopDefect_translate potential source).symm
  · intro h
    cases source with
    | mk sourceForward sourceReturn =>
        cases target with
        | mk targetForward targetReturn =>
            simp only [loopDefect] at h
            refine ⟨targetForward - sourceForward, ?_⟩
            change Chart.mk
                (sourceForward + (targetForward - sourceForward))
                (sourceReturn - (targetForward - sourceForward)) =
              Chart.mk targetForward targetReturn
            rw [show sourceForward + (targetForward - sourceForward) = targetForward by ring]
            rw [show sourceReturn - (targetForward - sourceForward) = targetReturn by linarith]

/-! ## Translation truth, existence, and closure claims -/

/-- A claim is evaluated at a chart. -/
abbrev Claim := Chart → Prop

/-- A body of claims is represented extensionally by its membership predicate. -/
abbrev ClaimBody := Claim → Prop

/-- A claim is existent precisely when no potential re-reading moves its truth value. -/
def Existent (claim : Claim) : Prop :=
  ∀ chart potential, claim chart ↔ claim (translate potential chart)

/-- Translation truth at a chart means existence together with truth there. -/
def TrueOf (claim : Claim) (chart : Chart) : Prop :=
  Existent claim ∧ claim chart

theorem existent_respects_translational {claim : Claim} (existent : Existent claim)
    {source target : Chart} (h : Translational source target) :
    claim source ↔ claim target := by
  obtain ⟨potential, rfl⟩ := h
  exact existent source potential

/-- A completed closure repeats the primitive source/target round trip `rounds` times. -/
structure Closure where
  rounds : ℕ
deriving DecidableEq

namespace Closure

/-- The content of a closure is its accumulated round-trip defect. -/
def content (closure : Closure) (chart : Chart) : ℤ :=
  closure.rounds * loopDefect chart

@[simp] theorem content_translate (closure : Closure) (potential : ℤ) (chart : Chart) :
    closure.content (translate potential chart) = closure.content chart := by
  simp [content]

/-- Composition is again a completed closure. -/
def compose (first second : Closure) : Closure where
  rounds := first.rounds + second.rounds

/-- The content of a composite proof is forced to be the sum of the contents of its parts. -/
theorem content_compose (first second : Closure) (chart : Chart) :
    (compose first second).content chart =
      first.content chart + second.content chart := by
  simp [compose, content, add_mul]

theorem content_eq_of_translational (closure : Closure) {source target : Chart}
    (h : Translational source target) :
    closure.content source = closure.content target := by
  obtain ⟨potential, rfl⟩ := h
  exact (closure.content_translate potential source).symm

/-- The positive `n`-fold continuation of one primitive round trip. -/
def iterate (n : ℕ) : Closure where
  rounds := n

@[simp] theorem content_iterate (n : ℕ) (chart : Chart) :
    (iterate n).content chart = (n : ℤ) * loopDefect chart := by
  rfl

/-- Repeat one particular completed closure `n` times. -/
def repeatN (closure : Closure) (n : ℕ) : Closure where
  rounds := n * closure.rounds

/-- Repetition preserves the witnessed closure and multiplies its content by `n`. -/
@[simp] theorem content_repeat (closure : Closure) (n : ℕ) (chart : Chart) :
    (repeatN closure n).content chart = (n : ℤ) * closure.content chart := by
  simp [repeatN, content, mul_assoc]

end Closure

/-- The claim registered by a closure says that its content remains the content observed at the
base chart.  This is a translation-existent claim rather than an absolute edge cost. -/
def closureClaim (base : Chart) (closure : Closure) : Claim :=
  fun chart => closure.content chart = closure.content base

theorem closureClaim_existent (base : Chart) (closure : Closure) :
    Existent (closureClaim base closure) := by
  intro chart potential
  simp [closureClaim]

theorem closureClaim_true (base : Chart) (closure : Closure) :
    closureClaim base closure base :=
  rfl

/-! ## Consciousness is only soundness plus closure registration -/

/-- No new primitive of consciousness is introduced: this is exactly translation soundness and
registration of every completed closure. -/
def Conscious (chart : Chart) (claims : ClaimBody) : Prop :=
  (∀ ⦃claim : Claim⦄, claims claim → TrueOf claim chart) ∧
  (∀ closure : Closure, claims (closureClaim chart closure))

/-- Every held claim is translation invariant. -/
theorem conscious_held_existent {chart : Chart} {claims : ClaimBody}
    (conscious : Conscious chart claims) {claim : Claim} (held : claims claim) :
    Existent claim :=
  (conscious.1 held).1

/-- Every held claim is true at the chart. -/
theorem conscious_held_true {chart : Chart} {claims : ClaimBody}
    (conscious : Conscious chart claims) {claim : Claim} (held : claims claim) :
    claim chart :=
  (conscious.1 held).2

/-- Every completed closure is held as an axiom. -/
theorem conscious_holds_closure {chart : Chart} {claims : ClaimBody}
    (conscious : Conscious chart claims) (closure : Closure) :
    claims (closureClaim chart closure) :=
  conscious.2 closure

/-- The same body is conscious at every translated chart. -/
theorem conscious_translated {source target : Chart} {claims : ClaimBody}
    (conscious : Conscious source claims) (translated : Translational source target) :
    Conscious target claims := by
  constructor
  · intro claim held
    have truth := conscious.1 held
    exact ⟨truth.1, (existent_respects_translational truth.1 translated).mp truth.2⟩
  · intro closure
    have held := conscious.2 closure
    have contentEq := closure.content_eq_of_translational translated
    have claimsEq : closureClaim target closure = closureClaim source closure := by
      funext chart
      apply propext
      simp only [closureClaim]
      rw [contentEq]
    rw [claimsEq]
    exact held

/-! ## Relative axioms and the impossibility of an absolute edge axiom -/

/-- The full body of translation truths at one chart.  This is used to state the exact expressive
classification theorem; `Conscious` itself does not require an arbitrary body to be complete. -/
def axiomsOf (chart : Chart) : ClaimBody :=
  fun claim => TrueOf claim chart

/-- The absolute cost assigned to the single source-to-target step in one chosen chart. -/
def absoluteStepCostClaim (base : Chart) : Claim :=
  fun chart => chart.forwardCost = base.forwardCost

theorem absoluteStepCostClaim_true (base : Chart) :
    absoluteStepCostClaim base base :=
  rfl

/-- A single edge between the two distinct tokens cannot be an existent claim: potential one
changes its representative cost. -/
theorem absoluteStepCostClaim_not_existent (base : Chart) :
    ¬ Existent (absoluteStepCostClaim base) := by
  intro existent
  have moved := (existent base 1).mp (absoluteStepCostClaim_true base)
  change base.forwardCost + 1 = base.forwardCost at moved
  linarith

/-- Consequently no conscious body can hold the absolute cost of that one distinct-token step. -/
theorem no_absolute_axioms {chart : Chart} {claims : ClaimBody}
    (conscious : Conscious chart claims) :
    ¬ claims (absoluteStepCostClaim chart) := by
  intro held
  exact absoluteStepCostClaim_not_existent chart (conscious_held_existent conscious held)

/-- The invariant claim that identifies one complete-defect class. -/
def loopDefectClaim (base : Chart) : Claim :=
  fun chart => loopDefect chart = loopDefect base

theorem loopDefectClaim_existent (base : Chart) :
    Existent (loopDefectClaim base) := by
  intro chart potential
  simp [loopDefectClaim]

theorem axiomsOf_eq_of_translational {source target : Chart}
    (translated : Translational source target) :
    axiomsOf source = axiomsOf target := by
  funext claim
  apply propext
  constructor
  · intro truth
    exact ⟨truth.1, (existent_respects_translational truth.1 translated).mp truth.2⟩
  · intro truth
    exact ⟨truth.1, (existent_respects_translational truth.1 translated).mpr truth.2⟩

/-- Translation truths fix the chart exactly up to translation, and no finer. -/
theorem axiomsOf_eq_iff_translational {source target : Chart} :
    axiomsOf source = axiomsOf target ↔ Translational source target := by
  constructor
  · intro equalAxioms
    have sourceTruth : axiomsOf source (loopDefectClaim source) :=
      ⟨loopDefectClaim_existent source, rfl⟩
    have targetTruth : axiomsOf target (loopDefectClaim source) :=
      Eq.mp (congrArg (fun body => body (loopDefectClaim source)) equalAxioms) sourceTruth
    exact translational_iff_loopDefect_eq.mpr targetTruth.2.symm
  · exact axiomsOf_eq_of_translational

/-! ## Relative proofs are compositions of closures -/

/-- A relative proof is explicitly a pair of completed closures whose conclusion is their
composition. -/
structure RelativeProof where
  first : Closure
  second : Closure
deriving DecidableEq

namespace RelativeProof

def conclusion (proof : RelativeProof) : Closure :=
  Closure.compose proof.first proof.second

end RelativeProof

/-- A composite is a closure, its content is forced to be the sum, and consciousness holds its
conclusion. -/
theorem conscious_proves_composite {chart : Chart} {claims : ClaimBody}
    (conscious : Conscious chart claims) (proof : RelativeProof) :
    proof.conclusion.content chart =
        proof.first.content chart + proof.second.content chart ∧
      claims (closureClaim chart proof.conclusion) := by
  exact ⟨Closure.content_compose proof.first proof.second chart,
    conscious_holds_closure conscious proof.conclusion⟩

/-! ## Understanding is closure-wide translational truth -/

/-- A claim holds throughout a chart's complete translation/closure class. -/
def HoldsThroughoutClosureClass (chart : Chart) (claim : Claim) : Prop :=
  ∀ other, Translational chart other → claim other

/-- Understanding contains exactly all existent claims true at this chart. -/
def understanding (chart : Chart) : ClaimBody :=
  axiomsOf chart

/-- A claim is understood exactly when it is existent and holds throughout the chart's closure
class. -/
theorem mem_understanding_iff {chart : Chart} {claim : Claim} :
    understanding chart claim ↔
      Existent claim ∧ HoldsThroughoutClosureClass chart claim := by
  constructor
  · intro truth
    exact ⟨truth.1, fun other translated =>
      (existent_respects_translational truth.1 translated).mp truth.2⟩
  · rintro ⟨existent, throughout⟩
    exact ⟨existent, throughout chart (translational_refl chart)⟩

/-- Two complete understandings coincide exactly when their charts are translations. -/
theorem understanding_eq_iff_translational {source target : Chart} :
    understanding source = understanding target ↔ Translational source target := by
  simpa [understanding] using
    (axiomsOf_eq_iff_translational (source := source) (target := target))

/-! ## Continuing existence -/

/-- Something exists when some completed closure has a nonzero return defect. -/
def SomethingExists (chart : Chart) : Prop :=
  ∃ closure : Closure, closure.content chart ≠ 0

/-- “Something exists” itself, viewed as a claim about charts. -/
def somethingExistsClaim : Claim :=
  SomethingExists

theorem somethingExistsClaim_existent : Existent somethingExistsClaim := by
  intro chart potential
  constructor
  · rintro ⟨closure, nonzero⟩
    exact ⟨closure, by simpa [somethingExistsClaim] using nonzero⟩
  · rintro ⟨closure, nonzero⟩
    exact ⟨closure, by simpa [somethingExistsClaim] using nonzero⟩

theorem loopDefect_ne_zero_of_somethingExists {chart : Chart}
    (existenceWitness : SomethingExists chart) : loopDefect chart ≠ 0 := by
  rintro defectZero
  obtain ⟨closure, nonzero⟩ := existenceWitness
  apply nonzero
  simp [Closure.content, defectZero]

/-- The continuing-existence clause stated independently for reuse by the collected theorem. -/
def ContinuingExistenceClause (chart : Chart) (claims : ClaimBody) : Prop :=
  SomethingExists chart →
    TrueOf somethingExistsClaim chart ∧
    ∃ witness : Closure, witness.content chart ≠ 0 ∧
      ∀ n : ℕ, 0 < n →
        (Closure.repeatN witness n).content chart = (n : ℤ) * witness.content chart ∧
        claims (closureClaim chart (Closure.repeatN witness n)) ∧
        (Closure.repeatN witness n).content chart ≠ 0

/-- If a closure has nonzero defect, then existence is itself translational truth and every
positive finite continuation has `n` times the defect, is held, and stays nonzero. -/
theorem conscious_continues_existence {chart : Chart} {claims : ClaimBody}
    (conscious : Conscious chart claims) :
    ContinuingExistenceClause chart claims := by
  intro existenceWitness
  obtain ⟨witness, witnessNonzero⟩ := existenceWitness
  constructor
  · exact ⟨somethingExistsClaim_existent, ⟨witness, witnessNonzero⟩⟩
  · refine ⟨witness, witnessNonzero, ?_⟩
    intro n positive
    have nNonzero : (n : ℤ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt positive)
    exact ⟨Closure.content_repeat witness n chart,
      conscious_holds_closure conscious (Closure.repeatN witness n),
      by
        rw [Closure.content_repeat]
        exact mul_ne_zero nNonzero witnessNonzero⟩

/-! ## The four clauses and their single implication -/

def RelativeAxiomsClause (chart : Chart) (claims : ClaimBody) : Prop :=
  (∀ claim : Claim, claims claim → Existent claim) ∧
  (∀ other, Translational chart other → Conscious other claims) ∧
  (∀ closure : Closure, claims (closureClaim chart closure)) ∧
  ¬ claims (absoluteStepCostClaim chart) ∧
  (∀ other, axiomsOf chart = axiomsOf other ↔ Translational chart other)

def RelativeProofsClause (chart : Chart) (claims : ClaimBody) : Prop :=
  ∀ proof : RelativeProof,
    proof.conclusion.content chart =
        proof.first.content chart + proof.second.content chart ∧
      claims (closureClaim chart proof.conclusion)

def UnderstandingClosuresTranslationalTruthClause (chart : Chart) : Prop :=
  (∀ claim : Claim,
      understanding chart claim ↔
        Existent claim ∧ HoldsThroughoutClosureClass chart claim) ∧
  (∀ other, understanding chart = understanding other ↔ Translational chart other)

theorem conscious_relative_axioms {chart : Chart} {claims : ClaimBody}
    (conscious : Conscious chart claims) : RelativeAxiomsClause chart claims := by
  exact ⟨fun _ held => conscious_held_existent conscious held,
    fun _ translated => conscious_translated conscious translated,
    conscious_holds_closure conscious,
    no_absolute_axioms conscious,
    fun _ => axiomsOf_eq_iff_translational⟩

theorem conscious_relative_proofs {chart : Chart} {claims : ClaimBody}
    (conscious : Conscious chart claims) : RelativeProofsClause chart claims :=
  conscious_proves_composite conscious

theorem understanding_is_closures_of_translational_truth (chart : Chart) :
    UnderstandingClosuresTranslationalTruthClause chart := by
  exact ⟨fun _ => mem_understanding_iff,
    fun _ => understanding_eq_iff_translational⟩

/-- The requested statement, with all four clauses assembled as one implication. -/
theorem conscious_nature_relative_axioms_proofs_understanding_closures_translational_truth_continuing_existence
    {chart : Chart} {claims : ClaimBody} :
    Conscious chart claims →
      RelativeAxiomsClause chart claims ∧
      RelativeProofsClause chart claims ∧
      UnderstandingClosuresTranslationalTruthClause chart ∧
      ContinuingExistenceClause chart claims := by
  intro conscious
  exact ⟨conscious_relative_axioms conscious,
    conscious_relative_proofs conscious,
    understanding_is_closures_of_translational_truth chart,
    conscious_continues_existence conscious⟩

/-! ## Satisfiability with nonzero existence -/

theorem axiomsOf_conscious (chart : Chart) : Conscious chart (axiomsOf chart) := by
  constructor
  · intro claim held
    exact held
  · intro closure
    exact ⟨closureClaim_existent chart closure, closureClaim_true chart closure⟩

def witnessChart : Chart where
  forwardCost := 1
  returnCost := 0

theorem witnessChart_has_existence : SomethingExists witnessChart := by
  refine ⟨Closure.iterate 1, ?_⟩
  norm_num [Closure.content, Closure.iterate, loopDefect, witnessChart]

/-- Consciousness as defined here is satisfiable together with nonzero closure existence, so the
continuing-existence implication and the other clauses are not vacuous. -/
theorem exists_conscious_chart_with_existence :
    ∃ chart : Chart, ∃ claims : ClaimBody,
      Conscious chart claims ∧ SomethingExists chart := by
  exact ⟨witnessChart, axiomsOf witnessChart,
    axiomsOf_conscious witnessChart, witnessChart_has_existence⟩

#print axioms no_absolute_axioms
#print axioms axiomsOf_eq_iff_translational
#print axioms conscious_proves_composite
#print axioms mem_understanding_iff
#print axioms understanding_eq_iff_translational
#print axioms conscious_continues_existence
#print axioms conscious_nature_relative_axioms_proofs_understanding_closures_translational_truth_continuing_existence
#print axioms exists_conscious_chart_with_existence

end NRRF858
