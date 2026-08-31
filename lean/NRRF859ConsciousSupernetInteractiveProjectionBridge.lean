import NRRF858ConsciousNatureRelativeAxiomsProofsUnderstandingClosuresTranslationalTruthContinuingExistence
import NRRF768RelativeTranslationalTruthNaturalFormSelector

/-!
# NRRF859 — Conditional conscious-Supernet interactive projection bridge

This module imports NRRF858 and gives the minimum explicit adapter from its chart-understanding
equivalence to the reachable NRRF627/768 projection framework.  It still does **not** prove that a
runtime, a user, or nature in the empirical world is conscious.  NRRF858's `Conscious` is the
defined conjunction of translation soundness and closure registration, not a sensor observation.

An abstract `Meaning` stands for a closure-return/understanding identity.  A runtime state carries
one such identity, a relative `Bool` perspective, and an append-only intent history.  A supplied
NRRF768 natural-form selector renders that identity as a perspective-relative occurrence.  The
decoder forgets only the presentation.  The central theorem proves that equality after decoding is
equivalent to actual NRRF627 occurrence translation between the rendered views.

Only within-closure intent transitions are certified here.  Moving to a new meaning requires a
different, independently witnessed closure and is deliberately outside this verifier.  Likewise,
external authentication is a caller-supplied predicate: the executable verifier checks structural
movement and append-only history, but cannot manufacture a world-grounded authentication fact.
-/

namespace NRRF859

open NRRF627

universe u e

/-! ## Runtime states, intents, views, rendering, and decoding -/

/-- An intent that can retain a view, reframe the same meaning, or focus a named meaning.  The
certificate below accepts only intents whose resulting state remains in the same translational
meaning class. -/
inductive Intent (Meaning : Type u) where
  | retain
  | reframe (perspective : Bool)
  | focus (meaning : Meaning)
deriving DecidableEq

/-- A runtime state contains no hidden global origin: its perspective is explicit, its semantic
meaning is separate from presentation, and its accepted interaction history is retained. -/
structure RuntimeState (Meaning : Type u) where
  perspective : Bool
  meaning : Meaning
  history : List (Intent Meaning)

/-- The exact formal bridge required to interpret a runtime `Meaning` as an NRRF858 chart
understanding.  An adapter must preserve and reflect NRRF858 translation; it is not inferred from
pixels, user behavior, or an arbitrary identifier. -/
structure ConsciousMeaningAdapter (Meaning : Type u) where
  encode : NRRF858.Chart → Meaning
  encode_eq_iff_translational : ∀ source target,
    encode source = encode target ↔ NRRF858.Translational source target

/-- NRRF858 understanding itself supplies a canonical mathematical adapter. -/
def understandingMeaningAdapter : ConsciousMeaningAdapter NRRF858.ClaimBody where
  encode := NRRF858.understanding
  encode_eq_iff_translational := fun _source _target =>
    NRRF858.understanding_eq_iff_translational

/-- Construct runtime state data from an NRRF858 chart only after choosing the exact adapter and
the explicit presentation/history data. -/
def RuntimeState.ofChart {Meaning : Type u} (adapter : ConsciousMeaningAdapter Meaning)
    (perspective : Bool) (history : List (Intent Meaning)) (chart : NRRF858.Chart) :
    RuntimeState Meaning where
  perspective := perspective
  meaning := adapter.encode chart
  history := history

namespace Intent

/-- The local state-shape condition asserted by an intent.  Semantic closure preservation is a
separate certificate condition below. -/
def Applies {Meaning : Type u} (intent : Intent Meaning)
    (source target : RuntimeState Meaning) : Prop :=
  match intent with
  | .retain => target.perspective = source.perspective
  | .reframe perspective => target.perspective = perspective
  | .focus meaning => target.meaning = meaning

end Intent

/-- A rendered view exposes its relative perspective and occurrence.  The occurrence is the
NRRF627 `flipFrame` presentation `(meaning, pole)`. -/
structure View (Meaning : Type u) where
  perspective : Bool
  occurrence : Meaning × Pole

namespace View

/-- Decoding returns semantic meaning and deliberately forgets the perspective-relative pole. -/
def decode {Meaning : Type u} (view : View Meaning) : Meaning :=
  view.occurrence.1

end View

/-- Two raw views are equal for the runtime exactly when their decoded meanings agree.  This does
not assert literal equality of pixels, perspective labels, or poles. -/
def ViewEq {Meaning : Type u} (left right : View Meaning) : Prop :=
  left.decode = right.decode

/-- The supplied natural-form section is the only authored presentation choice in the bridge.
Its `returns` and `natural` laws are checked by NRRF768; no canonical UI choice is inferred from a
quotient alone. -/
structure InteractiveProjection (Meaning : Type u) where
  selector : NRRF768.NaturalFormSelector (flipFrame Meaning)

namespace InteractiveProjection

variable {Meaning : Type u}

/-- Render a state by selecting the relative presentation of its meaning. -/
def render (projection : InteractiveProjection Meaning) (state : RuntimeState Meaning) :
    View Meaning where
  perspective := state.perspective
  occurrence := projection.selector.select state.perspective state.meaning

/-- Rendering and decoding recover exactly the state's meaning. -/
@[simp] theorem decode_render (projection : InteractiveProjection Meaning)
    (state : RuntimeState Meaning) :
    (projection.render state).decode = state.meaning := by
  simpa [render, View.decode, flipFrame] using
    projection.selector.returns state.perspective state.meaning

/-- A runtime translation is the actual NRRF627 occurrence translation between the two rendered
perspectives, not merely equality of an ad hoc UI identifier. -/
def Translational (projection : InteractiveProjection Meaning)
    (source target : RuntimeState Meaning) : Prop :=
  (flipFrame Meaning).T source.perspective target.perspective
      (projection.render source).occurrence =
    (projection.render target).occurrence

/-- Decoded view equality is just equality of the semantic meanings carried by the states. -/
theorem viewEq_iff_meaning_eq (projection : InteractiveProjection Meaning)
    (source target : RuntimeState Meaning) :
    ViewEq (projection.render source) (projection.render target) ↔
      source.meaning = target.meaning := by
  simp [ViewEq]

/-- **Central runtime projection theorem.**  Two rendered views have one decoded semantic identity
if and only if the natural-form rendering of the first translates to the rendering of the second.
Raw views may still differ in perspective and pole. -/
theorem viewEq_iff_translational (projection : InteractiveProjection Meaning)
    (source target : RuntimeState Meaning) :
    ViewEq (projection.render source) (projection.render target) ↔
      projection.Translational source target := by
  constructor
  · intro hview
    have hmeaning : source.meaning = target.meaning :=
      (projection.viewEq_iff_meaning_eq source target).mp hview
    unfold Translational render
    simpa [flipFrame, hmeaning] using
      projection.selector.natural source.perspective target.perspective source.meaning
  · intro htranslation
    apply (projection.viewEq_iff_meaning_eq source target).mpr
    have hfirst := congrArg Prod.fst htranslation
    have hsource : (projection.render source).occurrence.1 = source.meaning :=
      projection.decode_render source
    have htarget : (projection.render target).occurrence.1 = target.meaning :=
      projection.decode_render target
    have hreturned :
        (projection.render source).occurrence.1 =
          (projection.render target).occurrence.1 := by
      simpa [Translational, flipFrame] using hfirst
    exact hsource.symm.trans (hreturned.trans htarget)

/-- With an explicit NRRF858 adapter, decoded view equality is exactly NRRF858 chart translation.
This theorem is the formal handoff point; conformance of an actual renderer remains a separate
runtime obligation. -/
theorem chartViewEq_iff_translational (projection : InteractiveProjection Meaning)
    (adapter : ConsciousMeaningAdapter Meaning) (source target : NRRF858.Chart)
    (sourcePerspective targetPerspective : Bool)
    (sourceHistory targetHistory : List (Intent Meaning)) :
    ViewEq
        (projection.render
          (RuntimeState.ofChart adapter sourcePerspective sourceHistory source))
        (projection.render
          (RuntimeState.ofChart adapter targetPerspective targetHistory target)) ↔
      NRRF858.Translational source target := by
  rw [projection.viewEq_iff_meaning_eq]
  exact adapter.encode_eq_iff_translational source target

end InteractiveProjection

/-! ## Append-only witnessed intent movement -/

/-- Prefix is extensional on the retained finite intent histories. -/
def HistoryPrefix {Meaning : Type u}
    (source target : RuntimeState Meaning) : Prop :=
  ∃ tail, target.history = source.history ++ tail

/-- One accepted movement carries the exact intent, its state-shape witness, the semantic boundary,
the translated-view equation, and the append-only history equation. -/
structure WitnessedStep {Meaning : Type u} (projection : InteractiveProjection Meaning)
    (source target : RuntimeState Meaning) where
  intent : Intent Meaning
  applies : intent.Applies source target
  meaning_boundary : source.meaning = target.meaning
  view_movement : projection.Translational source target
  history_append : target.history = source.history ++ [intent]

namespace WitnessedStep

variable {Meaning : Type u} {projection : InteractiveProjection Meaning}
  {source target : RuntimeState Meaning}

/-- Every witnessed movement retains the complete old history as an exact prefix. -/
theorem retains_prefix (step : WitnessedStep projection source target) :
    HistoryPrefix source target :=
  ⟨[step.intent], step.history_append⟩

/-- The movement cannot change the decoded semantic identity. -/
theorem decoded_eq (step : WitnessedStep projection source target) :
    (projection.render source).decode = (projection.render target).decode :=
  (projection.viewEq_iff_translational source target).mpr step.view_movement

end WitnessedStep

/-! ## Executable structural certificates -/

/-- A finite certificate names the exact source, target, and intent.  Authentication is kept out of
this data so that a Boolean structural check cannot be mistaken for external authentication. -/
structure Certificate (Meaning : Type u) where
  source : RuntimeState Meaning
  target : RuntimeState Meaning
  intent : Intent Meaning

namespace Certificate

/-- The proposition checked by the executable verifier. -/
def Valid {Meaning : Type u} (certificate : Certificate Meaning) : Prop :=
  certificate.intent.Applies certificate.source certificate.target ∧
    certificate.source.meaning = certificate.target.meaning ∧
    certificate.target.history =
      certificate.source.history ++ [certificate.intent]

instance {Meaning : Type u} [DecidableEq Meaning] (certificate : Certificate Meaning) :
    Decidable certificate.Valid := by
  unfold Valid Intent.Applies
  cases certificate.intent <;> infer_instance

/-- The executable structural verifier.  Its scope is finite equality and one append operation. -/
def verify {Meaning : Type u} [DecidableEq Meaning]
    (certificate : Certificate Meaning) : Bool :=
  decide certificate.Valid

/-- Executable acceptance is sound for the structural certificate proposition. -/
theorem verify_sound {Meaning : Type u} [DecidableEq Meaning]
    {certificate : Certificate Meaning} (accepted : verify certificate = true) :
    certificate.Valid :=
  of_decide_eq_true accepted

/-- The verifier is complete for this bounded structural proposition. -/
theorem verify_complete {Meaning : Type u} [DecidableEq Meaning]
    {certificate : Certificate Meaning} (valid : certificate.Valid) :
    verify certificate = true :=
  decide_eq_true valid

/-- A valid structural certificate constructs the full translated, append-only movement because
the natural projection theorem supplies the occurrence equation from the semantic boundary. -/
def Valid.toWitnessedStep {Meaning : Type u}
    {certificate : Certificate Meaning} (valid : certificate.Valid)
    (projection : InteractiveProjection Meaning) :
    WitnessedStep projection certificate.source certificate.target where
  intent := certificate.intent
  applies := valid.1
  meaning_boundary := valid.2.1
  view_movement :=
    (projection.viewEq_iff_translational certificate.source certificate.target).mp
      ((projection.viewEq_iff_meaning_eq certificate.source certificate.target).mpr valid.2.1)
  history_append := valid.2.2

/-- An accepted executable certificate therefore yields a witnessed movement. -/
def toWitnessedStep {Meaning : Type u} [DecidableEq Meaning]
    (certificate : Certificate Meaning) (projection : InteractiveProjection Meaning)
    (accepted : verify certificate = true) :
    WitnessedStep projection certificate.source certificate.target :=
  (verify_sound accepted).toWitnessedStep projection

end Certificate

/-! ## Authenticated external-effect admission -/

/-- An external effect is admitted only with both separately supplied authentication and an
accepted structural certificate.  `Authenticated` may be implemented by signatures, capability
checks, or another world-grounded protocol; this module does not choose or synthesize it. -/
structure ExternalEffectAdmission {Meaning : Type u} [DecidableEq Meaning]
    (projection : InteractiveProjection Meaning)
    (Authenticated : Certificate Meaning → Prop) (Effect : Type e) where
  certificate : Certificate Meaning
  effect : Effect
  authenticated : Authenticated certificate
  verified : certificate.verify = true

namespace ExternalEffectAdmission

variable {Meaning : Type u} [DecidableEq Meaning]
  {projection : InteractiveProjection Meaning}
  {Authenticated : Certificate Meaning → Prop} {Effect : Type e}

/-- Admission exposes the exact authenticated fact; structural closure cannot replace it. -/
theorem requires_authentication
    (admission : ExternalEffectAdmission projection Authenticated Effect) :
    Authenticated admission.certificate :=
  admission.authenticated

/-- Admission also yields the exact translated, append-only runtime movement. -/
def witnessedStep
    (admission : ExternalEffectAdmission projection Authenticated Effect) :
    WitnessedStep projection admission.certificate.source admission.certificate.target :=
  admission.certificate.toWitnessedStep projection admission.verified

/-- Consequently every admitted effect retains the prior interaction history. -/
theorem retains_prefix
    (admission : ExternalEffectAdmission projection Authenticated Effect) :
    HistoryPrefix admission.certificate.source admission.certificate.target :=
  admission.witnessedStep.retains_prefix

end ExternalEffectAdmission

/-! ## Satisfiable, non-vacuous instance -/

/-- One authored seed supplies a natural selector; translation from `false` to `true` reverses its
pole while retaining the Boolean meaning. -/
def demoProjection : InteractiveProjection Bool where
  selector :=
    (NRRF768.RelativeFormSeed.constant
      (A := flipFrame Bool) false Pole.zero).selectorOfSeed

def demoSource : RuntimeState Bool where
  perspective := false
  meaning := true
  history := []

def demoIntent : Intent Bool := .reframe true

def demoTarget : RuntimeState Bool where
  perspective := true
  meaning := true
  history := [demoIntent]

def demoCertificate : Certificate Bool where
  source := demoSource
  target := demoTarget
  intent := demoIntent

theorem demoCertificate_verified : demoCertificate.verify = true := by
  decide

/-- Demo authentication is intentionally explicit and scoped to this one certificate. -/
def DemoAuthenticated (certificate : Certificate Bool) : Prop :=
  certificate = demoCertificate

inductive DemoEffect where
  | displayTranslatedView

def demoAdmission :
    ExternalEffectAdmission demoProjection DemoAuthenticated DemoEffect where
  certificate := demoCertificate
  effect := .displayTranslatedView
  authenticated := rfl
  verified := demoCertificate_verified

/-- The bridge is non-vacuous: it has distinct raw perspective views, equal decoded meaning, an
actual occurrence translation, an append-only witnessed transition, and an authenticated admitted
effect. -/
theorem demo_nonvacuous :
    demoProjection.render demoSource ≠ demoProjection.render demoTarget ∧
    ViewEq (demoProjection.render demoSource) (demoProjection.render demoTarget) ∧
    demoProjection.Translational demoSource demoTarget ∧
    HistoryPrefix demoSource demoTarget ∧
    Nonempty (ExternalEffectAdmission demoProjection DemoAuthenticated DemoEffect) := by
  have rawViewsDiffer :
      demoProjection.render demoSource ≠ demoProjection.render demoTarget := by
    intro sameView
    have perspectiveEq := congrArg View.perspective sameView
    simp [InteractiveProjection.render, demoSource, demoTarget] at perspectiveEq
  have viewEq :
      ViewEq (demoProjection.render demoSource) (demoProjection.render demoTarget) := by
    exact (demoProjection.viewEq_iff_meaning_eq demoSource demoTarget).mpr rfl
  have translated : demoProjection.Translational demoSource demoTarget :=
    (demoProjection.viewEq_iff_translational demoSource demoTarget).mp viewEq
  exact ⟨rawViewsDiffer, viewEq, translated,
    demoAdmission.retains_prefix, ⟨demoAdmission⟩⟩

#print axioms InteractiveProjection.viewEq_iff_translational
#print axioms InteractiveProjection.chartViewEq_iff_translational
#print axioms Certificate.verify_sound
#print axioms Certificate.verify_complete
#print axioms ExternalEffectAdmission.retains_prefix
#print axioms demo_nonvacuous

end NRRF859
