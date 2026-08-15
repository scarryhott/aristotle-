import NRRF627IndependentReturnBridge

/-!
# NRRF631 runtime bridge — frame-conditional openness

This module states the order enforced by the executable runtime.  A reference frame is first the
equivalence relation it admits.  A translation is then accepted only as an axiom-geometry
equivalence preserving and reflecting that relation.  Resolution and openness are defined only
afterward, as relations between a frame and a question.

The module is deliberately named as a runtime bridge.  It does not claim to replace the more
general `NRRF631FrameConditionalOpennessRelationalEquality` development; that source is not part of
this repository.  It machine-checks the exact interface used here from the existing NRRF627
`TransFrame`, without adding axioms.
-/

namespace NRRF631Runtime

open NRRF627
open NRRF627IndependentReturn

universe u v w z

/-! ## Equality is the reference frame -/

/-- A runtime reference frame contains no verdict: it is exactly an admitted equality. -/
structure ReferenceFrame (X : Type u) where
  equality : Setoid X

/-- A question is resolved only relative to a frame: it cannot separate frame-equal occurrences. -/
def ResolvedIn {X : Type u} {Ω : Type v}
    (F : ReferenceFrame X) (Q : X → Ω) : Prop :=
  ∀ ⦃x y⦄, F.equality.r x y → Q x = Q y

/-- Openness is the two-place negation of frame-relative resolution. -/
def OpenIn {X : Type u} {Ω : Type v}
    (F : ReferenceFrame X) (Q : X → Ω) : Prop :=
  ¬ ResolvedIn F Q

/-- The closure frame of a return map admits equality exactly when returns agree. -/
def closureFrame {X : Type u} {B : Type v} (W : X → B) : ReferenceFrame X where
  equality := {
    r := CEq W
    iseqv := ⟨
      fun _ => rfl,
      fun h => h.symm,
      fun hxy hyz => hxy.trans hyz
    ⟩
  }

/-- The discrete control frame admits only literal equality. -/
def discreteFrame (X : Type u) : ReferenceFrame X where
  equality := {
    r := Eq
    iseqv := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  }

/-- Factorization through the quotient is the operational meaning of resolution. -/
def FactorsThroughQuotient {X : Type u} {Ω : Type v}
    (F : ReferenceFrame X) (Q : X → Ω) : Prop :=
  ∃ q : Quotient F.equality → Ω, ∀ x, q (Quotient.mk F.equality x) = Q x

theorem resolvedIn_iff_factors {X : Type u} {Ω : Type v}
    (F : ReferenceFrame X) (Q : X → Ω) :
    ResolvedIn F Q ↔ FactorsThroughQuotient F Q := by
  constructor
  · intro hQ
    refine ⟨Quotient.lift Q ?_, ?_⟩
    · intro x y hxy
      exact hQ hxy
    · intro x
      rfl
  · rintro ⟨q, hq⟩ x y hxy
    rw [← hq x, ← hq y]
    exact congrArg q (@Quotient.sound X F.equality x y hxy)

theorem factor_through_quotient_unique {X : Type u} {Ω : Type v}
    (F : ReferenceFrame X) (Q : X → Ω) (hQ : ResolvedIn F Q) :
    ∃! q : Quotient F.equality → Ω, ∀ x, q (Quotient.mk F.equality x) = Q x := by
  let q : Quotient F.equality → Ω := Quotient.lift Q (fun _ _ h => hQ h)
  refine ⟨q, fun _ => rfl, ?_⟩
  intro g hg
  funext c
  refine Quotient.inductionOn c ?_
  intro x
  simpa [q] using hg x

theorem closure_return_resolved {X : Type u} {B : Type v} (W : X → B) :
    ResolvedIn (closureFrame W) W := by
  intro x y hxy
  exact hxy

theorem discrete_resolves_every_question {X : Type u} {Ω : Type v} (Q : X → Ω) :
    ResolvedIn (discreteFrame X) Q := by
  intro x y hxy
  exact congrArg Q hxy

/-! ## Axiom-geometry equivalence precedes translation consequences -/

/-- A comparison of frames preserves and reflects exactly the admitted equality. -/
structure GeomEquiv {X : Type u} {Y : Type v}
    (F : ReferenceFrame X) (G : ReferenceFrame Y) where
  occurrenceEquiv : X ≃ Y
  equality_iff : ∀ x y,
    G.equality.r (occurrenceEquiv x) (occurrenceEquiv y) ↔ F.equality.r x y

namespace GeomEquiv

def refl {X : Type u} (F : ReferenceFrame X) : GeomEquiv F F where
  occurrenceEquiv := Equiv.refl X
  equality_iff := by simp

def symm {X : Type u} {Y : Type v} {F : ReferenceFrame X} {G : ReferenceFrame Y}
    (e : GeomEquiv F G) : GeomEquiv G F where
  occurrenceEquiv := e.occurrenceEquiv.symm
  equality_iff := by
    intro x y
    simpa using (e.equality_iff (e.occurrenceEquiv.symm x) (e.occurrenceEquiv.symm y)).symm

def trans {X : Type u} {Y : Type v} {Z : Type w}
    {F : ReferenceFrame X} {G : ReferenceFrame Y} {H : ReferenceFrame Z}
    (e : GeomEquiv F G) (f : GeomEquiv G H) : GeomEquiv F H where
  occurrenceEquiv := e.occurrenceEquiv.trans f.occurrenceEquiv
  equality_iff := by
    intro x y
    exact (f.equality_iff _ _).trans (e.equality_iff x y)

/-- Transport a question without choosing either frame as the origin. -/
def transportQuestion {X : Type u} {Y : Type v} {Ω : Type z}
    {F : ReferenceFrame X} {G : ReferenceFrame Y}
    (e : GeomEquiv F G) (Q : X → Ω) : Y → Ω :=
  fun y => Q (e.occurrenceEquiv.symm y)

theorem resolvedIn_transport {X : Type u} {Y : Type v} {Ω : Type z}
    {F : ReferenceFrame X} {G : ReferenceFrame Y}
    (e : GeomEquiv F G) (Q : X → Ω) :
    ResolvedIn F Q ↔ ResolvedIn G (transportQuestion e Q) := by
  constructor
  · intro hQ x y hxy
    have hsource : F.equality.r
        (e.occurrenceEquiv.symm x) (e.occurrenceEquiv.symm y) := by
      apply (e.equality_iff _ _).mp
      simpa using hxy
    exact hQ hsource
  · intro hQ x y hxy
    have htarget : G.equality.r (e.occurrenceEquiv x) (e.occurrenceEquiv y) :=
      (e.equality_iff x y).mpr hxy
    simpa [transportQuestion] using hQ htarget

theorem openIn_transport {X : Type u} {Y : Type v} {Ω : Type z}
    {F : ReferenceFrame X} {G : ReferenceFrame Y}
    (e : GeomEquiv F G) (Q : X → Ω) :
    OpenIn F Q ↔ OpenIn G (transportQuestion e Q) := by
  exact not_congr (resolvedIn_transport e Q)

end GeomEquiv

/-! ## The existing translational frame supplies every runtime `GeomEquiv` -/

def RelativeEqualityForm.geomEquiv
    {Y₀ : Type v} {Y₁ : Type w} {B₀ : Type z} {B₁ : Type u}
    {W₀ : Y₀ → B₀} {W₁ : Y₁ → B₁}
    (e : RelativeEqualityForm Y₀ Y₁ B₀ B₁ W₀ W₁) :
    GeomEquiv (closureFrame W₀) (closureFrame W₁) where
  occurrenceEquiv := e.T
  equality_iff := NRRF627IndependentReturn.relativeEquality_iff e

/-- Translation from `TransFrame` is an axiom-geometry equivalence, with no new axiom. -/
def TransFrame.transGeomEquiv
    {L : Type u} {B : L → Type v} {Y : L → Type w}
    (A : TransFrame L B Y) (ℓ m : L) :
    GeomEquiv (closureFrame (A.W ℓ)) (closureFrame (A.W m)) :=
  NRRF631Runtime.RelativeEqualityForm.geomEquiv
    (NRRF627IndependentReturn.TransFrame.relativeEqualityForm A ℓ m)

theorem TransFrame.resolution_language_independent
    {L : Type u} {B : L → Type v} {Y : L → Type w}
    (A : TransFrame L B Y) {Ω : Type z} (ℓ m : L) (Q : Y ℓ → Ω) :
    ResolvedIn (closureFrame (A.W ℓ)) Q ↔
      ResolvedIn (closureFrame (A.W m))
        ((NRRF631Runtime.TransFrame.transGeomEquiv A ℓ m).transportQuestion Q) :=
  GeomEquiv.resolvedIn_transport
    (NRRF631Runtime.TransFrame.transGeomEquiv A ℓ m) Q

theorem TransFrame.openness_language_independent
    {L : Type u} {B : L → Type v} {Y : L → Type w}
    (A : TransFrame L B Y) {Ω : Type z} (ℓ m : L) (Q : Y ℓ → Ω) :
    OpenIn (closureFrame (A.W ℓ)) Q ↔
      OpenIn (closureFrame (A.W m))
        ((NRRF631Runtime.TransFrame.transGeomEquiv A ℓ m).transportQuestion Q) :=
  GeomEquiv.openIn_transport
    (NRRF631Runtime.TransFrame.transGeomEquiv A ℓ m) Q

theorem TransFrame.return_question_resolved
    {L : Type u} {B : L → Type v} {Y : L → Type w}
    (A : TransFrame L B Y) (ℓ : L) :
    ResolvedIn (closureFrame (A.W ℓ)) (A.W ℓ) :=
  closure_return_resolved (A.W ℓ)

/-! ## The finite runtime's concrete conditional-openness witness -/

def productReturn {B : Type u} : Pole × B → B := Prod.snd

def literalPole {B : Type u} : Pole × B → Pole := Prod.fst

theorem literalPole_open_in_closure {B : Type u} [Nonempty B] :
    OpenIn (closureFrame (productReturn (B := B))) (literalPole (B := B)) := by
  intro hresolved
  let b : B := Classical.choice inferInstance
  have heq : (closureFrame (productReturn (B := B))).equality.r
      (Pole.zero, b) (Pole.inf, b) := rfl
  have hpole : Pole.zero = Pole.inf := hresolved heq
  exact Pole.other_ne Pole.zero (by simpa [Pole.other] using hpole.symm)

theorem literalPole_resolved_in_discrete {B : Type u} :
    ResolvedIn (discreteFrame (Pole × B)) (literalPole (B := B)) :=
  discrete_resolves_every_question _

/-- Bundle the runtime order in one proposition: equality, equivalence, then resolution/openness. -/
theorem runtime_begins_in_axiom_geometry
    {L : Type u} {B : L → Type v} {Y : L → Type w}
    (A : TransFrame L B Y) {Ω : Type z} (ℓ m : L) (Q : Y ℓ → Ω) :
    (ResolvedIn (closureFrame (A.W ℓ)) Q ↔
      ResolvedIn (closureFrame (A.W m))
        ((NRRF631Runtime.TransFrame.transGeomEquiv A ℓ m).transportQuestion Q)) ∧
    (OpenIn (closureFrame (A.W ℓ)) Q ↔
      OpenIn (closureFrame (A.W m))
        ((NRRF631Runtime.TransFrame.transGeomEquiv A ℓ m).transportQuestion Q)) := by
  exact ⟨NRRF631Runtime.TransFrame.resolution_language_independent A ℓ m Q,
    NRRF631Runtime.TransFrame.openness_language_independent A ℓ m Q⟩

end NRRF631Runtime

#print axioms NRRF631Runtime.resolvedIn_iff_factors
#print axioms NRRF631Runtime.factor_through_quotient_unique
#print axioms NRRF631Runtime.TransFrame.transGeomEquiv
#print axioms NRRF631Runtime.TransFrame.openness_language_independent
#print axioms NRRF631Runtime.literalPole_open_in_closure
#print axioms NRRF631Runtime.runtime_begins_in_axiom_geometry
