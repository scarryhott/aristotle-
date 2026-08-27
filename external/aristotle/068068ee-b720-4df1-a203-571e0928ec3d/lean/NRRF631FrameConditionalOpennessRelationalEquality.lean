import Mathlib
import NRRF630TranslationalAxiometryExistenceNaturality

/-!
# NRRF631 — Openness is explicitly conditional on the frame, and resolves in forms of equality

The claim formalised here is:

> the openness of a question has always been *explicitly conditional* — conditional under the
> axiom-geometry equivalence of the frame (the reference frame).  Such questions do not resolve in
> static definitions; they resolve in *forms of equality* and in *relational definition*.

Everything below is a theorem.  A **reference frame** on a type of occurrences is nothing but the
form of equality it admits — a setoid, its *axiom geometry*.  A **question** is a map from
occurrences to verdicts.  A frame **resolves** a question when the question cannot separate
occurrences the frame equates, and the question is **open** in that frame otherwise.

## Contents

* **§1 Resolution is a form of equality.**  `resolvedIn_iff_factors`: a frame resolves a question
  exactly when the question factors through the frame's quotient; `resolvedEquiv`: the resolved
  questions of a frame *are* the functions on its quotient.  `resolution_depends_only_on_equality`
  and `resolvedIn_mono`: only the admitted equality matters, and refining it can only resolve more.
* **§2 Relational definitions resolve; static definitions need not.**  `relQuestion_resolved`,
  `resolved_of_relational` — a question defined by relation to given data, through the frame's own
  equality, is resolved in that frame.  `resolved_in_every_frame_iff_constant`: a question resolved
  in *every* frame is constant, so no static (frame-independent) definition carries content that is
  resolved unconditionally.  `openness_is_frame_relative`: one and the same static definition is
  open in one frame and resolved in another.
* **§3 Conditional under axiom-geometry equivalence.**  `GeomEquiv`, an equivalence of reference
  frames; `resolvedIn_transport`, `openIn_transport`: equivalent frames agree, after transport, on
  which questions are open.  So openness is an invariant of the equivalence class of the frame, and
  is well-posed only relative to it.  `GeomEquiv.refl/symm/trans`: the frames form a groupoid.
* **§4 The frame is exactly its forms of equality.**  `equality_recovered_from_resolved_questions`:
  two frames resolving the same questions admit the same equality — nothing static is left over.
* **§5 The closure translational axiometry as reference frames.**  For a `NRRF627.TransFrame`, the
  closure equality of each language is a reference frame; every translation is an axiom-geometry
  equivalence (`transGeomEquiv`), hence `openness_language_independent`: openness is not a property
  of a language, it is a property of the equivalence class.  `resolvedIdentEquiv`: the questions
  resolved in a language are exactly the functions of the returned relational identity.
  `return_question_resolved` (a relational definition, resolved everywhere and translating
  correctly) versus `pole_question_open` (a static definition, open in the closure frame while
  resolved in the discrete frame).
* **§6 The bundle** `openness_is_frame_conditional_and_relational`.
-/

namespace NRRF631

open Function NRRF627

universe u v w

/-! ## §1  Reference frames, questions, resolution -/

section Abstract

variable {X Z : Type*} {Ω : Type*}

/-- The discrete reference frame: only literal identity is admitted as equality. -/
def discreteFrame (X : Type*) : Setoid X := ⟨Eq, eq_equivalence⟩

/-- The indiscrete reference frame: every occurrence is admitted as equal to every other. -/
def indiscreteFrame (X : Type*) : Setoid X :=
  ⟨fun _ _ => True, ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩⟩

/-- A frame **resolves** a question when the question cannot separate occurrences that the frame's
form of equality identifies: the verdict is determined by the admitted equality, not by the
occurrence. -/
def ResolvedIn (s : Setoid X) (Q : X → Ω) : Prop := ∀ x y, s.r x y → Q x = Q y

/-- A question is **open** in a frame when that frame does not resolve it.  Openness is a relation
between a question and a reference frame, never a property of the question alone. -/
def OpenIn (s : Setoid X) (Q : X → Ω) : Prop := ¬ ResolvedIn s Q

/-- **Resolution is a form of equality.**  A frame resolves a question exactly when the question
factors through the quotient by the frame's equality: to resolve is to be a function of the
admitted equality class, and of nothing else. -/
theorem resolvedIn_iff_factors (s : Setoid X) (Q : X → Ω) :
    ResolvedIn s Q ↔ ∃ q : Quotient s → Ω, ∀ x, Q x = q (Quotient.mk s x) := by
  constructor
  · intro h
    exact ⟨Quotient.lift Q fun a b hab => h a b hab, fun _ => rfl⟩
  · rintro ⟨q, hq⟩ x y hxy
    rw [hq, hq]
    exact congrArg q (Quotient.sound hxy)

/-- The resolved questions of a frame **are** the functions on its quotient. -/
def resolvedEquiv (s : Setoid X) : {Q : X → Ω // ResolvedIn s Q} ≃ (Quotient s → Ω) where
  toFun Q := Quotient.lift Q.1 fun a b hab => Q.2 a b hab
  invFun q := ⟨fun x => q (Quotient.mk s x), fun _ _ h => congrArg q (Quotient.sound h)⟩
  left_inv Q := Subtype.ext rfl
  right_inv q := funext fun t => by induction t using Quotient.ind; rfl

/-- Resolution depends on the frame only through the equality it admits: two frames with the same
form of equality resolve exactly the same questions. -/
theorem resolution_depends_only_on_equality {s t : Setoid X} (h : ∀ x y, s.r x y ↔ t.r x y)
    (Q : X → Ω) : ResolvedIn s Q ↔ ResolvedIn t Q :=
  ⟨fun hs x y hxy => hs x y ((h x y).2 hxy), fun ht x y hxy => ht x y ((h x y).1 hxy)⟩

/-- Refining the admitted equality can only resolve more questions. -/
theorem resolvedIn_mono {s t : Setoid X} (h : ∀ x y, t.r x y → s.r x y) {Q : X → Ω}
    (hQ : ResolvedIn s Q) : ResolvedIn t Q := fun x y hxy => hQ x y (h x y hxy)

/-- Every question is resolved in the discrete frame — which is why the discrete frame decides
nothing about the *content* of a question. -/
theorem resolvedIn_discrete (Q : X → Ω) : ResolvedIn (discreteFrame X) Q := by
  rintro x y (rfl : x = y); rfl

/-- The indiscrete frame resolves exactly the constant questions. -/
theorem resolvedIn_indiscrete_iff (Q : X → Ω) :
    ResolvedIn (indiscreteFrame X) Q ↔ ∀ x y, Q x = Q y :=
  ⟨fun h x y => h x y trivial, fun h x y _ => h x y⟩

/-! ## §2  Relational definitions resolve; static definitions need not -/

/-- A question **defined relationally**: "is this occurrence equal, in the frame's own sense, to the
reference occurrence `a`?" -/
def relQuestion (s : Setoid X) (a : X) : X → Prop := fun x => s.r a x

/-- **A relational definition is resolved by the frame it is stated in.**  A question defined by
relation to given data, through the frame's own form of equality, is never open in that frame. -/
theorem relQuestion_resolved (s : Setoid X) (a : X) : ResolvedIn s (relQuestion s a) := by
  intro x y hxy
  exact propext ⟨fun hax => s.trans hax hxy, fun hay => s.trans hay (s.symm hxy)⟩

/-- More generally, a question pulled back along a map that respects the two frames' equalities is
resolved as soon as the target question is: relational definition transports resolution. -/
theorem resolved_of_relational {s : Setoid X} {t : Setoid Z} (f : X → Z)
    (hf : ∀ x y, s.r x y → t.r (f x) (f y)) {Q : Z → Ω} (hQ : ResolvedIn t Q) :
    ResolvedIn s (Q ∘ f) := fun x y hxy => hQ (f x) (f y) (hf x y hxy)

/-- **No static definition is resolved unconditionally with content.**  A question resolved in
*every* reference frame is constant: an unconditional verdict is an empty verdict.  Content is
resolved only relative to a frame. -/
theorem resolved_in_every_frame_iff_constant (Q : X → Ω) :
    (∀ s : Setoid X, ResolvedIn s Q) ↔ ∀ x y, Q x = Q y :=
  ⟨fun h => (resolvedIn_indiscrete_iff Q).1 (h _), fun h _ x y _ => h x y⟩

/-- Dually: a question is open in some frame exactly when it is non-constant, i.e. exactly when it
has content at all. -/
theorem openIn_some_frame_iff_nonconstant (Q : X → Ω) :
    (∃ s : Setoid X, OpenIn s Q) ↔ ¬ ∀ x y, Q x = Q y := by
  constructor
  · rintro ⟨s, hs⟩ hconst
    exact hs fun x y _ => hconst x y
  · intro h
    exact ⟨indiscreteFrame X, fun hr => h ((resolvedIn_indiscrete_iff Q).1 hr)⟩

/-- **Openness is frame-relative.**  One and the same static definition — here the question
"is this bit `true`?" — is open in one reference frame and resolved in another.  Openness is
therefore never a property of the question by itself. -/
theorem openness_is_frame_relative :
    ∃ (X : Type) (Q : X → Prop) (s t : Setoid X), OpenIn s Q ∧ ResolvedIn t Q := by
  refine ⟨Bool, fun b => b = true, indiscreteFrame Bool, discreteFrame Bool, ?_,
    resolvedIn_discrete _⟩
  intro h
  have := h true false trivial
  simp at this

/-! ## §3  Openness is conditional under axiom-geometry equivalence of the frames -/

/-- An **axiom-geometry equivalence** of reference frames: a comparison of the occurrences that
preserves *and reflects* the admitted forms of equality.  Two frames related in this way have the
same geometry of equalities, however differently they are presented. -/
structure GeomEquiv {X Z : Type*} (s : Setoid X) (t : Setoid Z) where
  /-- the comparison of occurrences -/
  toEquiv : X ≃ Z
  /-- the admitted equality is preserved and reflected -/
  rel : ∀ x y, s.r x y ↔ t.r (toEquiv x) (toEquiv y)

namespace GeomEquiv

/-- Each frame is equivalent to itself. -/
def refl (s : Setoid X) : GeomEquiv s s := ⟨Equiv.refl X, fun _ _ => Iff.rfl⟩

/-- Axiom-geometry equivalence is symmetric. -/
def symm {s : Setoid X} {t : Setoid Z} (e : GeomEquiv s t) : GeomEquiv t s where
  toEquiv := e.toEquiv.symm
  rel z w := by
    constructor
    · intro h
      exact (e.rel _ _).2 (by simpa using h)
    · intro h
      simpa using (e.rel _ _).1 h

/-- Axiom-geometry equivalence is transitive. -/
def trans {W : Type*} {s : Setoid X} {t : Setoid Z} {r : Setoid W}
    (e : GeomEquiv s t) (f : GeomEquiv t r) : GeomEquiv s r where
  toEquiv := e.toEquiv.trans f.toEquiv
  rel x y := (e.rel x y).trans (f.rel _ _)

/-- Transport of a question along an equivalence of reference frames. -/
def transport {s : Setoid X} {t : Setoid Z} (e : GeomEquiv s t) (Q : X → Ω) : Z → Ω :=
  fun z => Q (e.toEquiv.symm z)

end GeomEquiv

/-- **Resolution is conditional exactly on the axiom-geometry equivalence class of the frame.**
Equivalent reference frames resolve corresponding questions. -/
theorem resolvedIn_transport {s : Setoid X} {t : Setoid Z} (e : GeomEquiv s t) (Q : X → Ω) :
    ResolvedIn s Q ↔ ResolvedIn t (e.transport Q) := by
  constructor
  · intro h z w hzw
    refine h _ _ ((e.rel _ _).2 ?_)
    simpa using hzw
  · intro h x y hxy
    have := h (e.toEquiv x) (e.toEquiv y) ((e.rel x y).1 hxy)
    simpa [GeomEquiv.transport] using this

/-- The same statement for openness: a question open in a frame is open in every axiom-geometry
equivalent frame, and only there is the comparison meaningful. -/
theorem openIn_transport {s : Setoid X} {t : Setoid Z} (e : GeomEquiv s t) (Q : X → Ω) :
    OpenIn s Q ↔ OpenIn t (e.transport Q) :=
  not_congr (resolvedIn_transport e Q)

/-! ## §4  A frame is exactly its forms of equality -/

/-- **Nothing static is left over.**  If two reference frames resolve exactly the same questions,
they admit exactly the same equality.  The frame is recoverable from — indeed is nothing but — its
forms of equality. -/
theorem equality_recovered_from_resolved_questions {s t : Setoid X}
    (h : ∀ Q : X → Prop, ResolvedIn s Q ↔ ResolvedIn t Q) (x y : X) : s.r x y ↔ t.r x y := by
  constructor
  · intro hxy
    have hres : ResolvedIn t (relQuestion t x) := relQuestion_resolved t x
    have heq : (relQuestion t x) x = (relQuestion t x) y := ((h _).2 hres) x y hxy
    exact cast heq (t.refl x)
  · intro hxy
    have hres : ResolvedIn s (relQuestion s x) := relQuestion_resolved s x
    have heq : (relQuestion s x) x = (relQuestion s x) y := ((h _).1 hres) x y hxy
    exact cast heq (s.refl x)

end Abstract

/-! ## §5  The closure translational axiometry, read as reference frames -/


variable {L : Type u} {B : L → Type v} {Y : L → Type w} (A : TransFrame L B Y)

/-- The reference frame of a language: its admitted equality is closure equality, "returns the same
relational identity". -/
def closureFrame (ℓ : L) : Setoid (Y ℓ) := A.ceqSetoid ℓ

/-- **Every translation is an axiom-geometry equivalence of reference frames.**  The comparison of
two languages preserves and reflects closure equality, so the languages are one and the same
reference frame up to equivalence — no language is the origin. -/
def transGeomEquiv (ℓ m : L) : GeomEquiv (closureFrame A ℓ) (closureFrame A m) where
  toEquiv := A.transEquiv ℓ m
  rel u v := A.ceq_iff ℓ m u v

/-- **Openness is a property of the equivalence class, not of the language.**  A question is open in
one language exactly when its translate is open in any other. -/
theorem openness_language_independent {Ω : Type*} (ℓ m : L) (Q : Y ℓ → Ω) :
    OpenIn (closureFrame A ℓ) Q ↔ OpenIn (closureFrame A m) (fun u => Q (A.T m ℓ u)) :=
  openIn_transport (transGeomEquiv A ℓ m) Q

/-- Likewise for resolution. -/
theorem resolution_language_independent {Ω : Type*} (ℓ m : L) (Q : Y ℓ → Ω) :
    ResolvedIn (closureFrame A ℓ) Q ↔ ResolvedIn (closureFrame A m) (fun u => Q (A.T m ℓ u)) :=
  resolvedIn_transport (transGeomEquiv A ℓ m) Q

/-- A question is resolved in a language exactly when it is a function of the relational identity
returned: resolution happens in the return, i.e. in the form of equality. -/
theorem resolvedIn_closureFrame_iff {Ω : Type*} (ℓ : L) (Q : Y ℓ → Ω) :
    ResolvedIn (closureFrame A ℓ) Q ↔ ∃ q : B ℓ → Ω, ∀ u, Q u = q (A.W ℓ u) := by
  constructor
  · intro h
    refine ⟨fun b => Q (A.E ℓ Pole.zero b), fun u => ?_⟩
    exact h u (A.E ℓ Pole.zero (A.W ℓ u)) (show A.W ℓ u = _ by rw [A.recov])
  · rintro ⟨q, hq⟩ u v huv
    rw [hq, hq, show A.W ℓ u = A.W ℓ v from huv]

/-- The questions resolved in a language **are** the functions of the relational identity. -/
def resolvedIdentEquiv {Ω : Type*} (ℓ : L) :
    {Q : Y ℓ → Ω // ResolvedIn (closureFrame A ℓ) Q} ≃ (B ℓ → Ω) where
  toFun Q := fun b => Q.1 (A.E ℓ Pole.zero b)
  invFun q := ⟨fun u => q (A.W ℓ u), by
    intro u v huv
    exact congrArg q (show A.W ℓ u = A.W ℓ v from huv)⟩
  left_inv Q := by
    refine Subtype.ext (funext fun u => ?_)
    exact (Q.2 u (A.E ℓ Pole.zero (A.W ℓ u)) (show A.W ℓ u = _ by rw [A.recov])).symm
  right_inv q := funext fun b => by simp [A.recov]

/-- **A relational definition.**  "Does this occurrence return the identity `b`?" is resolved in
every language's reference frame. -/
theorem return_question_resolved (ℓ : L) (b : B ℓ) :
    ResolvedIn (closureFrame A ℓ) (fun u => A.W ℓ u = b) := by
  intro u v huv
  show (A.W ℓ u = b) = (A.W ℓ v = b)
  rw [show A.W ℓ u = A.W ℓ v from huv]

/-- And it translates as a relational definition should: asked in another language, it is the same
question about the translated identity. -/
theorem return_question_translate (ℓ m : L) (b : B ℓ) (u : Y ℓ) :
    (A.W m (A.T ℓ m u) = A.phi ℓ m b) ↔ (A.W ℓ u = b) := by
  rw [A.T_ret]
  exact ⟨fun h => A.phi_injective ℓ m h, fun h => by rw [h]⟩

/-- **A static definition.**  "Is this occurrence literally the zero-presentation of `b`?" is open
in the closure frame of a separated language: it distinguishes occurrences the frame equates.  It
is nevertheless resolved in the discrete frame — the openness is conditional on the frame, not on
the question. -/
theorem pole_question_open (hsep : A.Separated) (ℓ : L) (b : B ℓ) :
    OpenIn (closureFrame A ℓ) (fun u => u = A.E ℓ Pole.zero b) := by
  intro h
  have hceq : (closureFrame A ℓ).r (A.E ℓ Pole.zero b) (A.E ℓ Pole.inf b) :=
    A.poles_closure_equal ℓ Pole.zero Pole.inf b
  have h' : (A.E ℓ Pole.zero b = A.E ℓ Pole.zero b) = (A.E ℓ Pole.inf b = A.E ℓ Pole.zero b) :=
    h _ _ hceq
  exact hsep ℓ b (cast h' rfl).symm

/-- The same static definition is resolved in the discrete frame. -/
theorem pole_question_resolved_discrete (ℓ : L) (b : B ℓ) :
    ResolvedIn (discreteFrame (Y ℓ)) (fun u => u = A.E ℓ Pole.zero b) :=
  resolvedIn_discrete _

/-! ## §6  The bundle -/

/-- **Openness is explicitly conditional on the frame, and what resolves it is a form of equality,
not a static definition.**

1. Resolution in a reference frame is exactly factorisation through the frame's form of equality.
2. A question resolved in every frame is constant: unconditional resolution has no content.
3. Every translation of the closure translational axiometry is an axiom-geometry equivalence, and
   openness is invariant under it: openness is a property of the equivalence class of frames.
4. Relationally defined questions — "does this occurrence return this identity?" — are resolved in
   every language, and translate correctly.
5. A statically defined question — "is this occurrence literally that presentation?" — is open in
   the closure frame of a separated language while resolved in the discrete frame. -/
theorem openness_is_frame_conditional_and_relational {Ω : Type*} (hsep : A.Separated) (ℓ m : L)
    (b : B ℓ) :
    (∀ Q : Y ℓ → Ω, ResolvedIn (closureFrame A ℓ) Q ↔ ∃ q : B ℓ → Ω, ∀ u, Q u = q (A.W ℓ u)) ∧
    (∀ Q : Y ℓ → Ω, (∀ s : Setoid (Y ℓ), ResolvedIn s Q) ↔ ∀ u v, Q u = Q v) ∧
    (∀ Q : Y ℓ → Ω,
        OpenIn (closureFrame A ℓ) Q ↔ OpenIn (closureFrame A m) (fun u => Q (A.T m ℓ u))) ∧
    ResolvedIn (closureFrame A ℓ) (fun u => A.W ℓ u = b) ∧
    (∀ u : Y ℓ, (A.W m (A.T ℓ m u) = A.phi ℓ m b) ↔ (A.W ℓ u = b)) ∧
    OpenIn (closureFrame A ℓ) (fun u => u = A.E ℓ Pole.zero b) ∧
    ResolvedIn (discreteFrame (Y ℓ)) (fun u => u = A.E ℓ Pole.zero b) :=
  ⟨resolvedIn_closureFrame_iff A ℓ, fun Q => resolved_in_every_frame_iff_constant Q,
    fun Q => openness_language_independent A ℓ m Q, return_question_resolved A ℓ b,
    return_question_translate A ℓ m b, pole_question_open A hsep ℓ b,
    pole_question_resolved_discrete A ℓ b⟩


/-- **The openness is realised, not hypothetical.**  In the concrete separated model
`NRRF627.witnessFrame`, the static question "is this occurrence literally the zero-presentation?"
is genuinely open in the closure reference frame. -/
theorem closure_openness_realised :
    OpenIn (closureFrame NRRF627.witnessFrame ())
      (fun u => u = NRRF627.witnessFrame.E () Pole.zero ()) :=
  pole_question_open _ NRRF627.witnessFrame_separated () ()

end NRRF631

#print axioms NRRF631.resolvedIn_iff_factors
#print axioms NRRF631.resolvedEquiv
#print axioms NRRF631.relQuestion_resolved
#print axioms NRRF631.resolved_in_every_frame_iff_constant
#print axioms NRRF631.openness_is_frame_relative
#print axioms NRRF631.resolvedIn_transport
#print axioms NRRF631.equality_recovered_from_resolved_questions
#print axioms NRRF631.openness_language_independent
#print axioms NRRF631.resolvedIdentEquiv
#print axioms NRRF631.pole_question_open
#print axioms NRRF631.closure_openness_realised
#print axioms NRRF631.openness_is_frame_conditional_and_relational
