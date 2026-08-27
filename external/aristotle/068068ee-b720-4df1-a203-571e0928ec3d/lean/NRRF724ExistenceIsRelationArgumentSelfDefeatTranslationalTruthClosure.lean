import Mathlib

/-!
# NRRF724 — Existence is relation: no argument can argue a thing out of existence, and the
admission of that is exactly the translational truth closure of Existence / Identity / Reality /
Imagination

The statement formalized here is the user's:

> What I mean by existence is: for any argument, to argue that a thing must not exist is itself to
> relate to it — and existence *is* relation.  Admitting this is exactly the translational truth
> closure of Existence, Identity, Reality, Imagination.

## §1  The frame

A `Frame` carries the whole content of "existence is relation": a type `T` of terms, one symmetric
relation `rel` ("stands in relation to"), and, for each term, its *denial* `arg x` — the arguing
that `x` must not exist.  Existence is *defined* relationally, `Ex x ↔ ∃ y, rel y x`; it is not a
further property on top of the relation.  `existence_is_relational` makes that precise: existence
is preserved and reflected by every full relation-translation between frames, so it is a function
of the relation alone.

## §2  The self-defeat

`Frame.Denies a x` says the argument `a` relates to `x` and concludes that `x` does not exist.
`no_relating_denial` is the core theorem, and it needs no hypothesis at all: **no such denial
exists**.  Corollaries: an argument against `x` witnesses `Ex x` (`argument_grants_existence`), the
arguing itself exists (`denial_itself_exists`), and no term admits a relating denial while the
denier keeps its own existence (`denier_and_denied_both_exist`).

## §3  The four readings and their translations

`Reading` is the four-fold Existence / Identity / Reality / Imagination, read off the *same*
relation:

* Existence   `Ex x  := ∃ y, rel y x`                  — to be is to be related to;
* Identity    `Idn x := ∃ y, rel x y ∧ rel y x`        — to be itself is to be held in a two-way relation;
* Reality     `Re x  := ∃ y, rel y x ∧ Ex y`           — to be real is to be related to by something that is;
* Imagination `Im x  := rel (arg x) x`                 — even what merely argues it away relates to it.

`Frame.Transl a b` is truth-preserving translation between two readings (they agree at every term);
`transl_equivalence` shows the translations already form an equivalence relation, so they *are*
their own closure, and `translationalTruthClosure` is the complete such closure: all four readings
intertranslatable **and** true of every term.

## §4  The exactness

`admission_iff_translational_truth_closure`:

    Admission F  ↔  TranslationalTruthClosure F

— the admission (every denial relates to what it denies) and the complete translational truth
closure of the four readings are *the same condition*, not merely one implying the other.

`closure_needs_totality` is the sharpness check: intertranslatability by itself is strictly weaker
— the empty relation makes all four readings uniformly false, hence trivially intertranslatable,
while the admission fails.  So the totality clause in the closure is doing real work.

`existence_argument_frame` is a concrete non-vacuous model (distinctness on `ℕ`), where the
admission holds although no term is naively self-related.

`nrrf724_answer` collects the three headline facts.
-/

namespace NRRF724

/-! ## §1  The frame: existence is relation -/

/-- A **frame**: terms, one symmetric relation between them, and for each term the argument that
denies it.  Nothing else is assumed — in particular the relation is *not* assumed reflexive, and
existence is not primitive. -/
structure Frame where
  /-- the terms -/
  T : Type
  /-- "stands in relation to" -/
  rel : T → T → Prop
  /-- relation is mutual -/
  symm : ∀ {x y : T}, rel x y → rel y x
  /-- the arguing that a term must not exist -/
  arg : T → T

namespace Frame

variable (F : Frame)

/-- **Existence** is relation: to be is to be related to. -/
def Ex (x : F.T) : Prop := ∃ y, F.rel y x

/-- **Identity**: to be itself is to be held in a two-way relation. -/
def Idn (x : F.T) : Prop := ∃ y, F.rel x y ∧ F.rel y x

/-- **Reality**: to be real is to be related to by something that itself is. -/
def Re (x : F.T) : Prop := ∃ y, F.rel y x ∧ F.Ex y

/-- **Imagination**: what merely argues the term away still relates to it. -/
def Im (x : F.T) : Prop := F.rel (F.arg x) x

/-- Existence is witnessed by any relation. -/
theorem ex_of_rel {x y : F.T} (h : F.rel y x) : F.Ex x := ⟨y, h⟩

/-- Existence is symmetric in the relation: whatever relates, exists. -/
theorem ex_of_rel_left {x y : F.T} (h : F.rel x y) : F.Ex x := ⟨y, F.symm h⟩

end Frame

/-- A **full relation-translation** between frames: a map of terms that preserves and reflects the
relation, and is full onto the relaters of its image. -/
structure FrameTranslation (F G : Frame) where
  /-- the underlying map on terms -/
  f : F.T → G.T
  /-- the relation is preserved -/
  pres : ∀ {x y : F.T}, F.rel x y → G.rel (f x) (f y)
  /-- every relater of a translated term is itself translated -/
  full : ∀ (x : F.T) (b : G.T), G.rel b (f x) → ∃ a : F.T, f a = b ∧ F.rel a x

/-- **Existence is a function of the relation alone.**  Any full relation-translation preserves and
reflects existence — there is no residue of "existing" beyond standing in relation. -/
theorem existence_is_relational {F G : Frame} (t : FrameTranslation F G) (x : F.T) :
    F.Ex x ↔ G.Ex (t.f x) := by
  constructor
  · rintro ⟨y, hy⟩; exact ⟨t.f y, t.pres hy⟩
  · rintro ⟨b, hb⟩
    obtain ⟨a, _, ha⟩ := t.full x b hb
    exact ⟨a, ha⟩

/-! ## §2  The self-defeat of any argument against existence -/

namespace Frame

variable (F : Frame)

/-- `Denies a x`: the argument `a` relates to `x` and concludes that `x` does not exist. -/
def Denies (a x : F.T) : Prop := F.rel a x ∧ ¬ F.Ex x

end Frame

/-- **The core theorem, hypothesis-free.**  For any argument, to argue that a term must not exist
is already to relate to it, and to relate to it is for it to exist: there is no relating denial. -/
theorem no_relating_denial (F : Frame) (a x : F.T) : ¬ F.Denies a x := by
  rintro ⟨hrel, hnex⟩
  exact hnex ⟨a, hrel⟩

/-- The **admission**: every denial relates to what it denies. -/
def Frame.Admission (F : Frame) : Prop := ∀ x : F.T, F.rel (F.arg x) x

/-- Under the admission, the argument against a term grants the term's existence. -/
theorem argument_grants_existence {F : Frame} (h : F.Admission) (x : F.T) : F.Ex x :=
  ⟨F.arg x, h x⟩

/-- Under the admission, the arguing itself exists too. -/
theorem denial_itself_exists {F : Frame} (h : F.Admission) (x : F.T) : F.Ex (F.arg x) :=
  ⟨x, F.symm (h x)⟩

/-- Under the admission, denier and denied exist together: the denial cannot separate them. -/
theorem denier_and_denied_both_exist {F : Frame} (h : F.Admission) (x : F.T) :
    F.Ex x ∧ F.Ex (F.arg x) ∧ ¬ F.Denies (F.arg x) x :=
  ⟨argument_grants_existence h x, denial_itself_exists h x, no_relating_denial F _ x⟩

/-! ## §3  The four readings and truth-preserving translation between them -/

/-- The four readings of the one relation. -/
inductive Reading
  | existence
  | identity
  | reality
  | imagination
  deriving DecidableEq, Repr

namespace Frame

variable (F : Frame)

/-- Each reading, read off the same relation. -/
def read : Reading → F.T → Prop
  | Reading.existence => F.Ex
  | Reading.identity => F.Idn
  | Reading.reality => F.Re
  | Reading.imagination => F.Im

/-- **Truth-preserving translation** between two readings: they agree at every term. -/
def Transl (a b : Reading) : Prop := ∀ x : F.T, F.read a x ↔ F.read b x

/-- All four readings are true of every term. -/
def TotalTruth : Prop := ∀ (a : Reading) (x : F.T), F.read a x

/-- The **complete translational truth closure** of Existence / Identity / Reality / Imagination:
the four readings are pairwise intertranslatable and each holds of every term. -/
def TranslationalTruthClosure : Prop := (∀ a b : Reading, F.Transl a b) ∧ F.TotalTruth

end Frame

/-- Truth-preserving translation is already an equivalence relation: the translations are their own
closure. -/
theorem transl_equivalence (F : Frame) : Equivalence F.Transl where
  refl _ _ := Iff.rfl
  symm h x := (h x).symm
  trans h h' x := (h x).trans (h' x)

/-! ## §4  The exactness: the admission *is* the closure -/

/-- **Main theorem.**  Admitting that every argument against a term relates to that term is
*exactly* the complete translational truth closure of Existence, Identity, Reality and
Imagination — the two conditions are equivalent. -/
theorem admission_iff_translational_truth_closure (F : Frame) :
    F.Admission ↔ F.TranslationalTruthClosure := by
  constructor
  · intro h
    have total : F.TotalTruth := by
      intro a x
      cases a with
      | existence => exact ⟨F.arg x, h x⟩
      | identity => exact ⟨F.arg x, F.symm (h x), h x⟩
      | reality => exact ⟨F.arg x, h x, ⟨x, F.symm (h x)⟩⟩
      | imagination => exact h x
    exact ⟨fun a b x => iff_of_true (total a x) (total b x), total⟩
  · rintro ⟨-, total⟩ x
    exact total Reading.imagination x

/-- **Sharpness.**  Intertranslatability alone is strictly weaker than the admission: with the
empty relation all four readings are uniformly false, hence trivially intertranslatable, while the
admission fails.  The totality clause of the closure is therefore essential. -/
theorem closure_needs_totality :
    ∃ F : Frame, (∀ a b : Reading, F.Transl a b) ∧ ¬ F.Admission := by
  refine ⟨⟨ℕ, fun _ _ => False, fun h => h, id⟩, ?_, ?_⟩
  · intro a b x
    cases a <;> cases b <;>
      simp [Frame.read, Frame.Ex, Frame.Idn, Frame.Re, Frame.Im]
  · intro h
    exact h 0

/-- A concrete non-vacuous frame: terms are naturals, relation is distinctness, and the argument
against `x` is `x + 1`.  The admission holds although no term is naively self-related. -/
def existence_argument_frame : Frame where
  T := ℕ
  rel x y := x ≠ y
  symm h := Ne.symm h
  arg x := x + 1

theorem existence_argument_frame_admission : existence_argument_frame.Admission := by
  intro x
  exact Nat.succ_ne_self x

theorem existence_argument_frame_not_self_related (x : ℕ) :
    ¬ existence_argument_frame.rel x x := fun h => h rfl

/-- The concrete frame realizes the closure, so the closure is satisfiable and non-vacuous. -/
theorem existence_argument_frame_closure :
    existence_argument_frame.TranslationalTruthClosure :=
  (admission_iff_translational_truth_closure _).1 existence_argument_frame_admission

/-! ## §5  The answer -/

/-- **NRRF724.**  (i) No argument can relate to a term and yet deny its existence — the denial is
already a relation, and existence is relation.  (ii) Admitting this is *exactly* the complete
translational truth closure of Existence, Identity, Reality and Imagination.  (iii) That closure is
non-vacuous: a concrete frame realizes it. -/
theorem nrrf724_answer :
    (∀ (F : Frame) (a x : F.T), ¬ F.Denies a x) ∧
    (∀ F : Frame, F.Admission ↔ F.TranslationalTruthClosure) ∧
    existence_argument_frame.TranslationalTruthClosure :=
  ⟨no_relating_denial, admission_iff_translational_truth_closure,
    existence_argument_frame_closure⟩

end NRRF724
