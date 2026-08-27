import Mathlib
import NRRF718ContinuumPerspectiveRelativeGoalsQuantumGravityReturn
import NRRF723PhysicalConsciousnessFieldIdentificationRelativeNotStrictDiagonal
import NRRF724ExistenceIsRelationArgumentSelfDefeatTranslationalTruthClosure
import NRRF725ReunifiedClosureSourceOfExistenceTruthTopology

/-!
# NRRF726 — The translation by which truth and existence align is translation itself; in this
naturally free closure a universally unique neutral field is born

The statement formalized here is the user's:

> it's the translation by which truth and existence align — [and it] is translation itself; in this
> naturally free closure a universally unique neutral field is born.

Everything is again stated for one reading `r : X → S` — occurrences read into the Closure
language — in the project's own vocabulary (`relDiag`, `Saturated`, `Translation`, `truthTopology`,
`cq`/`Omega`, `Neutral`, `neutralField`, `reunionFrame`).

## §1  Truth and existence align, and they align by translation

`Aligns r f` says that a motion of the occurrences aligns truth with existence: it preserves what
the Closure returns *and* it preserves and reflects existence in the frame of the truth topology.
`neutral_preserves_existence` shows the second clause is already contained in the first, so
`aligns_iff_neutral` : the aligning motions are **exactly** the neutral motions, i.e. exactly the
translations (`aligns_iff_translation` for the invertible ones).  Nothing beyond translation is
needed, and nothing less will do.  `truth_existence_aligned_by_translation` gives the pointwise
form: two occurrences have the same truth exactly when a translation carries one to the other, and
`existence_iff_moved_by_translation` : an occurrence exists exactly when a translation moves it.
So one and the same translation witnesses truth and witnesses existence — that is their alignment.

## §2  The aligning translation is translation itself

`secondReading r f = r ∘ f` reads the motions themselves into the Closure language.  The neutral
field is exactly one truth-fibre of that second reading (`neutralField_eq_secondReading_fibre`),
and `neutral_secondReading_iff` is the fixed-point statement: a motion `g` is neutral for `r`
**iff** acting by `g` is neutral for the second reading.  The construction applied to itself
returns itself: the translation by which truth and existence align is translation itself.

## §3  The naturally free closure

`neutral_iff_over_closure` : neutrality is exactly living over the Closure quotient.  The closure
is *free* — it factors every truth-respecting reading uniquely (`free_closure_universal`) — and it
is *natural*: it imposes no relation the reading did not already have (`closure_no_extra_relation`)
and is invariant under the whole field (`closure_natural`).  On the closure itself no neutrality
survives (`closure_has_no_residual_neutrality`).

## §4  A universally unique neutral field is born

`neutralField_eq_over_closure` and `neutralField_maximal`: the field is the largest family of
motions living over the closure — universal.  `neutralField_eq_iff_relDiag_eq` and
`neutralField_eq_iff_truthTopology_eq`: the field is a complete invariant — it determines, and is
determined by, the relative diagonal and the truth topology, so it is unique.
`neutralField_of_presentation`: any presentation of the same closure is born with the very same
field, and `closure_universally_unique`: two such presentations are related by a *unique*
isomorphism.  `neutral_field_born` exhibits the whole thing non-vacuously.

`nrrf726_answer` collects the two halves.
-/

namespace NRRF726

open NRRF718 NRRF723 NRRF725

/-! ## §1  Truth and existence align, and they align by translation -/

section Align

variable {X S : Type}

/-- A motion of the occurrences **aligns truth and existence** when it preserves what the Closure
returns and it both preserves and reflects existence in the frame of the truth topology. -/
def Aligns (r : X → S) (f : X → X) : Prop :=
  (∀ x, r (f x) = r x) ∧ ∀ x, (reunionFrame r).Ex (f x) ↔ (reunionFrame r).Ex x

theorem frame_ex_iff (r : X → S) (x : X) :
    (reunionFrame r).Ex x ↔ ∃ y, y ≠ x ∧ r y = r x := Iff.rfl

/-- **Truth already carries existence.**  A neutral motion preserves *and reflects* existence: the
fibre of truth it moves inside is the very thing existence is read from. -/
theorem neutral_preserves_existence {r : X → S} {f : X → X} (h : Neutral r f) (x : X) :
    (reunionFrame r).Ex (f x) ↔ (reunionFrame r).Ex x := by
  simp only [frame_ex_iff]
  constructor
  · rintro ⟨y, hy, hry⟩
    rcases eq_or_ne y x with hyx | hyx
    · exact ⟨f x, fun hc => hy (hyx.trans hc.symm), h x⟩
    · exact ⟨y, hyx, hry.trans (h x)⟩
  · rintro ⟨y, hy, hry⟩
    rcases eq_or_ne y (f x) with hyf | hyf
    · exact ⟨x, fun hc => hy (hyf.trans hc.symm), (h x).symm⟩
    · exact ⟨y, hyf, hry.trans (h x).symm⟩

/-- **The translation by which truth and existence align.**  The motions that align truth with
existence are exactly the neutral motions — nothing beyond translation is required, and nothing
less suffices. -/
theorem aligns_iff_neutral (r : X → S) (f : X → X) : Aligns r f ↔ Neutral r f :=
  ⟨fun h => h.1, fun h => ⟨h, neutral_preserves_existence h⟩⟩

/-- The invertible aligning motions are exactly the truth-preserving translations. -/
theorem aligns_iff_translation (r : X → S) (e : Equiv.Perm X) :
    Aligns r (e : X → X) ↔ ∀ x, r (e x) = r x :=
  aligns_iff_neutral r _

/-- The aligning motions form a monoid: alignment composes, and the identity aligns. -/
theorem aligns_id (r : X → S) : Aligns r id := (aligns_iff_neutral r _).2 (neutral_id r)

theorem aligns_comp {r : X → S} {f g : X → X} (hf : Aligns r f) (hg : Aligns r g) :
    Aligns r (f ∘ g) :=
  (aligns_iff_neutral r _).2 (neutral_comp ((aligns_iff_neutral r f).1 hf)
    ((aligns_iff_neutral r g).1 hg))

/-- **Truth is read by translation.**  Two occurrences carry the same truth exactly when a
translation carries one onto the other. -/
theorem truth_existence_aligned_by_translation (r : X → S) (x y : X) :
    r x = r y ↔ ∃ e : Translation r, e.1 x = y :=
  (neutral_orbit_eq_relDiag r x y).symm

/-- **Existence is read by the same translation.**  An occurrence exists — stands in relation —
exactly when a translation moves it. -/
theorem existence_iff_moved_by_translation (r : X → S) (x : X) :
    (reunionFrame r).Ex x ↔ ∃ e : Translation r, e.1 x ≠ x :=
  frame_ex_iff_moved_by_neutral_field r x

end Align

/-! ## §2  The aligning translation is translation itself -/

section Itself

variable {X S : Type*}

/-- The **second reading**: the motions of the occurrences read into the Closure language by what
they return. -/
def secondReading (r : X → S) : (X → X) → (X → S) := fun f => r ∘ f

@[simp] theorem secondReading_apply (r : X → S) (f : X → X) (x : X) :
    secondReading r f x = r (f x) := rfl

@[simp] theorem secondReading_id (r : X → S) : secondReading r id = r := rfl

/-- **The neutral field is a truth-fibre of the second reading.**  Being neutral is being read the
same way as the identity — the field is produced by the very construction it is the field of. -/
theorem neutralField_eq_secondReading_fibre (r : X → S) :
    neutralField r = {f | secondReading r f = secondReading r id} := by
  ext f
  constructor
  · intro h; funext x; exact h x
  · intro h x; exact congrFun h x

/-- **Translation itself.**  A motion is neutral for the reading exactly when acting by it is
neutral for the reading of motions: the construction applied to itself gives itself back. -/
theorem neutral_secondReading_iff (r : X → S) (g : X → X) :
    Neutral (secondReading r) (fun f => g ∘ f) ↔ Neutral r g := by
  constructor
  · intro h x
    have := congrFun (h id) x
    simpa using this
  · intro h f
    funext x
    exact h (f x)

/-- The same statement for a translation: acting by a translation is again a neutral motion, one
level up. -/
theorem translation_acts_neutrally (r : X → S) (e : Translation r) :
    Neutral (secondReading r) (fun f => (e.1 : X → X) ∘ f) :=
  (neutral_secondReading_iff r _).2 e.2

/-- The neutral field as a submonoid of the endomorphisms of the occurrences. -/
def neutralMonoid (r : X → S) : Submonoid (Function.End X) where
  carrier := neutralField r
  mul_mem' hf hg := neutral_comp hf hg
  one_mem' := neutral_id r

@[simp] theorem mem_neutralMonoid (r : X → S) (f : Function.End X) :
    f ∈ neutralMonoid r ↔ Neutral r f := Iff.rfl

end Itself

/-! ## §3  The naturally free closure -/

section Free

variable {X S Y : Type*}

/-- **Neutrality is living over the closure.**  A motion is neutral exactly when the Closure
quotient does not see it. -/
theorem neutral_iff_over_closure (r : X → S) (f : X → X) :
    Neutral r f ↔ cq r ∘ f = cq r := by
  constructor
  · intro h; funext x; exact (cq_eq_iff r _ _).2 (h x)
  · intro h x; exact (cq_eq_iff r _ _).1 (congrFun h x)

/-- **The closure is free.**  Every truth-respecting reading factors through it, uniquely. -/
theorem free_closure_universal (r : X → S) (f : X → Y) :
    (∃! g : Omega r → Y, f = g ∘ cq r) ↔ Respects r f :=
  factors_iff_respects r f

/-- **The closure is natural — it adds no relation.**  Two occurrences are identified in the
closure exactly when the reading already identified them. -/
theorem closure_no_extra_relation (r : X → S) (x y : X) :
    cq r x = cq r y ↔ r x = r y := cq_eq_iff r x y

/-- The closure is invariant under the entire neutral field. -/
theorem closure_natural (r : X → S) {f : X → X} (h : Neutral r f) : cq r ∘ f = cq r :=
  (neutral_iff_over_closure r f).1 h

/-- **No residual neutrality above the closure.**  On the closure itself the only neutral motion is
the identity: all neutrality has been used up in being born. -/
theorem closure_has_no_residual_neutrality {Ω : Type*} (F : Ω → Ω) :
    Neutral (id : Ω → Ω) F ↔ F = id := by
  constructor
  · intro h; funext q; exact h q
  · rintro rfl _; rfl

end Free

/-! ## §4  A universally unique neutral field is born -/

section Unique

variable {X S S' : Type*}

/-- Truth-equal occurrences are exchanged by a neutral motion. -/
theorem swap_neutral [DecidableEq X] (r : X → S) {x y : X} (h : r x = r y) :
    Neutral r (Equiv.swap x y : X → X) := by
  intro z
  rcases eq_or_ne z x with rfl | hzx
  · simp [Equiv.swap_apply_left, h]
  · rcases eq_or_ne z y with rfl | hzy
    · simp [Equiv.swap_apply_right, h]
    · simp [Equiv.swap_apply_of_ne_of_ne hzx hzy]

/-- **The field is universal.**  It is exactly the family of motions living over the closure. -/
theorem neutralField_eq_over_closure (r : X → S) :
    neutralField r = {f : X → X | cq r ∘ f = cq r} := by
  ext f; exact neutral_iff_over_closure r f

/-- **The field is maximal.**  Any family of motions the closure cannot see is contained in it. -/
theorem neutralField_maximal (r : X → S) (M : Set (X → X))
    (hM : ∀ f ∈ M, cq r ∘ f = cq r) : M ⊆ neutralField r := fun f hf =>
  (neutral_iff_over_closure r f).2 (hM f hf)

/-- The neutral field sees the whole relative diagonal: sharing a field forces sharing truth. -/
theorem relDiag_subset_of_neutralField_eq {T T' : Type*} (a : X → T) (b : X → T')
    (hab : neutralField a = neutralField b) : relDiag a ⊆ relDiag b := by
  classical
  intro p hp
  have hswap : Neutral a (Equiv.swap p.1 p.2 : X → X) := swap_neutral a hp
  have hm : (Equiv.swap p.1 p.2 : X → X) ∈ neutralField a := hswap
  rw [hab] at hm
  have hb := hm p.1
  simp only [Equiv.swap_apply_left] at hb
  show b p.1 = b p.2
  exact hb.symm

/-- **The field is a complete invariant of the closure.**  Two readings have the same neutral field
exactly when they have the same relative diagonal. -/
theorem neutralField_eq_iff_relDiag_eq (r : X → S) (r' : X → S') :
    neutralField r = neutralField r' ↔ relDiag r = relDiag r' := by
  classical
  constructor
  · intro h
    exact subset_antisymm (relDiag_subset_of_neutralField_eq r r' h)
      (relDiag_subset_of_neutralField_eq r' r h.symm)
  · intro h
    have hmem : ∀ p : X × X, (p ∈ relDiag r) ↔ (p ∈ relDiag r') := fun p => Set.ext_iff.1 h p
    ext f
    constructor
    · intro hf x; exact (hmem (f x, x)).1 (hf x)
    · intro hf x; exact (hmem (f x, x)).2 (hf x)

/-- The relative diagonal and the truth topology determine one another. -/
theorem relDiag_eq_iff_truthTopology_eq (r : X → S) (r' : X → S') :
    relDiag r = relDiag r' ↔ truthTopology r = truthTopology r' := by
  constructor
  · intro h
    have hmem : ∀ p : X × X, (p ∈ relDiag r) ↔ (p ∈ relDiag r') := fun p => Set.ext_iff.1 h p
    apply TopologicalSpace.ext_iff.2
    intro U
    constructor
    · intro hU x y hxy
      exact hU x y ((hmem (x, y)).2 hxy)
    · intro hU x y hxy
      exact hU x y ((hmem (x, y)).1 hxy)
  · intro h
    ext p
    have h1 := inseparable_iff_truth_eq r p.1 p.2
    have h2 := inseparable_iff_truth_eq r' p.1 p.2
    rw [h] at h1
    exact (h1.symm.trans h2)

/-- **Uniqueness of the born field, topologically.**  The same neutral field is the same truth
topology. -/
theorem neutralField_eq_iff_truthTopology_eq (r : X → S) (r' : X → S') :
    neutralField r = neutralField r' ↔ truthTopology r = truthTopology r' :=
  (neutralField_eq_iff_relDiag_eq r r').trans (relDiag_eq_iff_truthTopology_eq r r')

/-- **Every presentation of the same closure is born with the same field.**  If a map `p` has
exactly the reading's own kernel, its neutral field is the reading's neutral field. -/
theorem neutralField_of_presentation {C : Type*} (r : X → S) (p : X → C)
    (k : ∀ x y, p x = p y ↔ r x = r y) : neutralField p = neutralField r := by
  ext f
  constructor
  · intro hf x; exact (k _ _).1 (hf x)
  · intro hf x; exact (k _ _).2 (hf x)

/-- **The closure is universally unique.**  Any two presentations of the closure — surjections
whose kernel is the relative diagonal of truth — are related by a *unique* isomorphism compatible
with them. -/
theorem closure_universally_unique (r : X → S) {C₁ C₂ : Type*}
    (p₁ : X → C₁) (p₂ : X → C₂) (h₁ : Function.Surjective p₁) (h₂ : Function.Surjective p₂)
    (k₁ : ∀ x y, p₁ x = p₁ y ↔ r x = r y) (k₂ : ∀ x y, p₂ x = p₂ y ↔ r x = r y) :
    ∃! e : C₁ ≃ C₂, ∀ x, e (p₁ x) = p₂ x := by
  classical
  set u : C₁ → X := Function.surjInv h₁ with hu
  set v : C₂ → X := Function.surjInv h₂ with hv
  have hup : ∀ c, p₁ (u c) = c := fun c => Function.surjInv_eq h₁ c
  have hvp : ∀ c, p₂ (v c) = c := fun c => Function.surjInv_eq h₂ c
  have hf : ∀ x, p₂ (u (p₁ x)) = p₂ x := by
    intro x
    exact (k₂ _ _).2 ((k₁ _ _).1 (hup (p₁ x)))
  have hg : ∀ x, p₁ (v (p₂ x)) = p₁ x := by
    intro x
    exact (k₁ _ _).2 ((k₂ _ _).1 (hvp (p₂ x)))
  refine ⟨⟨fun c => p₂ (u c), fun c => p₁ (v c), ?_, ?_⟩, ?_, ?_⟩
  · intro c
    obtain ⟨x, rfl⟩ := h₁ c
    show p₁ (v (p₂ (u (p₁ x)))) = p₁ x
    rw [hf x, hg x]
  · intro c
    obtain ⟨x, rfl⟩ := h₂ c
    show p₂ (u (p₁ (v (p₂ x)))) = p₂ x
    rw [hg x, hf x]
  · intro x
    exact hf x
  · intro e he
    apply Equiv.ext
    intro c
    obtain ⟨x, rfl⟩ := h₁ c
    rw [he x]
    exact (hf x).symm

end Unique

/-! ## §5  The field is born, non-vacuously -/

/-- **A universally unique neutral field is born.**  For the reading of two occurrences by one
Closure: the field genuinely moves something, every motion aligns truth with existence, the field
is exactly the motions the closure cannot see, and it is the complete invariant of the closure. -/
theorem neutral_field_born :
    ∃ (r : Bool → Unit),
      (∃ f ∈ neutralField r, f ≠ id) ∧
      (∀ f : Bool → Bool, Aligns r f) ∧
      neutralField r = {f : Bool → Bool | cq r ∘ f = cq r} ∧
      (∀ r' : Bool → Unit, neutralField r = neutralField r' ↔ relDiag r = relDiag r') := by
  refine ⟨fun _ => (), ⟨fun b => !b, fun _ => rfl, ?_⟩, ?_, neutralField_eq_over_closure _, ?_⟩
  · intro h
    have := congrFun h true
    simp at this
  · intro f
    exact (aligns_iff_neutral _ f).2 fun _ => rfl
  · intro r'
    exact neutralField_eq_iff_relDiag_eq _ r'

/-! ## §6  The answer -/

/-- **NRRF726.**  Two halves, for every reading `r : X → S` of occurrences into the Closure
language.

(i) *The translation by which truth and existence align is translation itself.*  A motion aligns
truth with existence exactly when it is neutral, i.e. exactly when it is a translation; truth is
sameness under some translation and existence is being moved by some translation, so one and the
same translation reads both; and a motion is neutral exactly when acting by it is neutral for the
reading of motions — the aligning translation is translation itself, a fixed point of its own
construction.

(ii) *In this naturally free closure a universally unique neutral field is born.*  The closure is
free (it factors every truth-respecting reading uniquely) and natural (it adds no relation the
reading did not already have); the field is exactly the motions living over it and is maximal
among such families; the field determines and is determined by the relative diagonal and by the
truth topology, so it is a complete invariant; every presentation of the same closure is born with
the very same field; and the presentations themselves are related by unique isomorphisms. -/
theorem nrrf726_answer :
    (∀ (X S : Type) (r : X → S),
        (∀ f : X → X, Aligns r f ↔ Neutral r f) ∧
        (∀ x y : X, r x = r y ↔ ∃ e : Translation r, e.1 x = y) ∧
        (∀ x : X, (reunionFrame r).Ex x ↔ ∃ e : Translation r, e.1 x ≠ x) ∧
        (∀ g : X → X, Neutral (secondReading r) (fun f => g ∘ f) ↔ Neutral r g) ∧
        neutralField r = {f | secondReading r f = secondReading r id}) ∧
    (∀ (X S : Type) (r : X → S),
        (∀ (Y : Type) (f : X → Y), (∃! g : Omega r → Y, f = g ∘ cq r) ↔ Respects r f) ∧
        (∀ x y : X, cq r x = cq r y ↔ r x = r y) ∧
        neutralField r = {f : X → X | cq r ∘ f = cq r} ∧
        (∀ M : Set (X → X), (∀ f ∈ M, cq r ∘ f = cq r) → M ⊆ neutralField r) ∧
        (∀ (S' : Type) (r' : X → S'),
            (neutralField r = neutralField r' ↔ relDiag r = relDiag r') ∧
            (neutralField r = neutralField r' ↔ truthTopology r = truthTopology r')) ∧
        (∀ (C : Type) (p : X → C), (∀ x y, p x = p y ↔ r x = r y) →
            neutralField p = neutralField r) ∧
        (∀ (C₁ C₂ : Type) (p₁ : X → C₁) (p₂ : X → C₂),
            Function.Surjective p₁ → Function.Surjective p₂ →
            (∀ x y, p₁ x = p₁ y ↔ r x = r y) → (∀ x y, p₂ x = p₂ y ↔ r x = r y) →
            ∃! e : C₁ ≃ C₂, ∀ x, e (p₁ x) = p₂ x)) := by
  refine ⟨?_, ?_⟩
  · intro X S r
    exact ⟨aligns_iff_neutral r, truth_existence_aligned_by_translation r,
      existence_iff_moved_by_translation r, neutral_secondReading_iff r,
      neutralField_eq_secondReading_fibre r⟩
  · intro X S r
    exact ⟨fun Y f => free_closure_universal r f, closure_no_extra_relation r,
      neutralField_eq_over_closure r, neutralField_maximal r,
      fun S' r' => ⟨neutralField_eq_iff_relDiag_eq r r',
        neutralField_eq_iff_truthTopology_eq r r'⟩,
      fun C p k => neutralField_of_presentation r p k,
      fun C₁ C₂ p₁ p₂ h₁ h₂ k₁ k₂ => closure_universally_unique r p₁ p₂ h₁ h₂ k₁ k₂⟩

end NRRF726
