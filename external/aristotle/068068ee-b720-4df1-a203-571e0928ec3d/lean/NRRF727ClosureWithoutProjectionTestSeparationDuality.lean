import Mathlib
import NRRF718ContinuumPerspectiveRelativeGoalsQuantumGravityReturn
import NRRF725ReunifiedClosureSourceOfExistenceTruthTopology

/-!
# NRRF727 — Closure without a projection: the test-separation (polarity) picture

The earlier development always presented the Closure the same way: an occurrence is *projected*
to what it returns (`r : X → S`), and the Closure relation is "lying in the same fibre" — the
ball-and-hair projection, and the sheaf-fibre picture.  This module gives a genuinely different
presentation of the same subject matter, one in which **no projection and no fibre appear at
all**.

The only datum is a relation

  `ans : X → T → Prop`,  "the occurrence `x` answers the test `t`",

between occurrences and tests.  From it one builds the two **polarities**

  `passed ans A = {t | every occurrence of A answers t}`,
  `passing ans B = {x | x answers every test of B}`,

an antitone Galois connection (`polarity_galois`) whose composite `hull` is a closure operator
(`subset_hull`, `hull_mono`, `hull_hull`).  Nothing is projected anywhere; the closure of a set is
what the tests already hold along with it.

* **§1–§2 The polarity and its closure operator.**  `hull_isLeast` : `hull A` is the least
  test-closed set containing `A`; `sInter_testClosed` : the test-closed sets are stable under
  arbitrary intersection.

* **§3 Duality.**  `conceptEquiv` : the polarities restrict to a bijection between the test-closed
  sets of occurrences and the closed sets of tests, and `conceptEquiv_antitone` says it reverses
  inclusion.  Occurrences and tests are two faces of one datum; neither is a base and neither is a
  fibre.

* **§4 Indistinguishability.**  `NoTestSeparates ans x y` — no test tells the two apart.  It is
  the *mutual* hull relation (`noTestSeparates_iff_mutual_hull`); the hull of a point is in general
  strictly larger (a specialization preorder, not a partition).  `hullOrder` is that preorder.

* **§5 The bridge to the projection picture.**  The derived reading `profile ans x = {t | ans x t}`
  turns the test picture into the old one: `relDiag_profile` (the relative diagonal of the derived
  reading is exactly non-separation), `saturated_profile_iff`, `neutral_profile_iff`
  (the neutral field of NRRF725 is exactly the test-neutral motions), and
  `omegaEquivProfiles` (the Closure language is exactly the set of realised test profiles).
  Conversely `readingTests` turns any projection into tests, with
  `hull_singleton_readingTests` recovering the fibre.

* **§6 The two pictures are not the same.**  `readingTests_sharp` : tests coming from a projection
  are *sharp*, and `sharp_iff_hull_singleton_eq_class` : sharpness is exactly the condition under
  which the hull of a point collapses to its indistinguishability class — i.e. exactly when the
  test picture degenerates to a fibre picture.  `boolAns_hull_singleton_ne_class` exhibits tests
  that are not sharp, so the test presentation is strictly more general.

* **§7 Every closure system is a test duality.**  `testClosed_iff_mem` : for *any* family `𝒞` of
  subsets of `X` stable under arbitrary intersections there is a set of tests whose closed sets are
  exactly `𝒞`.  So this presentation loses nothing: it is not a special picture but the general
  one.

`nrrf727_answer` collects the three headline points.
-/

namespace NRRF727

open NRRF718

/-! ## §1  Occurrences, tests, and the polarity -/

section Polarity

variable {X T : Type*}

/-- The tests answered by **every** occurrence of `A`. -/
def passed (ans : X → T → Prop) (A : Set X) : Set T := {t | ∀ x ∈ A, ans x t}

/-- The occurrences answering **every** test of `B`. -/
def passing (ans : X → T → Prop) (B : Set T) : Set X := {x | ∀ t ∈ B, ans x t}

/-- The **hull** of a set of occurrences: everything the tests hold along with it. -/
def hull (ans : X → T → Prop) (A : Set X) : Set X := passing ans (passed ans A)

/-- The dual hull on the side of the tests. -/
def dualHull (ans : X → T → Prop) (B : Set T) : Set T := passed ans (passing ans B)

variable {ans : X → T → Prop} {A A₁ A₂ : Set X} {B B₁ B₂ : Set T}

/-- **The polarity is an antitone Galois connection.** -/
theorem polarity_galois : A ⊆ passing ans B ↔ B ⊆ passed ans A := by
  constructor
  · intro h t ht x hx
    exact h hx t ht
  · intro h x hx t ht
    exact h ht x hx

theorem passed_antitone (h : A₁ ⊆ A₂) : passed ans A₂ ⊆ passed ans A₁ :=
  fun _ ht x hx => ht x (h hx)

theorem passing_antitone (h : B₁ ⊆ B₂) : passing ans B₂ ⊆ passing ans B₁ :=
  fun _ hx t ht => hx t (h ht)

theorem subset_hull : A ⊆ hull ans A := fun _ hx _ ht => ht _ hx

theorem subset_dualHull : B ⊆ dualHull ans B := fun _ ht _ hx => hx _ ht

theorem hull_mono (h : A₁ ⊆ A₂) : hull ans A₁ ⊆ hull ans A₂ :=
  passing_antitone (passed_antitone h)

/-- The tests of a set and of its hull are the same. -/
theorem passed_hull : passed ans (hull ans A) = passed ans A :=
  Set.Subset.antisymm (passed_antitone subset_hull) subset_dualHull

theorem passing_dualHull : passing ans (dualHull ans B) = passing ans B :=
  Set.Subset.antisymm (passing_antitone subset_dualHull) subset_hull

/-- **The hull is idempotent**: it is a genuine closure operator. -/
theorem hull_hull : hull ans (hull ans A) = hull ans A :=
  congrArg (passing ans) passed_hull

end Polarity

/-! ## §2  Test-closed sets -/

section Closed

variable {X T : Type*} {ans : X → T → Prop} {A : Set X} {B : Set T}

/-- A set of occurrences is **test-closed** when the tests it passes single it out. -/
def TestClosed (ans : X → T → Prop) (A : Set X) : Prop := hull ans A = A

/-- A set of tests is closed when the occurrences passing it single it out. -/
def DualClosed (ans : X → T → Prop) (B : Set T) : Prop := dualHull ans B = B

theorem testClosed_hull : TestClosed ans (hull ans A) := hull_hull

theorem dualClosed_passed : DualClosed ans (passed ans A) := passed_hull

theorem testClosed_passing : TestClosed ans (passing ans B) := passing_dualHull

/-- **The hull is the least test-closed set containing `A`.** -/
theorem hull_isLeast : A ⊆ hull ans A ∧ TestClosed ans (hull ans A) ∧
    ∀ C, TestClosed ans C → A ⊆ C → hull ans A ⊆ C := by
  refine ⟨subset_hull, testClosed_hull, ?_⟩
  intro C hC hAC
  calc hull ans A ⊆ hull ans C := hull_mono hAC
    _ = C := hC

/-- The test-closed sets form a closure system: they are stable under arbitrary intersections. -/
theorem sInter_testClosed (𝒮 : Set (Set X)) (h : ∀ C ∈ 𝒮, TestClosed ans C) :
    TestClosed ans (⋂₀ 𝒮) := by
  refine Set.Subset.antisymm ?_ subset_hull
  intro x hx C hC
  have : hull ans (⋂₀ 𝒮) ⊆ hull ans C := hull_mono (Set.sInter_subset_of_mem hC)
  rw [h C hC] at this
  exact this hx

end Closed

/-! ## §3  The duality between occurrences and tests -/

section Duality

variable {X T : Type*} (ans : X → T → Prop)

/-- **The polarity is a bijection between the closed sets on the two sides.**  Occurrences and
tests are two faces of one relation: neither is the base of a projection and neither is a fibre. -/
def conceptEquiv : {A : Set X // TestClosed ans A} ≃ {B : Set T // DualClosed ans B} where
  toFun A := ⟨passed ans A.1, dualClosed_passed⟩
  invFun B := ⟨passing ans B.1, testClosed_passing⟩
  left_inv A := Subtype.ext A.2
  right_inv B := Subtype.ext B.2

@[simp] theorem conceptEquiv_apply (A : {A : Set X // TestClosed ans A}) :
    (conceptEquiv ans A : Set T) = passed ans A.1 := rfl

@[simp] theorem conceptEquiv_symm_apply (B : {B : Set T // DualClosed ans B}) :
    ((conceptEquiv ans).symm B : Set X) = passing ans B.1 := rfl

/-- The duality reverses inclusion. -/
theorem conceptEquiv_antitone (A₁ A₂ : {A : Set X // TestClosed ans A}) :
    (A₁ : Set X) ⊆ A₂ ↔ (conceptEquiv ans A₂ : Set T) ⊆ conceptEquiv ans A₁ := by
  constructor
  · intro h; exact passed_antitone h
  · intro h
    have h2 : hull ans A₁.1 ⊆ hull ans A₂.1 := passing_antitone h
    rw [A₁.2, A₂.2] at h2
    exact h2

end Duality

/-! ## §4  Indistinguishability, without fibres -/

section Indist

variable {X T : Type*} (ans : X → T → Prop)

/-- The **profile** of an occurrence: the tests it answers.  (A derived reading — it is not given
in advance, and it is not a projection onto anything external.) -/
def profile (x : X) : Set T := {t | ans x t}

/-- **No test separates `x` from `y`.** -/
def NoTestSeparates (x y : X) : Prop := ∀ t, ans x t ↔ ans y t

/-- The specialization preorder of the hull. -/
def hullOrder (x y : X) : Prop := profile ans x ⊆ profile ans y

variable {ans}

theorem noTestSeparates_iff_profile_eq {x y : X} :
    NoTestSeparates ans x y ↔ profile ans x = profile ans y := by
  constructor
  · intro h; ext t; exact h t
  · intro h t; exact Set.ext_iff.1 h t

theorem hull_singleton (x : X) : hull ans {x} = {y | hullOrder ans x y} := by
  ext y
  constructor
  · intro hy t ht
    exact hy t (fun z hz => by cases hz; exact ht)
  · intro hy t ht
    exact hy (ht x rfl)

theorem hullOrder_refl (x : X) : hullOrder ans x x := le_refl _

theorem hullOrder_trans {x y z : X} (h₁ : hullOrder ans x y) (h₂ : hullOrder ans y z) :
    hullOrder ans x z := h₁.trans h₂

/-- **Indistinguishability is the mutual hull relation.** -/
theorem noTestSeparates_iff_mutual_hull {x y : X} :
    NoTestSeparates ans x y ↔ y ∈ hull ans {x} ∧ x ∈ hull ans {y} := by
  rw [hull_singleton, hull_singleton, noTestSeparates_iff_profile_eq]
  constructor
  · intro h; exact ⟨h.subset, h.symm.subset⟩
  · intro h; exact Set.Subset.antisymm h.1 h.2

/-- A motion of the occurrences is **test-neutral** when it changes no answer. -/
def TestNeutral (ans : X → T → Prop) (f : X → X) : Prop := ∀ x, NoTestSeparates ans (f x) x

/-- A test-neutral motion cannot change what a set is tested to be. -/
theorem passed_image_of_testNeutral {f : X → X} (hf : TestNeutral ans f) (A : Set X) :
    passed ans A ⊆ passed ans (f '' A) := by
  rintro t ht _ ⟨x, hx, rfl⟩
  exact (hf x t).2 (ht x hx)

theorem hull_image_of_testNeutral {f : X → X} (hf : TestNeutral ans f) (A : Set X) :
    f '' A ⊆ hull ans A := by
  rintro _ ⟨x, hx, rfl⟩ t ht
  exact (hf x t).2 (ht x hx)

end Indist

/-! ## §5  The bridge to the projection picture -/

section Bridge

variable {X T S : Type*}

/-- The relative diagonal of the derived reading is exactly non-separation by tests. -/
theorem relDiag_profile (ans : X → T → Prop) :
    relDiag (profile ans) = {p : X × X | NoTestSeparates ans p.1 p.2} := by
  ext p
  exact (noTestSeparates_iff_profile_eq (ans := ans)).symm

/-- Saturated sets of the derived reading are exactly the sets no test-indistinguishable pair
straddles: the truth topology of NRRF718 read off the tests. -/
theorem saturated_profile_iff (ans : X → T → Prop) (U : Set X) :
    Saturated (profile ans) U ↔ ∀ x y, NoTestSeparates ans x y → (x ∈ U ↔ y ∈ U) := by
  constructor
  · intro h x y hxy
    exact h x y (noTestSeparates_iff_profile_eq.1 hxy)
  · intro h x y hxy
    exact h x y (noTestSeparates_iff_profile_eq.2 hxy)

/-- The neutral field of NRRF725 for the derived reading is exactly the test-neutral motions. -/
theorem neutral_profile_iff (ans : X → T → Prop) (f : X → X) :
    NRRF725.Neutral (profile ans) f ↔ TestNeutral ans f := by
  constructor
  · intro h x
    exact noTestSeparates_iff_profile_eq.2 (h x)
  · intro h x
    exact noTestSeparates_iff_profile_eq.1 (h x)

/-- The Closure language of any reading is exactly the set of values it realises. -/
noncomputable def omegaEquivRange (r : X → S) : Omega r ≃ Set.range r :=
  Equiv.ofBijective (Quotient.lift (fun x => (⟨r x, x, rfl⟩ : Set.range r))
      (fun _ _ h => Subtype.ext h))
    ⟨by
      intro a b hab
      induction a using Quotient.ind with
      | _ x =>
        induction b using Quotient.ind with
        | _ y => exact (cq_eq_iff r x y).2 (congrArg Subtype.val hab),
     by
      rintro ⟨s, x, rfl⟩
      exact ⟨cq r x, rfl⟩⟩

/-- **The Closure language is the set of realised test profiles.**  No fibre is ever formed. -/
noncomputable def omegaEquivProfiles (ans : X → T → Prop) :
    Omega (profile ans) ≃ Set.range (profile ans) := omegaEquivRange _

/-- Tests manufactured from a projection: "does the occurrence return `s`?". -/
def readingTests (r : X → S) : X → S → Prop := fun x s => r x = s

theorem noTestSeparates_readingTests (r : X → S) (x y : X) :
    NoTestSeparates (readingTests r) x y ↔ r x = r y := by
  constructor
  · intro h
    exact ((h (r x)).1 rfl).symm
  · intro h t
    simp [readingTests, h]

/-- With tests manufactured from a projection the hull of a point is exactly its fibre: the
sheaf-fibre picture is the special case in which the tests are the values of one projection. -/
theorem hull_singleton_readingTests (r : X → S) (x : X) :
    hull (readingTests r) {x} = {y | r y = r x} := by
  ext y
  constructor
  · intro hy
    exact hy (r x) (fun z hz => by cases hz; rfl)
  · intro hy t ht
    have := ht x rfl
    simp only [readingTests] at this ⊢
    rw [hy, this]

end Bridge

/-! ## §6  The test picture is strictly more general -/

section Sharp

variable {X T : Type*} {S : Type*}

/-- A family of tests is **sharp** when its order is symmetric — when comparability of profiles
already forces equality.  Sharpness is exactly the degeneration of the test picture into a
partition into fibres. -/
def Sharp (ans : X → T → Prop) : Prop := ∀ x y, hullOrder ans x y → hullOrder ans y x

theorem readingTests_sharp (r : X → S) : Sharp (readingTests r) := by
  intro x y h s hs
  simp only [profile, readingTests, Set.mem_setOf_eq] at hs ⊢
  have hx : (r x = r x) := rfl
  have := h (show r x ∈ profile (readingTests r) x from hx)
  simp only [profile, readingTests, Set.mem_setOf_eq] at this
  rw [← hs, this]

/-- **Sharpness is exactly fibredness.**  The hull of every point is its indistinguishability
class precisely when the tests are sharp. -/
theorem sharp_iff_hull_singleton_eq_class (ans : X → T → Prop) :
    Sharp ans ↔ ∀ x, hull ans {x} = {y | NoTestSeparates ans x y} := by
  constructor
  · intro h x
    rw [hull_singleton]
    ext y
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hy
      exact noTestSeparates_iff_profile_eq.2 (Set.Subset.antisymm hy (h x y hy))
    · intro hy
      exact (noTestSeparates_iff_profile_eq.1 hy).subset
  · intro h x y hxy
    have : y ∈ hull ans {x} := by rw [hull_singleton]; exact hxy
    rw [h x] at this
    exact (noTestSeparates_iff_profile_eq.1 this).symm.subset

/-- One occurrence, one test, no sharpness: the answer `false` passes no test, so everything is in
its hull, while nothing but itself is indistinguishable from it. -/
def boolAns : Bool → Unit → Prop := fun x _ => x = true

theorem boolAns_hull_singleton_ne_class :
    hull boolAns {false} ≠ {y | NoTestSeparates boolAns false y} := by
  intro h
  have htrue : (true : Bool) ∈ hull boolAns {false} := by
    intro t ht
    have := ht false rfl
    simp [boolAns] at this
  rw [h] at htrue
  have := (htrue ()).2 rfl
  simp [boolAns] at this

/-- Hence the test presentation is strictly more general than the fibre presentation. -/
theorem exists_not_sharp : ∃ (X T : Type) (ans : X → T → Prop), ¬ Sharp ans := by
  refine ⟨Bool, Unit, boolAns, ?_⟩
  intro h
  exact boolAns_hull_singleton_ne_class ((sharp_iff_hull_singleton_eq_class boolAns).1 h false)

end Sharp

/-! ## §7  Every closure system is a test duality -/

section Representation

variable {X : Type*} (𝒞 : Set (Set X))

/-- The tests attached to a family of subsets: "does the occurrence lie in this member?". -/
def memberTests : X → {C : Set X // C ∈ 𝒞} → Prop := fun x C => x ∈ (C : Set X)

theorem hull_memberTests (A : Set X) :
    hull (memberTests 𝒞) A = ⋂₀ {C | C ∈ 𝒞 ∧ A ⊆ C} := by
  ext x
  constructor
  · rintro hx C ⟨hC𝒞, hAC⟩
    exact hx ⟨C, hC𝒞⟩ (fun z hz => hAC hz)
  · intro hx C hC
    exact hx C.1 ⟨C.2, fun z hz => hC z hz⟩

/-- **Representation theorem.**  For any family of subsets stable under arbitrary intersections,
the test-closed sets of the associated tests are exactly the members of the family.  So every
closure system whatsoever is presented by a separation relation — this picture is not a special
case, it is the general one. -/
theorem testClosed_iff_mem (hInter : ∀ 𝒮 ⊆ 𝒞, ⋂₀ 𝒮 ∈ 𝒞) (A : Set X) :
    TestClosed (memberTests 𝒞) A ↔ A ∈ 𝒞 := by
  constructor
  · intro hA
    have h := hull_memberTests 𝒞 A
    rw [hA] at h
    rw [h]
    exact hInter _ (fun C hC => hC.1)
  · intro hA
    refine Set.Subset.antisymm ?_ subset_hull
    rw [hull_memberTests]
    exact Set.sInter_subset_of_mem ⟨hA, subset_rfl⟩

end Representation

/-! ## §8  The answer -/

/-- **NRRF727.**  The Closure has a presentation with no projection and no fibre in it:

1. from a bare separation relation between occurrences and tests, the polarity is an antitone
   Galois connection whose composite is a closure operator, and it identifies the closed sets of
   occurrences with the closed sets of tests (`conceptEquiv`);
2. it subsumes the projection picture — the tests of a projection have exactly the fibres as
   hulls — and it is strictly more general, since not every family of tests is sharp;
3. and it is completely general: every closure system on the occurrences arises this way. -/
theorem nrrf727_answer :
    (∀ (X T : Type) (ans : X → T → Prop) (A : Set X), A ⊆ hull ans A ∧
        hull ans (hull ans A) = hull ans A) ∧
    (∀ (X S : Type) (r : X → S) (x : X),
        hull (readingTests r) {x} = {y | r y = r x} ∧ Sharp (readingTests r)) ∧
    (∃ (X T : Type) (ans : X → T → Prop), ¬ Sharp ans) ∧
    (∀ (X : Type) (𝒞 : Set (Set X)), (∀ 𝒮 ⊆ 𝒞, ⋂₀ 𝒮 ∈ 𝒞) →
        ∀ A : Set X, TestClosed (memberTests 𝒞) A ↔ A ∈ 𝒞) := by
  refine ⟨fun X T ans A => ⟨subset_hull, hull_hull⟩, fun X S r x =>
    ⟨hull_singleton_readingTests r x, readingTests_sharp r⟩, exists_not_sharp,
    fun X 𝒞 h A => testClosed_iff_mem 𝒞 h A⟩

end NRRF727
