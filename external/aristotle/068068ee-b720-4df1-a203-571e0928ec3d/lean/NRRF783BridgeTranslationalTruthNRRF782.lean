import NRRF782TranslationalTruthUniqueIsomorphicSetsSizesPotentialsRelativeAbsolutes
import NRRF783TranslationalTruthFormsWithoutClassical

/-!
# NRRF783d — The translational-truth forms of NRRF782, without classical logic

`NRRF783TranslationalTruthFormsWithoutClassical` develops translational truth with no library in
scope.  This module connects it to the project's own translational-truth module NRRF782 and
removes the classical steps there.

## §1  It is the same notion

A Mathlib additive commutative group supplies the level data of the constructive development
(`levels`), and under it `NRRF783T.TransTruth` *is* `NRRF782.TransTruth` and `NRRF783T.Closure` is
membership in `NRRF782.Closure` — both `Iff.rfl` (`transTruth_iff`, `mem_closure_iff`).

## §2  Where classical logic entered NRRF782, and how it is removed

The audit in §3 shows that `closure_eq_iff_transTruth`, `exists_unique_closure`,
`potential_invariant`, `value_not_absolute` and `transTruth_transEq` were already choice-free.
`Classical.choice` entered in two ways, both avoidable:

1. **A dichotomy that must decide translational truth.**  `closure_eq_or_disjoint` asserts that two
   closures are equal *or* disjoint; deciding which is a classical step.  The constructive content
   — a shared reading forces equality — is `closure_eq_of_overlap`, and it is what the development
   actually uses.
2. **`[Nonempty ι]` used to produce a site.**  Extracting an actual site from bare non-emptiness is
   choice.  Taking the site as data instead makes everything computable:
   `shift_unique_at_site`, `closureEquivOfSite` (a *computable* replacement for the noncomputable
   `NRRF782.closureEquiv`), `closureIsoOfSite`, `potential_complete_at_site` and
   `cocycle_iff_potential_at_site`.

So the sizes and potentials of a closure are relative absolutes without any classical principle:
the enumeration of a closure by the level group is a computation from the base site, not a choice
of representative.
-/

namespace NRRF783Bridge782

universe u

open NRRF782

variable {ι : Type u} {G : Type u} [AddCommGroup G]

/-! ## §1  The same notion of translational truth -/

/-- A Mathlib additive commutative group, read as the level data of the constructive
development. -/
def levels (G : Type u) [AddCommGroup G] : NRRF783T.AddGroupStr G where
  zero := 0
  add := (· + ·)
  neg := Neg.neg
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := add_zero
  add_neg := add_neg_cancel
  add_comm := add_comm

theorem transTruth_iff (x y : ι → G) :
    NRRF783T.TransTruth (levels G) x y ↔ NRRF782.TransTruth x y := Iff.rfl

theorem mem_closure_iff (x y : ι → G) :
    y ∈ NRRF782.Closure x ↔ NRRF783T.Closure (levels G) x y := Iff.rfl

/-! ## §2  The classical steps, removed -/

/-- **Overlapping closures are equal.**  This is the constructive content of NRRF782's
`closure_eq_or_disjoint`: the dichotomy has to decide translational truth, while what the
development uses is that a shared reading forces equality. -/
theorem closure_eq_of_overlap {x y z : ι → G} (hx : z ∈ NRRF782.Closure x)
    (hy : z ∈ NRRF782.Closure y) : NRRF782.Closure x = NRRF782.Closure y :=
  NRRF782.closure_eq_iff_transTruth.mpr (NRRF782.TransTruth.trans hx (NRRF782.TransTruth.symm hy))

/-- **The shift is unique**, with the site taken as data instead of extracted from `[Nonempty ι]`
by choice. -/
theorem shift_unique_at_site (i₀ : ι) {x y : ι → G} {k l : G} (hk : ∀ i, y i = x i + k)
    (hl : ∀ i, y i = x i + l) : k = l :=
  add_left_cancel (a := x i₀) ((hk i₀).symm.trans (hl i₀))

/-- **A computable enumeration of a closure by the level group.**  NRRF782's `closureEquiv` is
noncomputable: it extracts a site from `[Nonempty ι]` and a shift from an existential.  Given the
site as data, both directions are computations — encode by shifting, evaluate by reading the shift
off at the site — so the enumeration needs no choice at all. -/
def closureEquivOfSite (x : ι → G) (i₀ : ι) : G ≃ NRRF782.Closure x where
  toFun k := ⟨fun i => x i + k, ⟨k, fun _ => rfl⟩⟩
  invFun y := -x i₀ + y.val i₀
  left_inv k := by
    show -x i₀ + (x i₀ + k) = k
    rw [← add_assoc, neg_add_cancel, zero_add]
  right_inv y := by
    obtain ⟨y, k, hk⟩ := y
    have hval : (fun i => x i + (-x i₀ + y i₀)) = y := by
      funext i
      rw [hk i₀, hk i]
      abel
    exact Subtype.ext hval

@[simp] theorem closureEquivOfSite_apply (x : ι → G) (i₀ : ι) (k : G) :
    ((closureEquivOfSite x i₀) k).val = fun i => x i + k := rfl

/-- The base point is the neutral level. -/
@[simp] theorem closureEquivOfSite_zero (x : ι → G) (i₀ : ι) :
    ((closureEquivOfSite x i₀) 0).val = x := by
  funext i
  exact add_zero (x i)

/-- **Sizes are relative absolutes, computably**: any two closures over the same levels are
canonically isomorphic, by an isomorphism built from the site rather than chosen. -/
def closureIsoOfSite (x y : ι → G) (i₀ : ι) : NRRF782.Closure x ≃ NRRF782.Closure y :=
  (closureEquivOfSite x i₀).symm.trans (closureEquivOfSite y i₀)

/-- **Relative potentials determine the closure**, with the site as data. -/
theorem potential_complete_at_site (i₀ : ι) {x y : ι → G}
    (h : NRRF782.potential y = NRRF782.potential x) : NRRF782.TransTruth x y := by
  refine ⟨-x i₀ + y i₀, fun i => ?_⟩
  have hi : y i - y i₀ = x i - x i₀ := congrFun (congrFun h i) i₀
  have : y i = x i - x i₀ + y i₀ := by
    rw [← hi]
    abel
  rw [this]
  abel

/-- **The potentials are exactly the cocycles**, with the site as data: from a cocycle the reading
is *constructed* (`fun i => d i i₀`), not chosen. -/
theorem cocycle_iff_potential_at_site (i₀ : ι) (d : ι → ι → G) :
    NRRF782.Cocycle d ↔ ∃ x : ι → G, NRRF782.potential x = d := by
  constructor
  · intro hd
    refine ⟨fun i => d i i₀, ?_⟩
    funext i j
    show d i i₀ - d j i₀ = d i j
    have h1 : d i j + d j i₀ = d i i₀ := hd i j i₀
    rw [← h1]
    abel
  · rintro ⟨x, rfl⟩ i j k
    show (x i - x j) + (x j - x k) = x i - x k
    abel

/-- **The translational-truth strand of NRRF782, without classical logic.**  Closure equality is
translational truth; overlapping closures are equal; the shift is unique at any site; the closure
is computably enumerated by the level group, so any two closures are canonically isomorphic;
relative potentials are invariant on a closure, determine it, and are exactly the cocycles. -/
theorem nrrf782_answer_without_classical (x y : ι → G) (i₀ : ι) (d : ι → ι → G) :
    (NRRF782.Closure x = NRRF782.Closure y ↔ NRRF782.TransTruth x y) ∧
    (∀ z, z ∈ NRRF782.Closure x → z ∈ NRRF782.Closure y →
      NRRF782.Closure x = NRRF782.Closure y) ∧
    (∀ k l : G, (∀ i, y i = x i + k) → (∀ i, y i = x i + l) → k = l) ∧
    (∀ z ∈ NRRF782.Closure x, NRRF782.potential z = NRRF782.potential x) ∧
    (NRRF782.potential y = NRRF782.potential x → NRRF782.TransTruth x y) ∧
    (NRRF782.Cocycle d ↔ ∃ z : ι → G, NRRF782.potential z = d) :=
  ⟨NRRF782.closure_eq_iff_transTruth,
    fun _ hx hy => closure_eq_of_overlap hx hy,
    fun _ _ hk hl => shift_unique_at_site i₀ hk hl,
    fun _ hz => NRRF782.potential_invariant hz,
    fun h => potential_complete_at_site i₀ h,
    cocycle_iff_potential_at_site i₀ d⟩

end NRRF783Bridge782

/-! ## §3  Axiom audit -/

section Audit

/-! ### Already choice-free in NRRF782 -/

/-- info: 'NRRF782.closure_eq_iff_transTruth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms NRRF782.closure_eq_iff_transTruth

/-- info: 'NRRF782.exists_unique_closure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms NRRF782.exists_unique_closure

/-- info: 'NRRF782.potential_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms NRRF782.potential_invariant

/-- info: 'NRRF782.value_not_absolute' depends on axioms: [propext] -/
#guard_msgs in #print axioms NRRF782.value_not_absolute

/-! ### The classical steps of NRRF782 … -/

/-- info: 'NRRF782.closure_eq_or_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF782.closure_eq_or_disjoint

/-- info: 'NRRF782.shift_unique' depends on axioms: [Classical.choice] -/
#guard_msgs in #print axioms NRRF782.shift_unique

/-- info: 'NRRF782.closure_mk_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF782.closure_mk_eq

/-- info: 'NRRF782.potential_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF782.potential_complete

/-- info: 'NRRF782.cocycle_iff_potential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF782.cocycle_iff_potential

/-! ### … and their choice-free replacements -/

/-- info: 'NRRF783Bridge782.closure_eq_of_overlap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms NRRF783Bridge782.closure_eq_of_overlap

/-- info: 'NRRF783Bridge782.shift_unique_at_site' does not depend on any axioms -/
#guard_msgs in #print axioms NRRF783Bridge782.shift_unique_at_site

/-- info: 'NRRF783Bridge782.closureEquivOfSite' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms NRRF783Bridge782.closureEquivOfSite

/-- info: 'NRRF783Bridge782.closureIsoOfSite' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms NRRF783Bridge782.closureIsoOfSite

/-- info: 'NRRF783Bridge782.potential_complete_at_site' depends on axioms: [propext] -/
#guard_msgs in #print axioms NRRF783Bridge782.potential_complete_at_site

/-- info: 'NRRF783Bridge782.cocycle_iff_potential_at_site' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms NRRF783Bridge782.cocycle_iff_potential_at_site

/-- info: 'NRRF783Bridge782.nrrf782_answer_without_classical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms NRRF783Bridge782.nrrf782_answer_without_classical

end Audit
