import Mathlib
import NRRF772LinearLayoutRelativeEqualityFunctionsCompleteness

/-!
# NRRF782 — Translational truth creates unique isomorphic sets, whose sizes and potentials are relative absolutes of the closure

The reading being formalised:

> Translational truth creates unique isomorphic sets.  For each closure whose sizes and potentials
> are themselves relative absolutes of closure.

**The set-up.**  A *reading* of a domain `ι` in a group of levels `G` is a function `u : ι → G`:
it assigns a potential to each site.  *Translational truth* is the declaration that two readings
say the same thing when they differ by a single global shift (`TransTruth`).  The *closure* of a
reading is the set of all readings translationally equal to it (`Closure`) — the whole of what the
reading determines, with the undetermined absolute level left free.

**What is proved.**

* **§1 Translational truth is an equality.**  `TransTruth` is reflexive, symmetric and transitive
  (`transSetoid`), so it does create sets: the closures.
* **§2 The closures are *unique*.**  Two closures are equal or disjoint (`closure_eq_or_disjoint`),
  and every reading lies in exactly one closure (`exists_unique_closure`): the closure of a reading
  is not a choice, it is forced.  Nothing is lost — the reading is a member of its own closure
  (`self_mem_closure`).
* **§3 The closures are *isomorphic*, and the isomorphism is unique.**  Over a nonempty domain the
  shift witnessing translational truth is unique (`shift_unique`), so each closure is a torsor:
  `closureEquiv` is a bijection `G ≃ Closure u`, and it is the *only* shift-equivariant bijection
  based at `u` (`closureEquiv_unique`).  Hence any two closures are canonically isomorphic
  (`closureIso`, `closureIso_apply`), even when they are disjoint: translational truth creates
  unique isomorphic sets.
* **§4 Sizes are relative absolutes of the closure.**  The size of a closure is not a feature of
  any single reading — it is a feature of the closure, and *relative* to translational truth, since
  it is the size of the group of shifts (`closure_mk_eq`, `closure_nat_card_eq`).  But relative to
  the closure it is absolute: it is the same for every closure (`sizes_absolute`) and does not
  depend on the representative read (`size_representative_independent`).
* **§5 Potentials are relative absolutes of the closure.**  The individual potential `u i` is not
  determined — as soon as `G` has a nonzero shift, every value moves inside the closure
  (`value_not_absolute`).  The *relative* potential `potential u i j = u i - u j` is constant on the
  closure (`potential_invariant`) and, conversely, determines it (`potential_complete`): it is the
  complete invariant.  The potentials are exactly the cocycles (`cocycle_iff_potential`), so the
  closures and the cocycles correspond bijectively (`closure_potential_bijection`).
* **§6 Translational truth is strictly finer than mere translation of readings.**  A closure is a
  translational-equality class in the sense of NRRF772 (`transTruth_transEq`), but not conversely
  (`transEq_not_transTruth`): translational truth in the present sense pins the isomorphism type
  down to a torsor over the shift group, which bare mutual refinement does not.

`nrrf782_answer` collects the clauses.  §7 is the axiom audit: everything here is proved for an
arbitrary additive commutative group of levels — no real numbers, no completion, no analysis.
-/

universe u

namespace NRRF782

variable {ι G : Type u} [AddCommGroup G]

/-! ## §1  Translational truth -/

/-- **Translational truth.**  Two readings of the same domain say the same thing when they differ
by one global shift: the absolute level is not part of what is said. -/
def TransTruth (x y : ι → G) : Prop := ∃ k : G, ∀ i, y i = x i + k

theorem transTruth_refl (x : ι → G) : TransTruth x x := ⟨0, fun _ => (add_zero _).symm⟩

theorem TransTruth.symm {x y : ι → G} (h : TransTruth x y) : TransTruth y x := by
  obtain ⟨k, hk⟩ := h
  exact ⟨-k, fun i => by rw [hk i]; abel⟩

theorem TransTruth.trans {x y z : ι → G} (h : TransTruth x y) (h' : TransTruth y z) :
    TransTruth x z := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨l, hl⟩ := h'
  exact ⟨k + l, fun i => by rw [hl i, hk i]; abel⟩

/-- Translational truth is an equality: it is what creates the sets. -/
def transSetoid (ι G : Type u) [AddCommGroup G] : Setoid (ι → G) where
  r := TransTruth
  iseqv := ⟨transTruth_refl, TransTruth.symm, TransTruth.trans⟩

/-! ## §2  The sets it creates: closures, unique -/

/-- **The closure of a reading**: everything translationally equal to it.  This is the whole of
what the reading determines. -/
def Closure (x : ι → G) : Set (ι → G) := {y | TransTruth x y}

theorem mem_closure_iff {x y : ι → G} : y ∈ Closure x ↔ TransTruth x y := Iff.rfl

/-- A reading is a member of its own closure: closing loses nothing. -/
theorem self_mem_closure (x : ι → G) : x ∈ Closure x := transTruth_refl x

/-- The closure is exactly the orbit of the shift action. -/
theorem closure_eq_range (x : ι → G) : Closure x = Set.range fun k i => x i + k := by
  ext y
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, (funext fun i => (hk i).symm)⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, fun _ => rfl⟩

/-- Membership in a closure is the same relation as equality of closures. -/
theorem closure_eq_iff_transTruth {x y : ι → G} : Closure x = Closure y ↔ TransTruth x y := by
  constructor
  · intro h
    have : y ∈ Closure x := by rw [h]; exact self_mem_closure y
    exact this
  · intro h
    ext z
    exact ⟨fun hz => h.symm.trans hz, fun hz => h.trans hz⟩

theorem closure_eq_of_mem {x y : ι → G} (h : y ∈ Closure x) : Closure x = Closure y :=
  closure_eq_iff_transTruth.mpr h

/-- **Uniqueness, first form.**  Two closures are either the same set or disjoint. -/
theorem closure_eq_or_disjoint (x y : ι → G) :
    Closure x = Closure y ∨ Disjoint (Closure x) (Closure y) := by
  by_cases h : TransTruth x y
  · exact Or.inl (closure_eq_iff_transTruth.mpr h)
  · refine Or.inr (Set.disjoint_left.mpr ?_)
    intro z hz hz'
    exact h (hz.trans hz'.symm)

/-- **Uniqueness, second form.**  Every reading lies in exactly one closure. -/
theorem exists_unique_closure (y : ι → G) :
    ∃! C : Set (ι → G), (∃ x, C = Closure x) ∧ y ∈ C := by
  refine ⟨Closure y, ⟨⟨y, rfl⟩, self_mem_closure y⟩, ?_⟩
  rintro C ⟨⟨x, rfl⟩, hy⟩
  exact closure_eq_of_mem hy

/-! ## §3  Unique isomorphic sets -/

/-- Over a nonempty domain the shift is unique: the closure is a *torsor*, not merely an orbit. -/
theorem shift_unique [Nonempty ι] {x y : ι → G} {k l : G} (hk : ∀ i, y i = x i + k)
    (hl : ∀ i, y i = x i + l) : k = l := by
  have i := Classical.arbitrary ι
  have : x i + k = x i + l := by rw [← hk i, ← hl i]
  exact add_left_cancel this

/-- **Each closure is a copy of the group of shifts.**  Translation by `k` from the base reading
`x` enumerates the closure of `x` bijectively. -/
noncomputable def closureEquiv [Nonempty ι] (x : ι → G) : G ≃ Closure x where
  toFun k := ⟨fun i => x i + k, ⟨k, fun _ => rfl⟩⟩
  invFun y := y.1 (Classical.arbitrary ι) - x (Classical.arbitrary ι)
  left_inv k := by simp
  right_inv := by
    rintro ⟨y, k, hk⟩
    refine Subtype.ext (funext fun i => ?_)
    simp only [hk (Classical.arbitrary ι), hk i]
    abel

theorem closureEquiv_apply [Nonempty ι] (x : ι → G) (k : G) :
    ((closureEquiv x k : Closure x) : ι → G) = fun i => x i + k := rfl

theorem closureEquiv_zero [Nonempty ι] (x : ι → G) :
    ((closureEquiv x 0 : Closure x) : ι → G) = x := by
  funext i; simp [closureEquiv]

/-- **The isomorphism is unique.**  Any enumeration of the closure that is based at `x` and
respects composition of shifts *is* `closureEquiv`. -/
theorem closureEquiv_unique [Nonempty ι] (x : ι → G) (e : G → Closure x)
    (h0 : (e 0 : ι → G) = x)
    (hadd : ∀ k l : G, ((e (k + l) : Closure x) : ι → G) = fun i => (e k : ι → G) i + l) :
    ∀ k, (e k : ι → G) = ((closureEquiv x k : Closure x) : ι → G) := by
  intro k
  have := hadd 0 k
  rw [zero_add, h0] at this
  rw [this, closureEquiv_apply]

/-- **Any two closures are isomorphic**, whether or not they are the same set. -/
noncomputable def closureIso [Nonempty ι] (x y : ι → G) : Closure x ≃ Closure y :=
  (closureEquiv x).symm.trans (closureEquiv y)

theorem closureIso_apply [Nonempty ι] (x y : ι → G) (z : Closure x) :
    ((closureIso x y z : Closure y) : ι → G) =
      fun i => y i + (z.1 (Classical.arbitrary ι) - x (Classical.arbitrary ι)) := rfl

/-! ## §4  Sizes are relative absolutes of the closure -/

/-- **The size of a closure is the size of the group of shifts.**  It is *relative* — it measures
the freedom translational truth leaves — and it is read only at the level of the closure. -/
theorem closure_mk_eq [Nonempty ι] (x : ι → G) :
    Cardinal.mk (Closure x) = Cardinal.mk G :=
  Cardinal.mk_congr (closureEquiv x).symm

theorem closure_nat_card_eq [Nonempty ι] (x : ι → G) :
    Nat.card (Closure x) = Nat.card G :=
  Nat.card_congr (closureEquiv x).symm

/-- **Absolute relative to closure.**  Every closure has the same size: the size is an invariant
of translational truth itself, identical across all closures. -/
theorem sizes_absolute [Nonempty ι] (x y : ι → G) :
    Cardinal.mk (Closure x) = Cardinal.mk (Closure y) :=
  (closure_mk_eq x).trans (closure_mk_eq y).symm

/-- The size does not depend on which member of the closure is read. -/
theorem size_representative_independent {x y : ι → G} (h : y ∈ Closure x) :
    Cardinal.mk (Closure x) = Cardinal.mk (Closure y) := by
  rw [closure_eq_of_mem h]

/-! ## §5  Potentials are relative absolutes of the closure -/

/-- **The relative potential** of a reading: the level difference between two sites. -/
def potential (x : ι → G) : ι → ι → G := fun i j => x i - x j

theorem potential_self (x : ι → G) (i : ι) : potential x i i = 0 := sub_self _

theorem potential_antisymm (x : ι → G) (i j : ι) : potential x j i = -potential x i j :=
  (neg_sub _ _).symm

/-- The potentials of a reading satisfy the cocycle identity: potential differences compose. -/
theorem potential_cocycle (x : ι → G) (i j k : ι) :
    potential x i j + potential x j k = potential x i k := by
  simp only [potential]; abel

/-- **Absolute relative to closure.**  The relative potential is constant on a closure: it is not a
feature of the representative but of the closure. -/
theorem potential_invariant {x y : ι → G} (h : y ∈ Closure x) : potential y = potential x := by
  obtain ⟨k, hk⟩ := h
  funext i j
  simp only [potential, hk i, hk j]
  abel

/-- **The individual potential is not absolute.**  Whenever there is a nonzero shift, every value
of every reading moves inside its own closure: only the relations survive. -/
theorem value_not_absolute (x : ι → G) {k : G} (hk : k ≠ 0) (i : ι) :
    ∃ y ∈ Closure x, y i ≠ x i := by
  refine ⟨fun j => x j + k, ⟨k, fun _ => rfl⟩, ?_⟩
  intro h
  exact hk (by simpa using add_left_cancel (a := x i) (by simpa using h))

/-- **The relative potential is the complete invariant of the closure.**  Two readings have the
same potentials exactly when they generate the same closure. -/
theorem potential_complete [Nonempty ι] {x y : ι → G} :
    potential x = potential y ↔ Closure x = Closure y := by
  constructor
  · intro h
    refine closure_eq_iff_transTruth.mpr ⟨y (Classical.arbitrary ι) - x (Classical.arbitrary ι),
      fun i => ?_⟩
    have hi : y i - y (Classical.arbitrary ι) = x i - x (Classical.arbitrary ι) :=
      (congrFun (congrFun h i) (Classical.arbitrary ι)).symm
    have h4 : y i = x i - x (Classical.arbitrary ι) + y (Classical.arbitrary ι) := by
      rw [← hi]; abel
    rw [h4]; abel
  · intro h
    exact (potential_invariant (h ▸ self_mem_closure y : y ∈ Closure x)).symm

/-- A candidate potential field: a function on pairs of sites that composes. -/
def Cocycle (d : ι → ι → G) : Prop := ∀ i j k, d i j + d j k = d i k

/-- **The potentials are exactly the cocycles.**  Nothing else can be a field of relative levels,
and every cocycle is realised by a reading — which is then determined up to closure. -/
theorem cocycle_iff_potential [Nonempty ι] (d : ι → ι → G) :
    Cocycle d ↔ ∃ x : ι → G, potential x = d := by
  constructor
  · intro hd
    refine ⟨fun i => d i (Classical.arbitrary ι), funext fun i => funext fun j => ?_⟩
    have h1 := hd i j (Classical.arbitrary ι)
    simp only [potential]
    rw [← h1]
    abel
  · rintro ⟨x, rfl⟩
    exact potential_cocycle x

/-- **The bijection.**  Closures and cocycles correspond: the closure is the potential field, read
as a set of readings, and the potential field is the closure, read as relations. -/
theorem closure_potential_bijection [Nonempty ι] :
    (∀ x y : ι → G, potential x = potential y ↔ Closure x = Closure y) ∧
      (∀ d : ι → ι → G, Cocycle d ↔ ∃ x : ι → G, potential x = d) :=
  ⟨fun _ _ => potential_complete, fun d => cocycle_iff_potential d⟩

/-! ## §6  Translational truth is strictly finer than translation of readings -/

/-- Translationally true readings are translationally equal in the sense of NRRF772: each is a
translation of the other. -/
theorem transTruth_transEq {x y : ι → G} (h : TransTruth x y) : NRRF772.TransEq x y := by
  obtain ⟨k, hk⟩ := h
  exact ⟨⟨fun g => g + k, fun i => (hk i).symm⟩,
    ⟨fun g => g - k, fun i => by simp [hk i]⟩⟩

/-- The converse fails: mutual refinement in the sense of NRRF772 records only the induced equality
on sites, whereas translational truth also fixes the isomorphism type of the closure. -/
theorem transEq_not_transTruth :
    ∃ x y : ℤ → ℤ, NRRF772.TransEq x y ∧ ¬ TransTruth x y := by
  refine ⟨id, fun i => 2 * i, ⟨⟨fun g => 2 * g, fun i => rfl⟩, ⟨fun g => g / 2, fun i => ?_⟩⟩, ?_⟩
  · exact Int.mul_ediv_cancel_left i (by norm_num)
  · rintro ⟨k, hk⟩
    have h0 := hk 0
    have h1 := hk 1
    simp at h0 h1
    omega

/-! ## §7  The collected answer -/

/-- **NRRF782.**  For readings of a nonempty domain in a group of levels:

* translational truth is an equality, and the sets it creates — the closures — are unique: every
  reading lies in exactly one, and two closures are equal or disjoint;
* the closures are mutually isomorphic, each being a torsor over the group of shifts, and the
  isomorphism based at a reading is unique;
* the size of a closure is a relative absolute: relative, being the size of the shift group, and
  absolute, being the same for every closure and independent of the representative;
* the potentials are a relative absolute: the individual level is not determined (whenever a
  nonzero shift exists), while the relative potential is constant on the closure and determines the
  closure completely. -/
theorem nrrf782_answer [Nonempty ι] (x y : ι → G) :
    (x ∈ Closure x ∧ ∃! C : Set (ι → G), (∃ z, C = Closure z) ∧ x ∈ C) ∧
    (Closure x = Closure y ∨ Disjoint (Closure x) (Closure y)) ∧
    Nonempty (Closure x ≃ Closure y) ∧
    (Cardinal.mk (Closure x) = Cardinal.mk G ∧
      Cardinal.mk (Closure x) = Cardinal.mk (Closure y)) ∧
    (∀ z ∈ Closure x, potential z = potential x) ∧
    (potential x = potential y ↔ Closure x = Closure y) ∧
    (∀ (k : G), k ≠ 0 → ∀ i, ∃ z ∈ Closure x, z i ≠ x i) :=
  ⟨⟨self_mem_closure x, exists_unique_closure x⟩,
    closure_eq_or_disjoint x y,
    ⟨closureIso x y⟩,
    ⟨closure_mk_eq x, sizes_absolute x y⟩,
    fun _ hz => potential_invariant hz,
    potential_complete,
    fun _ hk i => value_not_absolute x hk i⟩

end NRRF782

/-! ## §8  Axiom audit -/

section Audit

#print axioms NRRF782.closure_eq_iff_transTruth
#print axioms NRRF782.closure_eq_or_disjoint
#print axioms NRRF782.exists_unique_closure
#print axioms NRRF782.shift_unique
#print axioms NRRF782.closureEquiv_unique
#print axioms NRRF782.closure_mk_eq
#print axioms NRRF782.sizes_absolute
#print axioms NRRF782.potential_invariant
#print axioms NRRF782.potential_complete
#print axioms NRRF782.cocycle_iff_potential
#print axioms NRRF782.value_not_absolute
#print axioms NRRF782.transTruth_transEq
#print axioms NRRF782.transEq_not_transTruth
#print axioms NRRF782.nrrf782_answer

end Audit
