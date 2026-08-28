import NRRF802UnifyClosure

/-!
# NRRF803 — Trajectory and basis are defined, and mean, relative to their external forms of natural equality

The instruction formalised here is the user's:

> trajectory and basis are defined and mean relative to their external forms of natural equality

A system here is a type `X` with a return `step : X → X`.  A **form of equality** on `X` is a
setoid `E`; it is *external* in the sense that it is not part of the data `(X, step)` — it is
supplied from outside, and different choices are possible for the same system.  A form of equality
is **natural** for the return when the return does not move it: `x ≈ step x`.

Relative to such an external form the two notions of this module are defined:

* the **trajectory** of `x` is the set of classes visited by the forward orbit of `x`,
  `Traj step E x = ⟦·⟧ '' {step^[n] x | n}`;
* a **basis** for `E` is a family `b : I → X` which spans (every point is `E`-equal to some `b i`)
  and is independent (distinct indices give `E`-distinct points).

Neither notion is available before a form of equality has been fixed, and neither depends on
anything else: both are functions of the relation `E` alone.  That is what is proved.

## What is proved

### §1  Forms of natural equality
`IsNatural`, `natural_returnSetoid` (the closure of NRRF802 is a natural equality),
`natural_iterate` (a natural equality is blind to every number of returns), `returnSetoid_finest`
(the closure equality is the *finest* natural equality), `factor`/`factor_cl` (hence every external
form of natural equality is a quotient of the closure).

### §2  Trajectory is relative to the external form
`mem_traj`, `sameTraj_iff` (the relational and set forms agree), `traj_natural` (relative to a
natural equality every trajectory is a single point), `traj_congr`, `sameTraj_congr_setoid`
(sameness of trajectory depends on the external form and on nothing else), `traj_not_absolute`
(two points with the same trajectory relative to one form and different trajectories relative to
another), `traj_factor` (the trajectory relative to any natural form is the image of the
trajectory relative to the closure).

### §3  Basis is relative to the external form
`IsBasis`, `isBasis_iff_bijective` (a basis is exactly an indexing of the quotient),
`isBasis_congr_setoid` (being a basis depends on the external form and on nothing else),
`basis_congr` (a basis stays a basis when its vectors are moved within their classes),
`exists_basis` (every external form has a basis), `basis_equiv_quotient`,
`basis_unique_up_to_reindex` (any two bases for the same form are matched by a *unique*
reindexing), `basis_not_absolute` (a family that is a basis for one natural form and not for
another on the same system), `isBasis_iff_factor_bijective` (a basis relative to any natural form,
read through the closure).

### §4  `nrrf803_answer` collects the clauses; the axiom audit at the end is machine-checked.

Nothing is asserted beyond the definitions made here and in NRRF802: each claim is a claim about
those definitions.
-/

namespace NRRF803

open NRRF802

universe u v w

/-! ## §1  Forms of natural equality -/

section Natural

variable {X : Type u}

/-- A form of equality `E` is **natural** for the return `step` when the return does not move it:
each point is `E`-equal to its return.  Naturality is the only condition tying an external form of
equality to the system it is used on. -/
def IsNatural (step : X → X) (E : Setoid X) : Prop := ∀ x, E.r x (step x)

/-- The translational completion of the return — the closure equality of NRRF802 — is a natural
form of equality. -/
theorem natural_returnSetoid (step : X → X) : IsNatural step (returnSetoid step) :=
  fun x => Relation.EqvGen.rel _ _ (rfl : step x = step x)

/-- A natural form of equality is blind to any number of returns. -/
theorem natural_iterate {step : X → X} {E : Setoid X} (hE : IsNatural step E) :
    ∀ (n : ℕ) (x : X), E.r x (step^[n] x) := by
  intro n
  induction n with
  | zero => intro x; simpa using E.iseqv.refl x
  | succ n ih =>
      intro x
      have h₁ : E.r x (step^[n] x) := ih x
      have h₂ : E.r (step^[n] x) (step (step^[n] x)) := hE _
      have h₃ : E.r x (step (step^[n] x)) := E.iseqv.trans h₁ h₂
      have he : step^[n + 1] x = step (step^[n] x) := Function.iterate_succ_apply' step n x
      rw [he]
      exact h₃

/-- The closure equality is the **finest** natural form of equality: every natural form of equality
identifies at least the points it identifies. -/
theorem returnSetoid_finest {step : X → X} {E : Setoid X} (hE : IsNatural step E) :
    ∀ x y, (returnSetoid step).r x y → E.r x y := by
  intro x y h
  induction h with
  | rel a b hab => exact hab ▸ hE a
  | refl a => exact E.iseqv.refl a
  | symm a b _ ih => exact E.iseqv.symm ih
  | trans a b c _ _ ih₁ ih₂ => exact E.iseqv.trans ih₁ ih₂

/-- Every external form of natural equality is a quotient of the closure: the canonical factoring
map from the closure of the return onto the quotient by the form. -/
def factor {step : X → X} {E : Setoid X} (hE : IsNatural step E) :
    Closure step → Quotient E :=
  Quotient.lift (Quotient.mk E) (fun a b hab => Quotient.sound (returnSetoid_finest hE a b hab))

@[simp] theorem factor_cl {step : X → X} {E : Setoid X} (hE : IsNatural step E) (x : X) :
    factor hE (cl step x) = Quotient.mk E x := rfl

end Natural

/-! ## §2  Trajectory relative to an external form of natural equality -/

section Trajectory

variable {X : Type u}

/-- The forward orbit of a point under the return. -/
def Orbit (step : X → X) (x : X) : Set X := {y | ∃ n : ℕ, y = step^[n] x}

/-- The **trajectory** of `x` relative to the external form of equality `E`: the set of `E`-classes
visited by the forward orbit.  With no form of equality fixed there is no trajectory. -/
def Traj (step : X → X) (E : Setoid X) (x : X) : Set (Quotient E) :=
  Quotient.mk E '' Orbit step x

theorem mem_traj {step : X → X} {E : Setoid X} {x : X} {q : Quotient E} :
    q ∈ Traj step E x ↔ ∃ n : ℕ, q = Quotient.mk E (step^[n] x) := by
  constructor
  · rintro ⟨y, ⟨n, rfl⟩, rfl⟩; exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩; exact ⟨step^[n] x, ⟨n, rfl⟩, rfl⟩

theorem self_mem_traj (step : X → X) (E : Setoid X) (x : X) :
    Quotient.mk E x ∈ Traj step E x := mem_traj.2 ⟨0, rfl⟩

/-- Sameness of trajectory, stated purely in terms of the relation `E`. -/
def SameTraj (step : X → X) (E : Setoid X) (x y : X) : Prop :=
  ∀ z : X, (∃ n : ℕ, E.r z (step^[n] x)) ↔ (∃ n : ℕ, E.r z (step^[n] y))

/-- The relational and the set-theoretic readings of "same trajectory" agree. -/
theorem sameTraj_iff {step : X → X} {E : Setoid X} {x y : X} :
    SameTraj step E x y ↔ Traj step E x = Traj step E y := by
  constructor
  · intro h
    ext q
    induction q using Quotient.ind with
    | _ z =>
      constructor
      · intro hq
        obtain ⟨n, hn⟩ := mem_traj.1 hq
        obtain ⟨m, hm⟩ := (h z).1 ⟨n, Quotient.exact hn⟩
        exact mem_traj.2 ⟨m, Quotient.sound hm⟩
      · intro hq
        obtain ⟨n, hn⟩ := mem_traj.1 hq
        obtain ⟨m, hm⟩ := (h z).2 ⟨n, Quotient.exact hn⟩
        exact mem_traj.2 ⟨m, Quotient.sound hm⟩
  · intro h z
    constructor
    · rintro ⟨n, hn⟩
      have : Quotient.mk E z ∈ Traj step E x := mem_traj.2 ⟨n, Quotient.sound hn⟩
      obtain ⟨m, hm⟩ := mem_traj.1 (h ▸ this)
      exact ⟨m, Quotient.exact hm⟩
    · rintro ⟨n, hn⟩
      have : Quotient.mk E z ∈ Traj step E y := mem_traj.2 ⟨n, Quotient.sound hn⟩
      obtain ⟨m, hm⟩ := mem_traj.1 (h ▸ this)
      exact ⟨m, Quotient.exact hm⟩

/-- **Relative to a natural form of equality every trajectory is a single point.**  What the
trajectory of a point *is* therefore depends entirely on the external form of equality used to read
it. -/
theorem traj_natural {step : X → X} {E : Setoid X} (hE : IsNatural step E) (x : X) :
    Traj step E x = {Quotient.mk E x} := by
  ext q
  constructor
  · intro hq
    obtain ⟨n, hn⟩ := mem_traj.1 hq
    exact hn.trans (Quotient.sound (E.iseqv.symm (natural_iterate hE n x)))
  · intro hq
    rw [Set.mem_singleton_iff] at hq
    exact hq ▸ self_mem_traj step E x

/-- Relative to a natural form of equality, `E`-equal points have the same trajectory. -/
theorem traj_congr {step : X → X} {E : Setoid X} (hE : IsNatural step E) {x y : X}
    (hxy : E.r x y) : Traj step E x = Traj step E y := by
  rw [traj_natural hE, traj_natural hE, Quotient.sound hxy]

/-- **Sameness of trajectory depends on the external form of equality and on nothing else**: two
forms with the same relation give the same trajectories, whatever else distinguishes them. -/
theorem sameTraj_congr_setoid {step : X → X} {E₁ E₂ : Setoid X}
    (h : ∀ a b, E₁.r a b ↔ E₂.r a b) (x y : X) :
    SameTraj step E₁ x y ↔ SameTraj step E₂ x y := by
  constructor
  · intro hs z
    constructor
    · rintro ⟨n, hn⟩
      obtain ⟨m, hm⟩ := (hs z).1 ⟨n, (h _ _).2 hn⟩
      exact ⟨m, (h _ _).1 hm⟩
    · rintro ⟨n, hn⟩
      obtain ⟨m, hm⟩ := (hs z).2 ⟨n, (h _ _).2 hn⟩
      exact ⟨m, (h _ _).1 hm⟩
  · intro hs z
    constructor
    · rintro ⟨n, hn⟩
      obtain ⟨m, hm⟩ := (hs z).1 ⟨n, (h _ _).1 hn⟩
      exact ⟨m, (h _ _).2 hm⟩
    · rintro ⟨n, hn⟩
      obtain ⟨m, hm⟩ := (hs z).2 ⟨n, (h _ _).1 hn⟩
      exact ⟨m, (h _ _).2 hm⟩

/-- The trajectory relative to any natural external form is the image, under the canonical
factoring map, of the trajectory relative to the closure: the closure trajectory carries all the
information, the external form only reads it. -/
theorem traj_factor {step : X → X} {E : Setoid X} (hE : IsNatural step E) (x : X) :
    factor hE '' Traj step (returnSetoid step) x = Traj step E x := by
  rw [traj_natural (natural_returnSetoid step), traj_natural hE]
  change factor hE '' ({cl step x} : Set (Closure step)) = {Quotient.mk E x}
  rw [Set.image_singleton, factor_cl]

/-- **Trajectory is not absolute.**  On the naturals with the successor return, `0` and `1` have the
same trajectory relative to the translational (natural) form of equality, and different
trajectories relative to bare equality. -/
theorem traj_not_absolute :
    SameTraj Nat.succ (returnSetoid Nat.succ) 0 1 ∧
      ¬ SameTraj Nat.succ (⊥ : Setoid ℕ) 0 1 := by
  constructor
  · have h01 : (returnSetoid Nat.succ).r 0 1 := Relation.EqvGen.rel _ _ (rfl : (1 : ℕ) = Nat.succ 0)
    exact sameTraj_iff.2 (traj_congr (natural_returnSetoid Nat.succ) h01)
  · intro h
    obtain ⟨n, hn⟩ := (h 0).1 ⟨0, rfl⟩
    have h0 : (0 : ℕ) = 1 + n := by simpa [Nat.succ_iterate] using hn
    exact Nat.zero_ne_add_one n (by simpa [Nat.add_comm] using h0)

end Trajectory

/-! ## §3  Basis relative to an external form of natural equality -/

section Basis

variable {X : Type u}

/-- A **basis** for the external form of equality `E`: a family that spans (every point is `E`-equal
to a member) and is independent (distinct indices are `E`-distinct).  As with the trajectory, the
notion is not available until a form of equality has been fixed. -/
structure IsBasis (E : Setoid X) {I : Type v} (b : I → X) : Prop where
  spans : ∀ x : X, ∃ i, E.r (b i) x
  independent : ∀ i j, E.r (b i) (b j) → i = j

/-- A basis for `E` is exactly an indexing of the quotient by `E`. -/
theorem isBasis_iff_bijective {E : Setoid X} {I : Type v} (b : I → X) :
    IsBasis E b ↔ Function.Bijective (fun i => Quotient.mk E (b i)) := by
  constructor
  · intro hb
    refine ⟨fun i j hij => hb.independent i j (Quotient.exact hij), ?_⟩
    intro q
    induction q using Quotient.ind with
    | _ x =>
      obtain ⟨i, hi⟩ := hb.spans x
      exact ⟨i, Quotient.sound hi⟩
  · intro hb
    refine ⟨fun x => ?_, fun i j hij => hb.1 (Quotient.sound hij)⟩
    obtain ⟨i, hi⟩ := hb.2 (Quotient.mk E x)
    exact ⟨i, Quotient.exact hi⟩

/-- **Being a basis depends on the external form of equality and on nothing else**: two forms with
the same relation have exactly the same bases. -/
theorem isBasis_congr_setoid {E₁ E₂ : Setoid X} (h : ∀ a b, E₁.r a b ↔ E₂.r a b)
    {I : Type v} (b : I → X) : IsBasis E₁ b ↔ IsBasis E₂ b := by
  constructor
  · intro hb
    exact ⟨fun x => (hb.spans x).imp fun _ hi => (h _ _).1 hi,
      fun i j hij => hb.independent i j ((h _ _).2 hij)⟩
  · intro hb
    exact ⟨fun x => (hb.spans x).imp fun _ hi => (h _ _).2 hi,
      fun i j hij => hb.independent i j ((h _ _).1 hij)⟩

/-- A basis is only ever a basis up to the external equality: moving each vector inside its own
class leaves a basis. -/
theorem basis_congr {E : Setoid X} {I : Type v} {b c : I → X} (hb : IsBasis E b)
    (hbc : ∀ i, E.r (b i) (c i)) : IsBasis E c where
  spans := fun x => (hb.spans x).imp fun i hi => E.iseqv.trans (E.iseqv.symm (hbc i)) hi
  independent := fun i j hij =>
    hb.independent i j (E.iseqv.trans (hbc i) (E.iseqv.trans hij (E.iseqv.symm (hbc j))))

/-- Every external form of equality has a basis. -/
theorem exists_basis (E : Setoid X) : ∃ b : Quotient E → X, IsBasis E b := by
  refine ⟨Quotient.out, (isBasis_iff_bijective _).2 ?_⟩
  have : (fun q : Quotient E => Quotient.mk E (Quotient.out q)) = id := by
    funext q; simp
  rw [this]
  exact Function.bijective_id

/-- The indexing of a basis is the quotient by the external form: the "size" of a basis is a
property of the form of equality, not of the system. -/
noncomputable def basis_equiv_quotient {E : Setoid X} {I : Type v} {b : I → X}
    (hb : IsBasis E b) : I ≃ Quotient E :=
  Equiv.ofBijective _ ((isBasis_iff_bijective b).1 hb)

@[simp] theorem basis_equiv_quotient_apply {E : Setoid X} {I : Type v} {b : I → X}
    (hb : IsBasis E b) (i : I) : basis_equiv_quotient hb i = Quotient.mk E (b i) := rfl

/-- Any two bases for the same external form are matched by **exactly one** reindexing. -/
theorem basis_unique_up_to_reindex {E : Setoid X} {I : Type v} {J : Type v} {b : I → X} {c : J → X}
    (hb : IsBasis E b) (hc : IsBasis E c) :
    ∃! σ : I ≃ J, ∀ i, E.r (b i) (c (σ i)) := by
  have key : ∀ i : I, E.r (b i)
      (c (((basis_equiv_quotient hb).trans (basis_equiv_quotient hc).symm) i)) := by
    intro i
    exact Quotient.exact
      ((basis_equiv_quotient hc).apply_symm_apply (Quotient.mk E (b i))).symm
  refine ⟨(basis_equiv_quotient hb).trans (basis_equiv_quotient hc).symm, key, ?_⟩
  intro τ hτ
  apply Equiv.ext
  intro i
  exact (hc.independent _ _ (E.iseqv.trans (E.iseqv.symm (key i)) (hτ i))).symm

/-- **Basis is not absolute.**  On the two-point system with the identity return, both bare equality
and total equality are natural forms; the identity family is a basis for the first and not for the
second. -/
theorem basis_not_absolute :
    IsNatural (id : Bool → Bool) (⊥ : Setoid Bool) ∧
      IsNatural (id : Bool → Bool) (⊤ : Setoid Bool) ∧
      IsBasis (⊥ : Setoid Bool) (id : Bool → Bool) ∧
      ¬ IsBasis (⊤ : Setoid Bool) (id : Bool → Bool) := by
  refine ⟨fun _ => rfl, fun _ => trivial, ⟨fun x => ⟨x, rfl⟩, fun i j hij => hij⟩, ?_⟩
  intro h
  exact absurd (h.independent true false trivial) (by simp)

/-- A basis relative to any natural external form, read through the closure: the family is a basis
exactly when its closure classes, pushed along the canonical factoring map, index the quotient. -/
theorem isBasis_iff_factor_bijective {step : X → X} {E : Setoid X} (hE : IsNatural step E)
    {I : Type v} (b : I → X) :
    IsBasis E b ↔ Function.Bijective (fun i => factor hE (cl step (b i))) := by
  simpa using isBasis_iff_bijective (E := E) b

end Basis

/-! ## §4  The answer -/

/-- **Trajectory and basis are defined, and mean, relative to their external forms of natural
equality.**

1. The closure of the return is a natural form of equality, and the finest one: every natural
   external form is a quotient of it, by a map commuting with the class maps.
2. Relative to a natural form, the trajectory of a point is a single point — what a trajectory *is*
   is a function of the form of equality used to read it.
3. Sameness of trajectory, and being a basis, depend on the external form and on nothing else: two
   forms with the same relation give the same answers.
4. Neither notion is absolute: there are points with the same trajectory for one form and different
   trajectories for another, and a family that is a basis for one natural form and not for another
   on the same system.
5. Every external form has a basis, any two bases for one form are matched by exactly one
   reindexing, and a basis stays a basis when its vectors move inside their classes — so a basis is
   determined by, and only up to, the external form. -/
theorem nrrf803_answer :
    (∀ (X : Type) (step : X → X), IsNatural step (returnSetoid step)) ∧
    (∀ (X : Type) (step : X → X) (E : Setoid X) (hE : IsNatural step E) (x : X),
        factor hE (cl step x) = Quotient.mk E x) ∧
    (∀ (X : Type) (step : X → X) (E : Setoid X), IsNatural step E →
        ∀ x : X, Traj step E x = {Quotient.mk E x}) ∧
    (∀ (X : Type) (step : X → X) (E₁ E₂ : Setoid X), (∀ a b, E₁.r a b ↔ E₂.r a b) →
        (∀ x y : X, SameTraj step E₁ x y ↔ SameTraj step E₂ x y) ∧
        (∀ (I : Type) (b : I → X), IsBasis E₁ b ↔ IsBasis E₂ b)) ∧
    (SameTraj Nat.succ (returnSetoid Nat.succ) 0 1 ∧ ¬ SameTraj Nat.succ (⊥ : Setoid ℕ) 0 1) ∧
    (IsBasis (⊥ : Setoid Bool) (id : Bool → Bool) ∧
      ¬ IsBasis (⊤ : Setoid Bool) (id : Bool → Bool)) ∧
    (∀ (X : Type) (E : Setoid X), ∃ b : Quotient E → X, IsBasis E b) ∧
    (∀ (X : Type) (E : Setoid X) (I J : Type) (b : I → X) (c : J → X),
        IsBasis E b → IsBasis E c → ∃! σ : I ≃ J, ∀ i, E.r (b i) (c (σ i))) := by
  refine ⟨fun X step => natural_returnSetoid step, fun X step E hE x => factor_cl hE x,
    fun X step E hE x => traj_natural hE x,
    fun X step E₁ E₂ h => ⟨fun x y => sameTraj_congr_setoid h x y,
      fun I b => isBasis_congr_setoid h b⟩,
    traj_not_absolute,
    ⟨basis_not_absolute.2.2.1, basis_not_absolute.2.2.2⟩,
    fun X E => exists_basis E,
    fun X E I J b c hb hc => basis_unique_up_to_reindex hb hc⟩

end NRRF803

/-! ## Axiom audit -/

#print axioms NRRF803.nrrf803_answer
#print axioms NRRF803.traj_natural
#print axioms NRRF803.basis_unique_up_to_reindex
#print axioms NRRF803.traj_not_absolute
#print axioms NRRF803.basis_not_absolute
