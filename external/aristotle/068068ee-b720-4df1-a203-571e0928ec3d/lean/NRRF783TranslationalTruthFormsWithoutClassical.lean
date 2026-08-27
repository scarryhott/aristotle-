import NRRF783AxiometricFormsUnifiedWithoutClassical

/-!
# NRRF783c — The translational-truth forms, without classical logic, and their unification with
the closure equations

The development's axiometric forms come in two strands.  The first — the closure equations
`encode`/`eval` — is carried through constructively in
`NRRF783AxiometricFormsUnifiedWithoutClassical`.  The second is **translational truth**: two
readings of a domain are the same truth when they differ by one global shift of level, and the
*closure* of a reading is the set of readings translationally true to it (NRRF781/NRRF782).  This
module carries that strand through constructively too, and then **joins the two strands**: a
translational closure *is* an axiometric form of the first strand, and it is a form that closes.

The only import is the constructive core, which itself imports nothing, so no library — and hence
no classical principle — is in scope here either.  The group of levels is axiomatised by hand
(`AddGroupStr`) rather than taken from a library, for the same reason.

## What is proved

* §1  levels: an additive commutative group given as data, with the arithmetic needed below.
* §2  translational truth is reflexive, symmetric and transitive, and a reading lies in its own
  closure — constructively (`transTruth_refl`, `transTruth_symm`, `transTruth_trans`,
  `mem_closure_self`).
* §3  the closures are unique: overlapping closures are equal (`closure_eq_of_overlap`), which is
  the constructive content of "equal or disjoint" — the classical dichotomy would have to decide
  translational truth, and is never needed.  Closure equality *is* translational truth
  (`closure_eq_iff_transTruth`).
* §4  the shift is unique on an inhabited domain (`shift_unique`), relative potentials are
  invariant on a closure (`potential_invariant`) and determine it (`potential_complete`), while
  individual levels are not absolute (`value_not_absolute`).
* §5  **the unification of the two strands**: for an inhabited domain, the closure of a reading is
  the carrier of an axiometric form `closureForm` whose encoding is the shift action and whose
  evaluation reads the shift off at the base site; the form *closes* (`closureForm_closes`), so a
  translational closure is a transparent form in the sense of the closure equations, and the level
  group is exactly its encoded carrier.  Extracting the shift is done by the form, not chosen.
* §6  the machine-checked axiom audit.
-/

namespace NRRF783T

universe u v

/-! ## §1  Levels -/

/-- An additive commutative group of levels, given as data.  No library, hence no classical
instance, is involved. -/
structure AddGroupStr (G : Type u) where
  /-- The neutral level. -/
  zero : G
  /-- Addition of levels. -/
  add : G → G → G
  /-- Negation of levels. -/
  neg : G → G
  /-- Associativity. -/
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  /-- Neutrality on the left. -/
  zero_add : ∀ a, add zero a = a
  /-- Neutrality on the right. -/
  add_zero : ∀ a, add a zero = a
  /-- Inverses. -/
  add_neg : ∀ a, add a (neg a) = zero
  /-- Commutativity. -/
  add_comm : ∀ a b, add a b = add b a

namespace AddGroupStr

variable {G : Type u} (L : AddGroupStr G)

theorem neg_add (a : G) : L.add (L.neg a) a = L.zero := by
  rw [L.add_comm, L.add_neg]

/-- Left cancellation. -/
theorem add_left_cancel {a b c : G} (h : L.add a b = L.add a c) : b = c := by
  have h' : L.add (L.neg a) (L.add a b) = L.add (L.neg a) (L.add a c) := by rw [h]
  rw [← L.add_assoc, ← L.add_assoc, L.neg_add, L.zero_add, L.zero_add] at h'
  exact h'

/-- Right cancellation. -/
theorem add_right_cancel {a b c : G} (h : L.add a c = L.add b c) : a = b := by
  refine L.add_left_cancel (a := c) ?_
  rw [L.add_comm c a, L.add_comm c b]
  exact h

end AddGroupStr

/-! ## §2  Translational truth -/

variable {ι : Type v} {G : Type u}

/-- A **reading** of the domain `ι` in the levels `G` is a potential at each site. -/
abbrev Reading (ι : Type v) (G : Type u) : Type max u v := ι → G

/-- **Translational truth**: two readings are the same truth when they differ by one global
shift. -/
def TransTruth (L : AddGroupStr G) (x y : Reading ι G) : Prop :=
  ∃ g : G, ∀ i, y i = L.add (x i) g

/-- The **closure** of a reading: the readings translationally true to it. -/
def Closure (L : AddGroupStr G) (x : Reading ι G) : Reading ι G → Prop :=
  fun y => TransTruth L x y

theorem transTruth_refl (L : AddGroupStr G) (x : Reading ι G) : TransTruth L x x :=
  ⟨L.zero, fun i => (L.add_zero (x i)).symm⟩

theorem transTruth_symm {L : AddGroupStr G} {x y : Reading ι G} (h : TransTruth L x y) :
    TransTruth L y x := by
  obtain ⟨g, hg⟩ := h
  refine ⟨L.neg g, fun i => ?_⟩
  rw [hg i, L.add_assoc, L.add_neg, L.add_zero]

theorem transTruth_trans {L : AddGroupStr G} {x y z : Reading ι G}
    (hxy : TransTruth L x y) (hyz : TransTruth L y z) : TransTruth L x z := by
  obtain ⟨g, hg⟩ := hxy
  obtain ⟨k, hk⟩ := hyz
  refine ⟨L.add g k, fun i => ?_⟩
  rw [hk i, hg i, L.add_assoc]

theorem mem_closure_self (L : AddGroupStr G) (x : Reading ι G) : Closure L x x :=
  transTruth_refl L x

/-! ## §3  The closures are unique -/

/-- **Closure equality is translational truth.** -/
theorem closure_eq_iff_transTruth (L : AddGroupStr G) (x y : Reading ι G) :
    Closure L x = Closure L y ↔ TransTruth L x y := by
  constructor
  · intro h
    have hy : Closure L y y := mem_closure_self L y
    rw [← h] at hy
    exact hy
  · intro h
    funext z
    apply propext
    exact ⟨fun hz => transTruth_trans (transTruth_symm h) hz, fun hz => transTruth_trans h hz⟩

/-- **Overlapping closures are equal.**  This is the constructive content of "closures are equal
or disjoint": the classical dichotomy would have to *decide* translational truth, and the
development never needs it — what it uses is that a shared reading forces equality. -/
theorem closure_eq_of_overlap (L : AddGroupStr G) {x y z : Reading ι G}
    (hx : Closure L x z) (hy : Closure L y z) : Closure L x = Closure L y :=
  (closure_eq_iff_transTruth L x y).mpr (transTruth_trans hx (transTruth_symm hy))

/-- Every reading lies in a closure, namely its own, and that closure is forced. -/
theorem exists_closure (L : AddGroupStr G) (x : Reading ι G) :
    Closure L x x ∧ ∀ y, Closure L y x → Closure L y = Closure L x :=
  ⟨mem_closure_self L x, fun _ hy => closure_eq_of_overlap L hy (mem_closure_self L x)⟩

/-! ## §4  Sizes and potentials as relative absolutes -/

/-- **The shift is unique** on an inhabited domain. -/
theorem shift_unique (L : AddGroupStr G) (x : Reading ι G) (i₀ : ι) {g k : G}
    (h : ∀ i, L.add (x i) g = L.add (x i) k) : g = k :=
  L.add_left_cancel (h i₀)

/-- **Relative potentials are invariant on a closure**: the difference of two levels does not move
when the reading is shifted. -/
theorem potential_invariant (L : AddGroupStr G) {x y : Reading ι G} (h : TransTruth L x y)
    (i j : ι) : L.add (y i) (L.neg (y j)) = L.add (x i) (L.neg (x j)) := by
  obtain ⟨g, hg⟩ := h
  rw [hg i, hg j]
  -- (x i + g) - (x j + g) = x i - x j
  have hneg : L.neg (L.add (x j) g) = L.add (L.neg (x j)) (L.neg g) := by
    refine L.add_left_cancel (a := L.add (x j) g) ?_
    rw [L.add_neg]
    rw [L.add_assoc, ← L.add_assoc g (L.neg (x j)) (L.neg g), L.add_comm g (L.neg (x j)),
      L.add_assoc, L.add_neg, L.add_zero, L.add_neg]
  rw [hneg, ← L.add_assoc, L.add_assoc (x i) g (L.neg (x j)), L.add_comm g (L.neg (x j)),
    ← L.add_assoc, L.add_assoc, L.add_neg, L.add_zero]

/-- **Relative potentials determine the closure**: on an inhabited domain, two readings with the
same relative potentials are translationally true to one another. -/
theorem potential_complete (L : AddGroupStr G) (x y : Reading ι G) (i₀ : ι)
    (h : ∀ i, L.add (y i) (L.neg (y i₀)) = L.add (x i) (L.neg (x i₀))) : TransTruth L x y := by
  refine ⟨L.add (L.neg (x i₀)) (y i₀), fun i => ?_⟩
  have hi := h i
  -- from `y i - y i₀ = x i - x i₀` conclude `y i = x i + (-x i₀ + y i₀)`
  have h1 : L.add (L.add (y i) (L.neg (y i₀))) (y i₀) =
      L.add (L.add (x i) (L.neg (x i₀))) (y i₀) := by rw [hi]
  rw [L.add_assoc (y i) (L.neg (y i₀)) (y i₀), L.neg_add, L.add_zero,
    L.add_assoc (x i) (L.neg (x i₀)) (y i₀)] at h1
  exact h1

/-- **Individual levels are not absolute**: as soon as a nonzero shift exists, every site moves
inside the closure.  The moving reading is exhibited, not obtained from excluded middle. -/
theorem value_not_absolute (L : AddGroupStr G) (x : Reading ι G) {g : G} (hg : g ≠ L.zero)
    (i : ι) : ∃ y, Closure L x y ∧ y i ≠ x i := by
  refine ⟨fun j => L.add (x j) g, ⟨g, fun _ => rfl⟩, fun hy => hg ?_⟩
  refine L.add_left_cancel (a := x i) ?_
  rw [L.add_zero]
  exact hy

/-! ## §5  The two strands are one: a translational closure is an axiometric form -/

/-- The carrier of the closure of `x`, as a type: the readings translationally true to `x`. -/
def ClosureCarrier (L : AddGroupStr G) (x : Reading ι G) : Type max u v :=
  {y : Reading ι G // Closure L x y}

/-- **The translational closure of a reading is an axiometric form** in the sense of the closure
equations: the encoding is the shift action of the level group, and the evaluation reads the shift
off at a base site.  No shift is ever *chosen*: the evaluation computes it. -/
def closureForm (L : AddGroupStr G) (x : Reading ι G) (i₀ : ι) :
    NRRF783.Closure G (ClosureCarrier L x) where
  encode := fun g => ⟨fun i => L.add (x i) g, ⟨g, fun _ => rfl⟩⟩
  eval := fun y => L.add (L.neg (x i₀)) (y.val i₀)
  eval_encode := fun g => by
    show L.add (L.neg (x i₀)) (L.add (x i₀) g) = g
    rw [← L.add_assoc, L.neg_add, L.zero_add]

/-- **The form closes**: `(U3)` holds for a translational closure.  So a closure of translational
truth is a *transparent* form — the level group is exactly its encoded carrier, with nothing left
over — and this is proved without deciding anything and without choosing a representative. -/
theorem closureForm_closes (L : AddGroupStr G) (x : Reading ι G) (i₀ : ι) :
    NRRF783.Closes (closureForm L x i₀) := by
  rw [NRRF783.closes_iff_transparent]
  rintro ⟨y, g, hg⟩
  have hval : (fun i => L.add (x i) (L.add (L.neg (x i₀)) (y i₀))) = y := by
    funext i
    rw [hg i₀, ← L.add_assoc (L.neg (x i₀)) (x i₀) g, L.neg_add, L.zero_add, hg i]
  show (⟨fun i => L.add (x i) (L.add (L.neg (x i₀)) (y i₀)), _⟩ : ClosureCarrier L x) = ⟨y, _⟩
  simp only [hval]

/-- **The unification of the two strands, constructively.**  For an inhabited domain: translational
truth is an equivalence, closures are unique (overlap forces equality), relative potentials are the
invariants of a closure while individual levels are not, and the closure is the carrier of an
axiometric form that satisfies both the return equation `(U1)` and the closing equation `(U3)`. -/
theorem nrrf783_translational_unification (L : AddGroupStr G) (x : Reading ι G) (i₀ : ι) :
    (TransTruth L x x ∧
      (∀ y z, TransTruth L x y → TransTruth L y z → TransTruth L x z)) ∧
    (∀ y z, Closure L x z → Closure L y z → Closure L x = Closure L y) ∧
    (∀ y, Closure L x = Closure L y ↔ TransTruth L x y) ∧
    (∀ y, TransTruth L x y → ∀ i j, L.add (y i) (L.neg (y j)) = L.add (x i) (L.neg (x j))) ∧
    (∀ y, (∀ i, L.add (y i) (L.neg (y i₀)) = L.add (x i) (L.neg (x i₀))) → TransTruth L x y) ∧
    ((closureForm L x i₀).eval ∘ (closureForm L x i₀).encode = id ∧
      NRRF783.Closes (closureForm L x i₀)) :=
  ⟨⟨transTruth_refl L x, fun _ _ hxy hyz => transTruth_trans hxy hyz⟩,
    fun _ _ hx hy => closure_eq_of_overlap L hx hy,
    fun y => closure_eq_iff_transTruth L x y,
    fun _ h => potential_invariant L h,
    fun y h => potential_complete L x y i₀ h,
    ⟨NRRF783.unified_return _, closureForm_closes L x i₀⟩⟩

end NRRF783T

/-! ## §6  Axiom audit — machine-checked

`propext` appears only where closures, which are predicates on readings, are compared as objects;
`Quot.sound` only through function extensionality.  `Classical.choice` appears nowhere. -/

section Audit

/-- info: 'NRRF783T.transTruth_trans' does not depend on any axioms -/
#guard_msgs in #print axioms NRRF783T.transTruth_trans

/-- info: 'NRRF783T.closure_eq_iff_transTruth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms NRRF783T.closure_eq_iff_transTruth

/-- info: 'NRRF783T.closure_eq_of_overlap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms NRRF783T.closure_eq_of_overlap

/-- info: 'NRRF783T.shift_unique' does not depend on any axioms -/
#guard_msgs in #print axioms NRRF783T.shift_unique

/-- info: 'NRRF783T.potential_invariant' does not depend on any axioms -/
#guard_msgs in #print axioms NRRF783T.potential_invariant

/-- info: 'NRRF783T.potential_complete' does not depend on any axioms -/
#guard_msgs in #print axioms NRRF783T.potential_complete

/-- info: 'NRRF783T.value_not_absolute' does not depend on any axioms -/
#guard_msgs in #print axioms NRRF783T.value_not_absolute

/-- info: 'NRRF783T.closureForm_closes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms NRRF783T.closureForm_closes

/-- info: 'NRRF783T.nrrf783_translational_unification' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms NRRF783T.nrrf783_translational_unification

end Audit
