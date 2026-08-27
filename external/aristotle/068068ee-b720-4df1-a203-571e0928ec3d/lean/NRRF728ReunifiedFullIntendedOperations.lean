import Mathlib
import NRRF718ContinuumPerspectiveRelativeGoalsQuantumGravityReturn
import NRRF725ReunifiedClosureSourceOfExistenceTruthTopology
import NRRF726TranslationAlignsTruthExistenceFreeClosureUniversalNeutralField
import NRRF727ClosureWithoutProjectionTestSeparationDuality

/-!
# NRRF728 — The full intended operations, reunified

Across the development the same subject matter has been *operated on* in many different ways: by
saturating a set with truth-fibres, by taking a union of fibres, by pushing forward and pulling
back along the reading, by passing to the Closure quotient and back, by taking the topological
closure in the truth topology, by taking the test-hull of the points, by moving the set with the
whole neutral field, and by intersecting all the saturated sets that contain it.  At the level of
*pairs* the subject matter has been described by the relative diagonal, by equality in the Closure
language, by non-separation by tests, by indiscernibility in the truth topology, and by
reachability inside the neutral field.  At the level of *motions* it has been described by
neutrality, by alignment of truth and existence, by living over the Closure quotient, by the second
reading, and by preserving the operation.

This module **reunifies** all of them.  Nothing new is postulated: for one reading `r : X → S`
each list is proved to have exactly one element.

* **§1 The operations on sets.**  Each of the eight operations is proved equal to `sat r`
  (`fibreUnion_eq`, `preimageImage_eq`, `quotientOp_eq`, `truthClosure_eq`, `testOp_eq`,
  `neutralOrbit_eq`, `leastSaturated_eq`), and `intendedOperations_eq_singleton` says the whole
  collection of intended operations *is* the one-element set `{sat r}`.

* **§2 The relations on pairs.**  `intendedRelations_eq_singleton` : the eight intended relations
  are the single relation `fun x y => r x = r y`.

* **§3 The fields of motions.**  `intendedFields_eq_singleton` : the eight intended descriptions of
  the admissible motions are the single field `neutralField r`.

* **§4 The three levels are one datum.**  `sat_eq_iff_relDiag_eq` and
  `all_levels_agree` : for two readings the operation, the relation, the neutral field and the
  truth topology agree or disagree together — each level determines the other two.

* **§5 The one operation, characterised.**  `sat_is_closure_operator`, `sat_iUnion`, `sat_empty`,
  `sat_comp_sat`, and `sat_unique` : `sat r` is the unique operation which is extensive, lands in
  the saturated sets and is below every saturated superset.  So the reunified operation is not one
  choice among many — it is forced.

`nrrf728_answer` collects the headline points.
-/

namespace NRRF728

open NRRF718 NRRF725 NRRF726 NRRF727

/-! ## §1  The intended operations on sets -/

section Operations

variable {X S : Type}

/-- Operation 1: the **saturation** by truth-fibres (NRRF725). -/
def satOp (r : X → S) : Set X → Set X := sat r

/-- Operation 2: the **union of the fibres** of the points of the set. -/
def fibreUnion (r : X → S) (U : Set X) : Set X := ⋃ x ∈ U, {y | r y = r x}

/-- Operation 3: **push forward along the reading and pull back again**. -/
def preimageImage (r : X → S) (U : Set X) : Set X := r ⁻¹' (r '' U)

/-- Operation 4: **through the Closure quotient and back**. -/
def quotientOp (r : X → S) (U : Set X) : Set X := cq r ⁻¹' (cq r '' U)

/-- Operation 5: the **topological closure** in the translational truth topology. -/
def truthClosure (r : X → S) (U : Set X) : Set X := @closure X (truthTopology r) U

/-- Operation 6: the **test hull of the points** of the set, in the projection-free presentation
of NRRF727. -/
def testOp (r : X → S) (U : Set X) : Set X := ⋃ x ∈ U, hull (readingTests r) {x}

/-- Operation 7: **moving the set by the whole neutral field**. -/
def neutralOrbit (r : X → S) (U : Set X) : Set X :=
  {y | ∃ f ∈ neutralField r, ∃ u ∈ U, f u = y}

/-- Operation 8: the **intersection of all saturated sets containing** the set. -/
def leastSaturated (r : X → S) (U : Set X) : Set X := ⋂₀ {V : Set X | Saturated r V ∧ U ⊆ V}

variable (r : X → S) (U : Set X)

@[simp] theorem mem_sat {x : X} : x ∈ sat r U ↔ ∃ u ∈ U, r x = r u := Iff.rfl

theorem satOp_eq : satOp r U = sat r U := rfl

theorem fibreUnion_eq : fibreUnion r U = sat r U := by
  ext y
  simp [fibreUnion, sat]

theorem preimageImage_eq : preimageImage r U = sat r U := by
  ext y
  constructor
  · rintro ⟨u, hu, hru⟩; exact ⟨u, hu, hru.symm⟩
  · rintro ⟨u, hu, hy⟩; exact ⟨u, hu, hy.symm⟩

theorem quotientOp_eq : quotientOp r U = sat r U := by
  ext y
  constructor
  · rintro ⟨u, hu, hcu⟩
    exact ⟨u, hu, ((cq_eq_iff r u y).1 hcu).symm⟩
  · rintro ⟨u, hu, hy⟩
    exact ⟨u, hu, (cq_eq_iff r u y).2 hy.symm⟩

theorem truthClosure_eq : truthClosure r U = sat r U := truth_closure_eq_sat r U

theorem testOp_eq : testOp r U = sat r U := by
  ext y
  simp [testOp, hull_singleton_readingTests, sat]

theorem neutralOrbit_eq : neutralOrbit r U = sat r U := by
  classical
  ext y
  constructor
  · rintro ⟨f, hf, u, hu, rfl⟩
    exact ⟨u, hu, hf u⟩
  · rintro ⟨u, hu, hy⟩
    refine ⟨fun z => if r z = r u then y else z, ?_, u, hu, ?_⟩
    · intro z
      show r (if r z = r u then y else z) = r z
      by_cases h : r z = r u
      · rw [if_pos h, hy, h]
      · rw [if_neg h]
    · show (if r u = r u then y else u) = y
      rw [if_pos rfl]

theorem leastSaturated_eq : leastSaturated r U = sat r U := by
  apply Set.Subset.antisymm
  · exact Set.sInter_subset_of_mem ⟨sat_saturated r U, subset_sat r U⟩
  · rintro x ⟨u, hu, hx⟩ V hV
    exact (hV.1 x u hx).2 (hV.2 hu)

/-- The **full list of intended operations** on sets of occurrences. -/
def intendedOperations (r : X → S) : Set (Set X → Set X) :=
  {satOp r, fibreUnion r, preimageImage r, quotientOp r, truthClosure r, testOp r,
    neutralOrbit r, leastSaturated r}

/-- **The operations are reunified.**  Every operation the development performs on a set of
occurrences is one and the same operation: the collection of intended operations is a singleton. -/
theorem intendedOperations_eq_singleton : intendedOperations r = {sat r} := by
  have h1 : satOp r = sat r := funext (satOp_eq r)
  have h2 : fibreUnion r = sat r := funext (fibreUnion_eq r)
  have h3 : preimageImage r = sat r := funext (preimageImage_eq r)
  have h4 : quotientOp r = sat r := funext (quotientOp_eq r)
  have h5 : truthClosure r = sat r := funext (truthClosure_eq r)
  have h6 : testOp r = sat r := funext (testOp_eq r)
  have h7 : neutralOrbit r = sat r := funext (neutralOrbit_eq r)
  have h8 : leastSaturated r = sat r := funext (leastSaturated_eq r)
  simp [intendedOperations, h1, h2, h3, h4, h5, h6, h7, h8]

end Operations

/-! ## §2  The intended relations on pairs -/

section Relations

variable {X S : Type} (r : X → S)

/-- The **full list of intended relations** between two occurrences. -/
def intendedRelations : Set (X → X → Prop) :=
  { (fun x y => r x = r y),
    (fun x y => (x, y) ∈ relDiag r),
    (fun x y => cq r x = cq r y),
    (fun x y => y ∈ sat r {x}),
    (fun x y => sat r {x} = sat r {y}),
    (fun x y => NoTestSeparates (readingTests r) x y),
    (fun x y => ∀ U : Set X, Saturated r U → (x ∈ U ↔ y ∈ U)),
    (fun x y => ∃ f ∈ neutralField r, f x = y) }

theorem relDiag_rel : (fun x y : X => (x, y) ∈ relDiag r) = fun x y => r x = r y := rfl

theorem cq_rel : (fun x y : X => cq r x = cq r y) = fun x y => r x = r y := by
  funext x y
  exact propext (cq_eq_iff r x y)

theorem satSingleton_rel : (fun x y : X => y ∈ sat r {x}) = fun x y => r x = r y := by
  funext x y
  refine propext ⟨?_, ?_⟩
  · rintro ⟨u, hu, hy⟩
    rw [Set.mem_singleton_iff] at hu
    subst hu
    exact hy.symm
  · intro h
    exact ⟨x, rfl, h.symm⟩

theorem satEq_rel : (fun x y : X => sat r {x} = sat r {y}) = fun x y => r x = r y := by
  funext x y
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · have hx : x ∈ sat r {y} := by rw [← h]; exact subset_sat r _ rfl
    obtain ⟨u, hu, hxu⟩ := hx
    rw [Set.mem_singleton_iff] at hu
    subst hu
    exact hxu
  · ext z
    constructor
    · rintro ⟨u, hu, hz⟩
      rw [Set.mem_singleton_iff] at hu
      subst hu
      exact ⟨y, rfl, hz.trans h⟩
    · rintro ⟨u, hu, hz⟩
      rw [Set.mem_singleton_iff] at hu
      subst hu
      exact ⟨x, rfl, hz.trans h.symm⟩

theorem noTestSeparates_rel :
    (fun x y : X => NoTestSeparates (readingTests r) x y) = fun x y => r x = r y := by
  funext x y
  exact propext (noTestSeparates_readingTests r x y)

theorem saturatedIndiscernible_rel :
    (fun x y : X => ∀ U : Set X, Saturated r U → (x ∈ U ↔ y ∈ U)) = fun x y => r x = r y := by
  funext x y
  refine propext ⟨fun h => ?_, fun h U hU => hU x y h⟩
  have := (h (sat r {x}) (sat_saturated r _)).1 (subset_sat r _ rfl)
  obtain ⟨u, hu, hy⟩ := this
  rw [Set.mem_singleton_iff] at hu
  subst hu
  exact hy.symm

theorem neutralReach_rel :
    (fun x y : X => ∃ f ∈ neutralField r, f x = y) = fun x y => r x = r y := by
  classical
  funext x y
  refine propext ⟨?_, ?_⟩
  · rintro ⟨f, hf, rfl⟩
    exact (hf x).symm
  · intro h
    refine ⟨fun z => if r z = r x then y else z, ?_, ?_⟩
    · intro z
      show r (if r z = r x then y else z) = r z
      by_cases hz : r z = r x
      · rw [if_pos hz, ← h, hz]
      · rw [if_neg hz]
    · show (if r x = r x then y else x) = y
      rw [if_pos rfl]

/-- **The relations are reunified.**  Every relation between occurrences the development uses is
one and the same relation: being returned to the same Closure. -/
theorem intendedRelations_eq_singleton :
    intendedRelations r = {fun x y => r x = r y} := by
  unfold intendedRelations
  rw [relDiag_rel, cq_rel, satSingleton_rel, satEq_rel, noTestSeparates_rel,
    saturatedIndiscernible_rel, neutralReach_rel]
  simp

end Relations

/-! ## §3  The intended fields of motions -/

section Fields

variable {X S : Type} (r : X → S)

/-- The **full list of intended descriptions** of the admissible motions of the occurrences. -/
def intendedFields : Set (Set (X → X)) :=
  { neutralField r,
    {f | Aligns r f},
    {f | cq r ∘ f = cq r},
    {f | secondReading r f = r},
    {f | ∀ x, f x ∈ sat r {x}},
    {f | ∀ U : Set X, f ⁻¹' (sat r U) = sat r U},
    {f | ∀ U : Set X, Saturated r U → f ⁻¹' U = U},
    {f | Neutral (secondReading r) (fun g => f ∘ g)} }

theorem aligns_field : {f : X → X | Aligns r f} = neutralField r := by
  ext f
  exact aligns_iff_neutral r f

theorem overClosure_field : {f : X → X | cq r ∘ f = cq r} = neutralField r := by
  ext f
  exact (neutral_iff_over_closure r f).symm

theorem secondReading_field : {f : X → X | secondReading r f = r} = neutralField r := by
  ext f
  constructor
  · intro h x; exact congrFun h x
  · intro h; funext x; exact h x

theorem movesInsideFibre_field : {f : X → X | ∀ x, f x ∈ sat r {x}} = neutralField r := by
  ext f
  constructor
  · intro h x
    obtain ⟨u, hu, hx⟩ := h x
    rw [Set.mem_singleton_iff] at hu
    subst hu
    exact hx
  · intro h x
    exact ⟨x, rfl, h x⟩

theorem preservesOperation_field :
    {f : X → X | ∀ U : Set X, f ⁻¹' (sat r U) = sat r U} = neutralField r := by
  ext f
  constructor
  · intro h x
    have hx : x ∈ f ⁻¹' (sat r {x}) := by
      rw [h {x}]; exact subset_sat r _ rfl
    obtain ⟨u, hu, hfx⟩ := hx
    rw [Set.mem_singleton_iff] at hu
    subst hu
    exact hfx
  · intro h U
    ext x
    constructor
    · rintro ⟨u, hu, hfx⟩
      exact ⟨u, hu, (h x).symm.trans hfx⟩
    · rintro ⟨u, hu, hx⟩
      exact ⟨u, hu, (h x).trans hx⟩

theorem preservesSaturated_field :
    {f : X → X | ∀ U : Set X, Saturated r U → f ⁻¹' U = U} = neutralField r := by
  ext f
  constructor
  · intro h x
    have hx : x ∈ f ⁻¹' (sat r {x}) := by
      rw [h _ (sat_saturated r {x})]; exact subset_sat r _ rfl
    obtain ⟨u, hu, hfx⟩ := hx
    rw [Set.mem_singleton_iff] at hu
    subst hu
    exact hfx
  · intro h U hU
    ext x
    exact hU (f x) x (h x)

theorem actsNeutrally_field :
    {f : X → X | Neutral (secondReading r) (fun g => f ∘ g)} = neutralField r := by
  ext f
  exact neutral_secondReading_iff r f

/-- **The fields of motions are reunified.**  Every description of the admissible motions the
development uses picks out one and the same field: the neutral field. -/
theorem intendedFields_eq_singleton : intendedFields r = {neutralField r} := by
  unfold intendedFields
  rw [aligns_field, overClosure_field, secondReading_field, movesInsideFibre_field,
    preservesOperation_field, preservesSaturated_field, actsNeutrally_field]
  simp

end Fields

/-! ## §4  The three levels are one datum -/

section Levels

variable {X S S' : Type} (r : X → S) (r' : X → S')

/-- The operation determines the relation and conversely. -/
theorem sat_eq_iff_relDiag_eq : sat r = sat r' ↔ relDiag r = relDiag r' := by
  constructor
  · intro h
    ext p
    have h1 : p.1 ∈ sat r {p.2} ↔ p.1 ∈ sat r' {p.2} := by rw [h]
    simp only [relDiag, Set.mem_setOf_eq]
    constructor
    · intro hp
      obtain ⟨u, hu, h2⟩ := h1.1 ⟨p.2, rfl, hp⟩
      rw [Set.mem_singleton_iff] at hu
      subst hu
      exact h2
    · intro hp
      obtain ⟨u, hu, h2⟩ := h1.2 ⟨p.2, rfl, hp⟩
      rw [Set.mem_singleton_iff] at hu
      subst hu
      exact h2
  · intro h
    have key : ∀ a b : X, r a = r b ↔ r' a = r' b := by
      intro a b
      have := Set.ext_iff.1 h (a, b)
      exact this
    funext U
    ext x
    constructor
    · rintro ⟨u, hu, hx⟩; exact ⟨u, hu, (key x u).1 hx⟩
    · rintro ⟨u, hu, hx⟩; exact ⟨u, hu, (key x u).2 hx⟩

/-- **All four levels agree together.**  For two readings of the same occurrences, the reunified
operation, the reunified relation, the reunified field of motions and the truth topology are equal
for one exactly when they are equal for all: there is a single datum, presented four ways. -/
theorem all_levels_agree :
    (sat r = sat r' ↔ relDiag r = relDiag r') ∧
    (relDiag r = relDiag r' ↔ neutralField r = neutralField r') ∧
    (relDiag r = relDiag r' ↔ truthTopology r = truthTopology r') :=
  ⟨sat_eq_iff_relDiag_eq r r', (neutralField_eq_iff_relDiag_eq r r').symm,
    relDiag_eq_iff_truthTopology_eq r r'⟩

end Levels

/-! ## §5  The one operation, characterised -/

section Characterisation

variable {X S : Type} (r : X → S)

@[simp] theorem sat_empty : sat r (∅ : Set X) = ∅ := by
  ext x; simp [sat]

theorem sat_mono {U V : Set X} (h : U ⊆ V) : sat r U ⊆ sat r V := by
  rintro x ⟨u, hu, hx⟩; exact ⟨u, h hu, hx⟩

theorem sat_sat (U : Set X) : sat r (sat r U) = sat r U := by
  apply Set.Subset.antisymm
  · rintro x ⟨v, ⟨u, hu, hv⟩, hx⟩
    exact ⟨u, hu, hx.trans hv⟩
  · exact subset_sat r _

theorem sat_comp_sat : sat r ∘ sat r = sat r := funext (sat_sat r)

/-- The reunified operation is a genuine closure operator. -/
theorem sat_is_closure_operator :
    (∀ U : Set X, U ⊆ sat r U) ∧ (∀ U V : Set X, U ⊆ V → sat r U ⊆ sat r V) ∧
      (∀ U : Set X, sat r (sat r U) = sat r U) :=
  ⟨subset_sat r, fun _ _ h => sat_mono r h, sat_sat r⟩

/-- The reunified operation preserves arbitrary unions: it is determined by what it does to
points. -/
theorem sat_iUnion {ι : Type} (V : ι → Set X) :
    sat r (⋃ i, V i) = ⋃ i, sat r (V i) := by
  ext x
  simp only [Set.mem_iUnion, sat, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, ⟨i, hi⟩, hx⟩; exact ⟨i, u, hi, hx⟩
  · rintro ⟨i, u, hi, hx⟩; exact ⟨u, ⟨i, hi⟩, hx⟩

theorem sat_eq_biUnion_points (U : Set X) : sat r U = ⋃ x ∈ U, sat r {x} := by
  have hpt : ∀ x : X, sat r {x} = {y | r y = r x} := by
    intro x; ext y; simp [sat]
  simp only [hpt]
  exact (fibreUnion_eq r U).symm

/-- **The reunified operation is forced.**  Any operation that is extensive, always saturated, and
below every saturated superset *is* `sat r`: the reunification is not a choice among equals but the
only possible operation. -/
theorem sat_unique (c : Set X → Set X) (h₁ : ∀ U, U ⊆ c U) (h₂ : ∀ U, Saturated r (c U))
    (h₃ : ∀ U V : Set X, Saturated r V → U ⊆ V → c U ⊆ V) : c = sat r := by
  funext U
  apply Set.Subset.antisymm
  · exact h₃ U (sat r U) (sat_saturated r U) (subset_sat r U)
  · rintro x ⟨u, hu, hx⟩
    exact (h₂ U x u hx).2 (h₁ U hu)

end Characterisation

/-! ## §6  The answer -/

section Answer

variable {X S : Type} (r : X → S)

/-- **The full intended operations, reunified.**  On sets, on pairs and on motions the development
performs exactly one operation, one relation and one field; the three levels determine one another;
and the operation is the unique one with the intended properties. -/
theorem nrrf728_answer :
    intendedOperations r = {sat r} ∧
    intendedRelations r = {fun x y => r x = r y} ∧
    intendedFields r = {neutralField r} ∧
    (∀ (S' : Type) (r' : X → S'), sat r = sat r' ↔ relDiag r = relDiag r') ∧
    (∀ c : Set X → Set X, (∀ U, U ⊆ c U) → (∀ U, Saturated r (c U)) →
      (∀ U V : Set X, Saturated r V → U ⊆ V → c U ⊆ V) → c = sat r) :=
  ⟨intendedOperations_eq_singleton r, intendedRelations_eq_singleton r,
    intendedFields_eq_singleton r, fun _ r' => sat_eq_iff_relDiag_eq r r', sat_unique r⟩

end Answer

end NRRF728
