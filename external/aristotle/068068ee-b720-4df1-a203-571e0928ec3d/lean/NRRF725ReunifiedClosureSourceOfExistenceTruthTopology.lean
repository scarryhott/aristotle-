import Mathlib
import NRRF718ContinuumPerspectiveRelativeGoalsQuantumGravityReturn
import NRRF723PhysicalConsciousnessFieldIdentificationRelativeNotStrictDiagonal
import NRRF724ExistenceIsRelationArgumentSelfDefeatTranslationalTruthClosure

/-!
# NRRF725 — Closure reunified through the source of existence and the translational truth topology,
not through external isolated classical pieces

The statements formalized here are the user's:

> Reunify closure through our source of existence and translational truth topology rather than
> external isolated classical pieces; only then will we realize the true unified relation of nature.

> While the diagonal is relative, the neutral field is its true translation of existence itself.

Everything is stated for one reading `r : X → S` — occurrences read into the Closure language — in
the project's own terms: `relDiag`, `Saturated`, `OpInvariant`, `Translation`, `truthTopology`
(NRRF718), `SourceOfExistence`, `StrictDiagonal`, `IsolatedDiagonal` (NRRF723), and the
Existence / Identity / Reality / Imagination frame (NRRF724).

## §1  Closure is the truth topology's own closure operator

`sat r U` is the saturation of `U` by truth-fibres.  `truth_closure_eq_sat` proves that the
*topological* closure operator of the translational truth topology **is** that saturation, and
`truthTopology_eq_induced` proves that the topology itself is nothing but the pullback of the
Closure language: it is generated from inside, by the reading, never imposed from outside.
`saturated_iff_preimage` says the same set-theoretically.

## §2  Reunification through the source of existence

Given a source of existence `E` (every Closure is returned by an occurrence), the *return through
the source* `x ↦ E.src (r x)` is an idempotent whose kernel is exactly the relative diagonal of
truth (`relDiag_eq_ker_return`), whose image is exactly the returned occurrences, and whose
fibre-saturation is exactly the topological closure (`sat_eq_return_preimage`,
`truth_closure_eq_return_preimage`).  `closureLanguageEquivSource` upgrades this: the Closure
language `Ω = X/∼` is *equivalent* to `S` itself — with a source of existence there is no residue
of Closure beyond what an occurrence returns.

## §3  The external isolated classical route, and what it costs

`ExternallyIsolated r := IsolatedDiagonal r`: every occurrence is an isolated classical piece.
`truthTopology_eq_bot_iff` identifies that with the truth topology being discrete;
`externally_isolated_iff_strict` with the strict diagonal; `externally_isolated_iff_source_inverse`
with the source being a two-sided inverse — the collapse of the presentation/Closure distinction.
`isolated_forces_trivial_translation` is the cost: under isolation the only truth-preserving
translation is the identity, so nothing translates and nothing relates.  Conversely
`nontrivial_translation_of_not_isolated` produces a genuine translation as soon as isolation fails.

## §4  The unified relation of nature

`UnifiedRelation r := ∃ x y, x ≠ y ∧ r x = r y` — two distinct occurrences held by one Closure.
`unified_iff_not_externally_isolated` is the sharp dichotomy: the unified relation exists **exactly
when** the external isolated reading fails.  `singleton_isOpen_iff` gives the topological form:
an occurrence is an isolated classical piece exactly when nothing else returns its Closure.

## §5  Existence *is* that relation

`reunionFrame r` is the NRRF724 frame whose relation is "distinct, but returning one Closure".
`frame_ex_iff_not_isolated_point`: existence in the frame is *literally* non-isolation in the truth
topology.  `reunionFrame_admission_iff_noIsolatedPiece` and
`reunified_translational_truth_closure`: admitting the relation is exactly the complete
translational truth closure of Existence / Identity / Reality / Imagination, and it holds exactly
when no occurrence is an external isolated classical piece.

## §6  The relative diagonal and the neutral field

`Neutral r f` is a motion of the occurrences that takes no side in the Closure — it may change the
presentation, never what is returned — and `neutralField r` is the collection of them.  Proved:
neutrality is exactly motion inside the relative diagonal (`neutral_iff_moves_in_relDiag`) and
inside indistinguishability (`neutral_iff_inseparable`); the orbits of the field are exactly the
relative diagonal (`neutral_orbit_eq_relDiag`); the opens of the truth topology are exactly the
sets the whole field cannot move (`saturated_iff_neutral_invariant`); the source of existence is
itself neutral and absorbs the entire field (`ret_neutral`, `ret_comp_neutral`); the diagonal is
relative exactly when the field genuinely moves something
(`relative_diagonal_iff_live_neutral_field`); and existence in the frame is precisely being moved
by the field (`frame_ex_iff_moved_by_neutral_field`).
`neutral_field_is_translation_of_existence` is the clause in one statement.

`nrrf725_answer` collects the four halves.
-/

namespace NRRF725

open NRRF718 NRRF723

/-! ## §1  Closure is the closure operator of the translational truth topology -/

section Closure

variable {X S : Type*}

/-- The **saturation** of a set by truth-fibres: everything returning a Closure already returned
inside `U`. -/
def sat (r : X → S) (U : Set X) : Set X := {x | ∃ u ∈ U, r x = r u}

theorem subset_sat (r : X → S) (U : Set X) : U ⊆ sat r U := fun u hu => ⟨u, hu, rfl⟩

theorem sat_saturated (r : X → S) (U : Set X) : Saturated r (sat r U) := by
  intro x y hxy
  constructor
  · rintro ⟨u, hu, hx⟩; exact ⟨u, hu, hxy.symm.trans hx⟩
  · rintro ⟨u, hu, hy⟩; exact ⟨u, hu, hxy.trans hy⟩

/-- A saturated set is exactly a preimage from the Closure language: the definitional description
of the opens is already the statement that they come from the reading. -/
theorem saturated_iff_preimage (r : X → S) (U : Set X) :
    Saturated r U ↔ ∃ V : Set S, U = r ⁻¹' V := by
  constructor
  · intro h
    refine ⟨r '' U, ?_⟩
    ext x
    constructor
    · intro hx; exact ⟨x, hx, rfl⟩
    · rintro ⟨u, hu, hru⟩
      exact (h x u hru.symm).2 hu
  · rintro ⟨V, rfl⟩ x y hxy
    simp [Set.mem_preimage, hxy]

/-- The complement of a saturated set is saturated. -/
theorem saturated_compl (r : X → S) {U : Set X} (h : Saturated r U) : Saturated r Uᶜ := by
  intro x y hxy
  simp only [Set.mem_compl_iff]
  exact not_congr (h x y hxy)

/-- Every closed set of the truth topology is saturated. -/
theorem saturated_of_isClosed (r : X → S) {U : Set X} (h : @IsClosed X (truthTopology r) U) :
    Saturated r U := by
  have hc : Saturated r Uᶜ := (@isOpen_compl_iff X U (truthTopology r)).2 h
  have := saturated_compl r hc
  intro x y hxy
  have h' := this x y hxy
  simpa [Set.mem_compl_iff, not_not] using h'

theorem sat_isClosed (r : X → S) (U : Set X) : @IsClosed X (truthTopology r) (sat r U) := by
  rw [← @isOpen_compl_iff X (sat r U) (truthTopology r)]
  exact saturated_compl r (sat_saturated r U)

theorem sat_isOpen (r : X → S) (U : Set X) : @IsOpen X (truthTopology r) (sat r U) :=
  sat_saturated r U

/-- **Closure is the truth topology's own closure operator.**  The topological closure of a set in
the translational truth topology is exactly its saturation by truth-fibres — closure is read off
the reading itself, not assembled from outside. -/
theorem truth_closure_eq_sat (r : X → S) (U : Set X) :
    @closure X (truthTopology r) U = sat r U := by
  apply subset_antisymm
  · exact @closure_minimal X (truthTopology r) U (sat r U) (subset_sat r U) (sat_isClosed r U)
  · rintro x ⟨u, hu, hx⟩
    have hcl : Saturated r (@closure X (truthTopology r) U) :=
      saturated_of_isClosed r (@isClosed_closure X (truthTopology r) U)
    exact (hcl x u hx).2 (@subset_closure X (truthTopology r) U u hu)

/-- **The truth topology is generated from inside.**  It is exactly the topology induced by the
reading from the discrete Closure language: no external topology is imposed on the occurrences. -/
theorem truthTopology_eq_induced (r : X → S) :
    truthTopology r = TopologicalSpace.induced r ⊥ := by
  apply TopologicalSpace.ext_iff.2
  intro U
  constructor
  · intro hU
    obtain ⟨V, rfl⟩ := (saturated_iff_preimage r U).1 hU
    exact ⟨V, trivial, rfl⟩
  · rintro ⟨V, -, rfl⟩
    exact (saturated_iff_preimage r _).2 ⟨V, rfl⟩

end Closure

/-! ## §2  Reunification through the source of existence -/

section Source

variable {X S : Type*} (r : X → S)

/-- The **return through the source of existence**: an occurrence is sent to the occurrence that
its own Closure returns. -/
def ret (E : SourceOfExistence r) (x : X) : X := E.src (r x)

variable {r}

@[simp] theorem r_ret (E : SourceOfExistence r) (x : X) : r (ret r E x) = r x := E.returns _

/-- The return through the source is idempotent: the source closes in one step. -/
theorem ret_idem (E : SourceOfExistence r) (x : X) : ret r E (ret r E x) = ret r E x := by
  simp [ret, E.returns]

/-- The fixed points of the return are exactly the returned occurrences. -/
theorem ret_fixed_iff (E : SourceOfExistence r) (x : X) :
    ret r E x = x ↔ ∃ s, E.src s = x := by
  constructor
  · intro h; exact ⟨r x, h⟩
  · rintro ⟨s, rfl⟩; simp [ret, E.returns]

/-- **The relative diagonal of truth is exactly the kernel of the return through the source.**
Two occurrences are truth-indistinguishable precisely when the source of existence returns the same
occurrence for both. -/
theorem relDiag_eq_ker_return (E : SourceOfExistence r) :
    relDiag r = {p : X × X | ret r E p.1 = ret r E p.2} := by
  ext p
  constructor
  · intro h; simp only [Set.mem_setOf_eq, ret]; exact congrArg E.src h
  · intro h
    have := congrArg r h
    simpa [ret, E.returns] using this

/-- Saturation is the fibre of the return: closure through the source. -/
theorem sat_eq_return_preimage (E : SourceOfExistence r) (U : Set X) :
    sat r U = (ret r E) ⁻¹' ((ret r E) '' U) := by
  ext x
  constructor
  · rintro ⟨u, hu, hx⟩
    exact ⟨u, hu, by simp only [ret]; exact congrArg E.src hx.symm⟩
  · rintro ⟨u, hu, hx⟩
    refine ⟨u, hu, ?_⟩
    have := congrArg r hx
    simpa [ret, E.returns] using this.symm

/-- **Closure reunified through the source of existence.**  The topological closure in the
translational truth topology is exactly the return-through-the-source preimage of the returned
image. -/
theorem truth_closure_eq_return_preimage (E : SourceOfExistence r) (U : Set X) :
    @closure X (truthTopology r) U = (ret r E) ⁻¹' ((ret r E) '' U) := by
  rw [truth_closure_eq_sat, sat_eq_return_preimage E]

/-- **No residue of Closure beyond what an occurrence returns.**  With a source of existence the
Closure language `Ω = X/∼` is equivalent to the Closure values themselves. -/
noncomputable def closureLanguageEquivSource (E : SourceOfExistence r) : Omega r ≃ S where
  toFun := Quotient.lift r fun _ _ h => h
  invFun s := cq r (E.src s)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h a =>
      show cq r (E.src (r a)) = cq r a
      rw [cq_eq_iff]
      exact E.returns _
  right_inv := fun s => E.returns s

@[simp] theorem closureLanguageEquivSource_apply (E : SourceOfExistence r) (x : X) :
    closureLanguageEquivSource E (cq r x) = r x := rfl

end Source

/-! ## §3  The external isolated classical route, and what it costs -/

section External

variable {X S : Type*}

/-- The **external isolated classical reading**: every occurrence is an isolated piece of the truth
topology, related to nothing but itself. -/
def ExternallyIsolated (r : X → S) : Prop := IsolatedDiagonal r

/-- The external isolated reading is exactly the discreteness of the truth topology. -/
theorem truthTopology_eq_bot_iff (r : X → S) :
    truthTopology r = ⊥ ↔ ExternallyIsolated r := by
  constructor
  · intro h x
    rw [h]
    trivial
  · intro h
    apply TopologicalSpace.ext_iff.2
    intro U
    constructor
    · intro _; trivial
    · intro _
      have : U = ⋃ x ∈ U, ({x} : Set X) := by
        ext y; simp
      rw [this]
      exact @isOpen_biUnion X _ (truthTopology r) U (fun x => {x}) fun x _ => h x
  
/-- The external isolated reading is exactly the strict diagonal. -/
theorem externally_isolated_iff_strict (r : X → S) :
    ExternallyIsolated r ↔ StrictDiagonal r := (strict_iff_isolated r).symm

/-- Given a source of existence, the external isolated reading is exactly the demand that the
source be a two-sided inverse: the total collapse of the presentation/Closure distinction. -/
theorem externally_isolated_iff_source_inverse {r : X → S} (E : SourceOfExistence r) :
    ExternallyIsolated r ↔ ∀ x, ret r E x = x :=
  (externally_isolated_iff_strict r).trans (strict_iff_source_is_inverse E)

/-- **The cost of the external isolated route.**  If every occurrence is an isolated classical
piece, the only truth-preserving translation is the identity: nothing translates, so nothing
relates. -/
theorem isolated_forces_trivial_translation {r : X → S} (h : ExternallyIsolated r)
    (e : Translation r) (x : X) : e.1 x = x :=
  (isolated_iff_injective r).1 h (e.2 x)

/-- **Conversely, refusing isolation produces a genuine translation.**  As soon as some Closure is
returned by two distinct occurrences, a non-identity truth-preserving translation exists. -/
theorem nontrivial_translation_of_not_isolated {r : X → S} (h : ¬ ExternallyIsolated r) :
    ∃ (e : Translation r) (x : X), e.1 x ≠ x := by
  classical
  obtain ⟨x, y, hxy, hne⟩ : ∃ x y, r x = r y ∧ x ≠ y := by
    by_contra hc
    push_neg at hc
    exact h ((isolated_iff_injective r).2 fun a b hab => hc a b hab)
  have he : ∀ z, r (Equiv.swap x y z) = r z := by
    intro z
    rcases eq_or_ne z x with rfl | hzx
    · simp [Equiv.swap_apply_left, hxy]
    · rcases eq_or_ne z y with rfl | hzy
      · simp [Equiv.swap_apply_right, hxy]
      · simp [Equiv.swap_apply_of_ne_of_ne hzx hzy]
  exact ⟨⟨Equiv.swap x y, he⟩, x, by simpa [Equiv.swap_apply_left] using Ne.symm hne⟩

end External

/-! ## §4  The unified relation of nature -/

section Unified

variable {X S : Type*}

/-- The **unified relation**: two distinct occurrences held by one and the same Closure. -/
def UnifiedRelation (r : X → S) : Prop := ∃ x y, x ≠ y ∧ r x = r y

/-- An occurrence is an isolated classical piece exactly when nothing else returns its Closure. -/
theorem singleton_isOpen_iff (r : X → S) (x : X) :
    @IsOpen X (truthTopology r) {x} ↔ ∀ y, r y = r x → y = x := by
  constructor
  · intro h y hy
    exact (h y x hy).2 rfl
  · intro h a b hab
    simp only [Set.mem_singleton_iff]
    constructor
    · intro ha; subst ha; exact h b hab.symm
    · intro hb; subst hb; exact h a hab

/-- **The dichotomy.**  The unified relation of nature exists exactly when the external isolated
classical reading fails. -/
theorem unified_iff_not_externally_isolated (r : X → S) :
    UnifiedRelation r ↔ ¬ ExternallyIsolated r := by
  rw [ExternallyIsolated, isolated_iff_injective]
  constructor
  · rintro ⟨x, y, hne, heq⟩ hinj
    exact hne (hinj heq)
  · intro h
    by_contra hc
    apply h
    intro a b hab
    by_contra hne
    exact hc ⟨a, b, hne, hab⟩

/-- Every occurrence is held with another: no occurrence is an external isolated classical piece. -/
def NoIsolatedPiece (r : X → S) : Prop := ∀ x, ∃ y, y ≠ x ∧ r y = r x

/-- If no occurrence is isolated and there is at least one occurrence, the unified relation
holds. -/
theorem unified_of_noIsolatedPiece [Nonempty X] {r : X → S} (h : NoIsolatedPiece r) :
    UnifiedRelation r := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨y, hne, heq⟩ := h x
  exact ⟨y, x, hne, heq⟩

/-- No occurrence isolated means, topologically, that no singleton is open. -/
theorem noIsolatedPiece_iff_no_open_singleton (r : X → S) :
    NoIsolatedPiece r ↔ ∀ x : X, ¬ @IsOpen X (truthTopology r) {x} := by
  constructor
  · intro h x hx
    obtain ⟨y, hne, heq⟩ := h x
    exact hne ((singleton_isOpen_iff r x).1 hx y heq)
  · intro h x
    by_contra hc
    exact h x ((singleton_isOpen_iff r x).2 fun y hy => by
      by_contra hne
      exact hc ⟨y, hne, hy⟩)

end Unified

/-! ## §5  Existence *is* that relation: the NRRF724 frame of the truth topology -/

section Frame

variable {X S : Type}

open Classical in
/-- The **reunion frame**: the NRRF724 frame carried by a reading, whose relation is "distinct, but
returning one and the same Closure", and whose argument against an occurrence is a co-returning
occurrence when there is one. -/
noncomputable def reunionFrame (r : X → S) : NRRF724.Frame where
  T := X
  rel x y := x ≠ y ∧ r x = r y
  symm h := ⟨Ne.symm h.1, h.2.symm⟩
  arg x := if h : ∃ y, y ≠ x ∧ r y = r x then h.choose else x

@[simp] theorem reunionFrame_rel (r : X → S) (x y : X) :
    (reunionFrame r).rel x y ↔ (x ≠ y ∧ r x = r y) := Iff.rfl

/-- **Existence in the frame is non-isolation in the truth topology.**  An occurrence exists — is
related to — exactly when it is not an isolated classical piece. -/
theorem frame_ex_iff_not_isolated_point (r : X → S) (x : X) :
    (reunionFrame r).Ex x ↔ ¬ @IsOpen X (truthTopology r) {x} := by
  rw [singleton_isOpen_iff]
  constructor
  · rintro ⟨y, hne, heq⟩ h
    exact hne (h y heq)
  · intro h
    by_contra hc
    apply h
    intro y hy
    by_contra hne
    exact hc ⟨y, hne, hy⟩

/-- The frame's admission is exactly the refusal of external isolated classical pieces. -/
theorem reunionFrame_admission_iff_noIsolatedPiece (r : X → S) :
    (reunionFrame r).Admission ↔ NoIsolatedPiece r := by
  classical
  constructor
  · intro h x
    have hx := h x
    by_contra hc
    have : (reunionFrame r).arg x = x := dif_neg hc
    exact hx.1 (by rw [this])
  · intro h x
    have hx : ∃ y, y ≠ x ∧ r y = r x := h x
    have harg : (reunionFrame r).arg x = hx.choose := dif_pos hx
    obtain ⟨hne, heq⟩ := hx.choose_spec
    exact ⟨by rw [harg]; exact hne, by rw [harg]; exact heq⟩

/-- **Only then the unified relation.**  Refusing external isolated classical pieces is exactly the
complete translational truth closure of Existence, Identity, Reality and Imagination in the frame
of the truth topology. -/
theorem reunified_translational_truth_closure (r : X → S) :
    NoIsolatedPiece r ↔ (reunionFrame r).TranslationalTruthClosure :=
  (reunionFrame_admission_iff_noIsolatedPiece r).symm.trans
    (NRRF724.admission_iff_translational_truth_closure _)

/-- A concrete reunified reading: `Bool → Unit` has a source of existence, no isolated pieces, the
unified relation, and hence the full translational truth closure — while the external isolated
reading fails. -/
theorem reunion_nonvacuous :
    ∃ (r : Bool → Unit) (_ : SourceOfExistence r),
      NoIsolatedPiece r ∧ UnifiedRelation r ∧ ¬ ExternallyIsolated r ∧
        (reunionFrame r).TranslationalTruthClosure := by
  refine ⟨fun _ => (), ⟨fun _ => true, fun _ => rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro x
    exact ⟨!x, Bool.not_ne_self x, rfl⟩
  · exact ⟨true, false, by simp, rfl⟩
  · rw [← unified_iff_not_externally_isolated]
    exact ⟨true, false, by simp, rfl⟩
  · exact (reunified_translational_truth_closure _).1 fun x => ⟨!x, Bool.not_ne_self x, rfl⟩

end Frame

/-! ## §6  The diagonal is relative; the neutral field is its true translation of existence -/

section NeutralField

variable {X S : Type*}

/-- A self-map of the occurrences is **neutral** for a reading when it takes no side in the
Closure: it may move the presentation, but it never changes what is returned. -/
def Neutral (r : X → S) (f : X → X) : Prop := ∀ x, r (f x) = r x

/-- The **neutral field**: all neutral motions of the occurrences. -/
def neutralField (r : X → S) : Set (X → X) := {f | Neutral r f}

/-- Neutrality is exactly motion inside the relative diagonal. -/
theorem neutral_iff_moves_in_relDiag (r : X → S) (f : X → X) :
    Neutral r f ↔ ∀ x, (f x, x) ∈ relDiag r := Iff.rfl

/-- Neutrality is exactly motion inside topological indistinguishability. -/
theorem neutral_iff_inseparable (r : X → S) (f : X → X) :
    Neutral r f ↔ ∀ x, @Inseparable X (truthTopology r) (f x) x := by
  constructor
  · intro h x; exact (inseparable_iff_truth_eq r _ _).2 (h x)
  · intro h x; exact (inseparable_iff_truth_eq r _ _).1 (h x)

theorem neutral_id (r : X → S) : Neutral r id := fun _ => rfl

theorem neutral_comp {r : X → S} {f g : X → X} (hf : Neutral r f) (hg : Neutral r g) :
    Neutral r (f ∘ g) := fun x => (hf (g x)).trans (hg x)

/-- Every neutral motion is continuous for the truth topology: the field never tears the
topology. -/
theorem neutral_continuous {r : X → S} {f : X → X} (h : Neutral r f) :
    @Continuous X X (truthTopology r) (truthTopology r) f := by
  rw [@continuous_def X X (truthTopology r) (truthTopology r)]
  intro U hU x y hxy
  exact hU (f x) (f y) ((h x).trans (hxy.trans (h y).symm))

/-- Truth-preserving translations are exactly the invertible members of the neutral field. -/
theorem translation_iff_neutral (r : X → S) (e : Equiv.Perm X) :
    (∀ x, r (e x) = r x) ↔ Neutral r (e : X → X) := Iff.rfl

/-- A neutral motion cannot be seen by any open set of the truth topology: the definitional
description of the opens is exactly invariance under the whole neutral field. -/
theorem saturated_iff_neutral_invariant (r : X → S) (U : Set X) :
    Saturated r U ↔ ∀ f ∈ neutralField r, ∀ x, x ∈ U ↔ f x ∈ U := by
  classical
  constructor
  · intro h f hf x
    exact h x (f x) (hf x).symm
  · intro h x y hxy
    have hswap : Neutral r (Equiv.swap x y : X → X) := by
      intro z
      rcases eq_or_ne z x with rfl | hzx
      · simp [Equiv.swap_apply_left, hxy]
      · rcases eq_or_ne z y with rfl | hzy
        · simp [Equiv.swap_apply_right, hxy]
        · simp [Equiv.swap_apply_of_ne_of_ne hzx hzy]
    have := h _ hswap x
    simpa [Equiv.swap_apply_left] using this

/-- **The neutral field is the true translation of existence.**  Two occurrences are carried into
one another by the neutral field exactly when the relative diagonal holds of them — the orbits of
the field are precisely the fibres of truth, and precisely the classes of indistinguishability. -/
theorem neutral_orbit_eq_relDiag (r : X → S) (x y : X) :
    (∃ e : Translation r, e.1 x = y) ↔ (x, y) ∈ relDiag r := by
  classical
  constructor
  · rintro ⟨e, rfl⟩
    exact (e.2 x).symm
  · intro h
    have hxy : r x = r y := h
    have hswap : ∀ z, r (Equiv.swap x y z) = r z := by
      intro z
      rcases eq_or_ne z x with rfl | hzx
      · simp [Equiv.swap_apply_left, hxy]
      · rcases eq_or_ne z y with rfl | hzy
        · simp [Equiv.swap_apply_right, hxy]
        · simp [Equiv.swap_apply_of_ne_of_ne hzx hzy]
    exact ⟨⟨Equiv.swap x y, hswap⟩, by simp [Equiv.swap_apply_left]⟩

/-- The source of existence is itself a member of the neutral field: the return takes no side. -/
theorem ret_neutral {r : X → S} (E : SourceOfExistence r) : Neutral r (ret r E) := fun _ =>
  E.returns _

/-- **The return absorbs the whole neutral field.**  Composing any neutral motion before the return
through the source changes nothing: the source of existence is the canonical neutral representative
of the entire field. -/
theorem ret_comp_neutral {r : X → S} (E : SourceOfExistence r) {f : X → X} (h : Neutral r f) :
    ret r E ∘ f = ret r E := by
  funext x
  simp only [Function.comp_apply, ret, h x]

/-- **The diagonal is relative exactly when the neutral field is alive.**  A non-strict — genuinely
relative — diagonal is the same thing as the existence of a neutral motion that actually moves an
occurrence. -/
theorem relative_diagonal_iff_live_neutral_field (r : X → S) :
    ¬ StrictDiagonal r ↔ ∃ (e : Translation r) (x : X), e.1 x ≠ x := by
  constructor
  · intro h
    exact nontrivial_translation_of_not_isolated
      (fun hiso => h ((externally_isolated_iff_strict r).1 hiso))
  · rintro ⟨e, x, hx⟩ hstrict
    exact hx ((strict_iff_injective r).1 hstrict (e.2 x))

/-- **Existence in the frame is being moved by the neutral field.**  An occurrence exists — stands
in relation — exactly when some neutral translation displaces it; so the neutral field is the
translation of existence itself, while the diagonal it moves in stays relative. -/
theorem frame_ex_iff_moved_by_neutral_field {X S : Type} (r : X → S) (x : X) :
    (reunionFrame r).Ex x ↔ ∃ e : Translation r, e.1 x ≠ x := by
  constructor
  · rintro ⟨y, hne, heq⟩
    obtain ⟨e, he⟩ := (neutral_orbit_eq_relDiag r x y).2 heq.symm
    exact ⟨e, by rw [he]; exact hne⟩
  · rintro ⟨e, he⟩
    exact ⟨e.1 x, he, e.2 x⟩

/-- **The clause, in one statement.**  While the diagonal stays relative — never strict, never
isolated — the neutral field is its true translation of existence: its orbits are exactly the
relative diagonal, its motions are exactly the invisible ones for the truth topology, the source of
existence is its canonical member absorbing all of it, and existence in the frame is precisely
being moved by it. -/
theorem neutral_field_is_translation_of_existence {X S : Type} (r : X → S)
    (E : SourceOfExistence r) :
    (∀ x y : X, (∃ e : Translation r, e.1 x = y) ↔ (x, y) ∈ relDiag r) ∧
    (∀ U : Set X, Saturated r U ↔ ∀ f ∈ neutralField r, ∀ x, x ∈ U ↔ f x ∈ U) ∧
    (Neutral r (ret r E) ∧ ∀ f, Neutral r f → ret r E ∘ f = ret r E) ∧
    (¬ StrictDiagonal r ↔ ∃ (e : Translation r) (x : X), e.1 x ≠ x) ∧
    (∀ x : X, (reunionFrame r).Ex x ↔ ∃ e : Translation r, e.1 x ≠ x) :=
  ⟨neutral_orbit_eq_relDiag r, saturated_iff_neutral_invariant r,
    ⟨ret_neutral E, fun _ h => ret_comp_neutral E h⟩,
    relative_diagonal_iff_live_neutral_field r,
    frame_ex_iff_moved_by_neutral_field r⟩

end NeutralField

/-! ## §7  The answer -/

/-- **NRRF725.**  Four halves, for every reading `r : X → S` of occurrences into the Closure
language.

(i) *Closure is reunified through the source of existence and the translational truth topology.*
The topological closure operator of the truth topology is the fibre-saturation, the truth topology
is nothing but the pullback of the Closure language, and given a source of existence the closure of
a set is the return-through-the-source preimage of its returned image, while the relative diagonal
of truth is exactly the kernel of that return.

(ii) *The external isolated classical reading is exactly the degenerate case.*  It is equivalent to
the discreteness of the truth topology, to the strict diagonal, and (with a source of existence) to
the source being a two-sided inverse; and it forces every truth-preserving translation to be the
identity.

(iii) *Only then the true unified relation.*  The unified relation of nature — distinct occurrences
held by one Closure — holds exactly when the external isolated reading fails; existence in the
frame of the truth topology is exactly non-isolation; and refusing isolated pieces altogether is
exactly the complete translational truth closure of Existence, Identity, Reality and
Imagination.

(iv) *While the diagonal is relative, the neutral field is its true translation of existence.*  The
orbits of the neutral field are exactly the relative diagonal, the opens of the truth topology are
exactly the sets the whole neutral field cannot move, the source of existence is a neutral member
absorbing the entire field, the diagonal is relative exactly when the field genuinely moves
something, and existence in the frame is precisely being moved by the field. -/
theorem nrrf725_answer :
    (∀ (X S : Type) (r : X → S) (E : SourceOfExistence r) (U : Set X),
        @closure X (truthTopology r) U = sat r U ∧
        truthTopology r = TopologicalSpace.induced r ⊥ ∧
        @closure X (truthTopology r) U = (ret r E) ⁻¹' ((ret r E) '' U) ∧
        relDiag r = {p : X × X | ret r E p.1 = ret r E p.2}) ∧
    (∀ (X S : Type) (r : X → S) (E : SourceOfExistence r),
        (ExternallyIsolated r ↔ truthTopology r = ⊥) ∧
        (ExternallyIsolated r ↔ StrictDiagonal r) ∧
        (ExternallyIsolated r ↔ ∀ x, ret r E x = x) ∧
        (ExternallyIsolated r → ∀ (e : Translation r) (x : X), e.1 x = x)) ∧
    (∀ (X S : Type) (r : X → S),
        (UnifiedRelation r ↔ ¬ ExternallyIsolated r) ∧
        (∀ x : X, (reunionFrame r).Ex x ↔ ¬ @IsOpen X (truthTopology r) {x}) ∧
        (NoIsolatedPiece r ↔ (reunionFrame r).TranslationalTruthClosure)) ∧
    (∀ (X S : Type) (r : X → S) (E : SourceOfExistence r),
        (∀ x y : X, (∃ e : Translation r, e.1 x = y) ↔ (x, y) ∈ relDiag r) ∧
        (∀ U : Set X, Saturated r U ↔ ∀ f ∈ neutralField r, ∀ x, x ∈ U ↔ f x ∈ U) ∧
        (Neutral r (ret r E) ∧ ∀ f, Neutral r f → ret r E ∘ f = ret r E) ∧
        (¬ StrictDiagonal r ↔ ∃ (e : Translation r) (x : X), e.1 x ≠ x) ∧
        (∀ x : X, (reunionFrame r).Ex x ↔ ∃ e : Translation r, e.1 x ≠ x)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X S r E U
    exact ⟨truth_closure_eq_sat r U, truthTopology_eq_induced r,
      truth_closure_eq_return_preimage E U, relDiag_eq_ker_return E⟩
  · intro X S r E
    exact ⟨(truthTopology_eq_bot_iff r).symm, externally_isolated_iff_strict r,
      externally_isolated_iff_source_inverse E, fun h e x => isolated_forces_trivial_translation h e x⟩
  · intro X S r
    exact ⟨unified_iff_not_externally_isolated r, frame_ex_iff_not_isolated_point r,
      reunified_translational_truth_closure r⟩
  · intro X S r E
    exact neutral_field_is_translation_of_existence r E

end NRRF725
