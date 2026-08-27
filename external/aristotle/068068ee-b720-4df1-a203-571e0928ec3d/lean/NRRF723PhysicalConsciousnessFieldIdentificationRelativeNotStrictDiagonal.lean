import Mathlib
import NRRF714DynamicHeldTranslationConnectionInteractiveAxiometricClosure
import NRRF718ContinuumPerspectiveRelativeGoalsQuantumGravityReturn

/-!
# NRRF723 — The physical consciousness-field identification closes as a *relative* diagonal, never as a strict isolated one

The question formalized here is:

> Physical consciousness-field identification: is the next unifying closure of our project, *as a
> strict isolated diagonal*, what follows from the source of existence, or from the admission of
> translational truth, naturally?

The answer proved below is **no**, and the proof says something sharper than a refutation: the
strict isolated diagonal is not merely underivable from either premise, it is *incompatible* with
the very thing that is being identified.  What follows naturally from both premises is the
**relative diagonal** of NRRF718 — the pairs of occurrences the physical reading cannot separate —
carrying its unified definitional/operational topology.

## §1  The physical consciousness-field identification

A `PhysId` bundles the NRRF714 data: stages `S`, interpretive paths `PS`, presentations `P`, a
consciousness field `χ` transporting presentations along paths, a return signature and Closure
reading `Rd`, and — this is the *admission of translational truth* — the hypothesis
`NatTranslEq χ Rd` that Closure is preserved along every path.

The **identification** is the map `phys : Occ → C` from occurrences `Occ = Σ s, P s` (a
presentation at a stage) to their physical Closure.  `transport_in_relDiag` is the content of the
admission: transporting a presentation by the field never leaves the relative diagonal of `phys`.

## §2  What a strict isolated diagonal would be

`StrictDiagonal r` says the relative diagonal is the set-theoretic diagonal; `IsolatedDiagonal r`
says every occurrence is an isolated point of the truth topology.  `strict_iff_injective`,
`isolated_iff_injective` and `strict_iff_isolated` prove that these are one and the same condition:
the physical reading separates all occurrences.

## §3  It does not follow from the source of existence

"Source of existence" is formalized in the project's own terms: the Closure is not imposed from
outside but returned — every Closure is realized by an occurrence, and there is a source section
`src` with `phys ∘ src = id` (`SourceOfExistence`).  `source_of_existence_does_not_force_strict`
exhibits a source of existence whose diagonal is not strict, and
`strict_iff_source_is_inverse` explains exactly what strictness would additionally demand: that the
source be a two-sided inverse, i.e. that presentation and Closure be the *same* thing and the whole
presentation/Closure distinction collapse.

## §4  It does not follow from the admission of translational truth — it is refuted by it

`admission_does_not_force_strict` gives an admitted field (the NRRF714 parity field) whose diagonal
is not strict.  `strict_diagonal_freezes_field` is the sharp statement: under the admission, a
strict diagonal forces *every* transport of the field to be the identity and every path to be a
loop — the field stops being a field.  Contrapositively `living_field_not_strict`: any field that
actually moves a presentation has a non-strict diagonal.  `gauge_forbids_strict` is the same fact
in gauge language, and `quantum_phase_gauge_not_strict` instantiates it physically: the Born
reading `ψ ↦ ‖ψ‖` has the phase gauge as a nontrivial translation, so its diagonal is not strict.

## §5  What does follow, naturally

`physical_identification_closes_as_relative_diagonal`: the identification closes as an equivalence
relation which is exactly the indistinguishability relation of the truth topology, whose opens
admit both the definitional description (unions of Closure-fibres) and the operational one
(invariance under every truth-preserving translation), whose continuous discrete readings are
exactly the Closure-respecting ones, and inside which the field's transport always stays.

`nrrf723_answer` is the headline conjunction, whose second half is the negative answer:
*no*, neither premise yields the strict isolated diagonal.
-/

namespace NRRF723

open NRRF714 NRRF718

/-! ## §1  The physical consciousness-field identification -/

/-- The **physical consciousness-field identification**: the NRRF714 data of stages, interpretive
paths, presentations, a consciousness field, a return signature with its Closure reading, together
with the *admission of translational truth* — Closure is preserved along every path. -/
structure PhysId where
  /-- the stages -/
  S : Type
  /-- the interpretive paths between stages -/
  PS : PathSystem S
  /-- the presentations available at each stage -/
  P : S → Type
  /-- the return signature at each stage -/
  R : S → Type
  /-- the one Closure language -/
  C : Type
  /-- the consciousness field: transport of presentations along paths -/
  chi : ConsciousnessField PS P
  /-- return signature and Closure readings -/
  Rd : Readings P R C
  /-- the admission of translational truth -/
  admitted : NatTranslEq chi Rd

/-- An **occurrence**: a presentation held at a stage. -/
def PhysId.Occ (I : PhysId) : Type := Σ s : I.S, I.P s

/-- The **identification** itself: the physical Closure read off an occurrence. -/
def PhysId.phys (I : PhysId) (o : I.Occ) : I.C := I.Rd.cls o.1 o.2

/-- Transporting an occurrence by the consciousness field. -/
def PhysId.move (I : PhysId) {a b : I.S} (γ : I.PS.Path a b) (x : I.P a) : I.Occ :=
  ⟨b, I.chi.T γ x⟩

/-- **The admission of translational truth, read as a statement about the diagonal.**  The field's
transport never leaves the relative diagonal of the physical reading. -/
theorem transport_in_relDiag (I : PhysId) {a b : I.S} (γ : I.PS.Path a b) (x : I.P a) :
    (I.move γ x, (⟨a, x⟩ : I.Occ)) ∈ relDiag I.phys :=
  I.admitted a b γ x

/-- A field is **live** at an occurrence when its transport actually moves it. -/
def PhysId.Live (I : PhysId) : Prop :=
  ∃ (a b : I.S) (γ : I.PS.Path a b) (x : I.P a), I.move γ x ≠ (⟨a, x⟩ : I.Occ)

/-! ## §2  What a strict isolated diagonal would be -/

section Strict

variable {X S : Type*}

/-- The **strict diagonal**: the relative diagonal of `r` collapses to set-theoretic equality. -/
def StrictDiagonal (r : X → S) : Prop := relDiag r = {p : X × X | p.1 = p.2}

/-- The **isolated diagonal**: every occurrence is an isolated point of the truth topology. -/
def IsolatedDiagonal (r : X → S) : Prop := ∀ x : X, @IsOpen X (truthTopology r) {x}

/-- Strictness of the diagonal is exactly injectivity of the reading. -/
theorem strict_iff_injective (r : X → S) : StrictDiagonal r ↔ Function.Injective r := by
  constructor
  · intro h x y hxy
    have : (x, y) ∈ relDiag r := hxy
    rw [h] at this
    exact this
  · intro h
    ext p
    constructor
    · intro hp; exact h hp
    · intro hp; show r p.1 = r p.2; rw [hp]

/-- Isolation of every occurrence is also exactly injectivity of the reading. -/
theorem isolated_iff_injective (r : X → S) : IsolatedDiagonal r ↔ Function.Injective r := by
  constructor
  · intro h x y hxy
    have := h x x y hxy
    exact (this.1 rfl).symm
  · intro h x u v huv
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro rfl; exact (h huv).symm
    · rintro rfl; exact h huv

/-- **Strict and isolated are the same condition.**  A strict diagonal is an isolated (discrete)
one, and conversely. -/
theorem strict_iff_isolated (r : X → S) : StrictDiagonal r ↔ IsolatedDiagonal r :=
  (strict_iff_injective r).trans (isolated_iff_injective r).symm

/-- A strict isolated diagonal is the discrete truth topology: every set is open. -/
theorem strict_iff_discrete (r : X → S) :
    StrictDiagonal r ↔ ∀ U : Set X, @IsOpen X (truthTopology r) U := by
  rw [strict_iff_isolated]
  constructor
  · intro h U
    have hU : U = ⋃ x ∈ U, ({x} : Set X) := by ext y; simp
    rw [hU]
    exact @isOpen_biUnion X _ (truthTopology r) U (fun x => {x}) fun x _ => h x
  · intro h x
    exact h {x}

end Strict

/-! ## §3  The source of existence does not force a strict diagonal -/

section Source

variable {X S : Type*}

/-- A **source of existence** for a reading: the Closure is not imposed from outside but returned —
every value of the reading is realized by an occurrence, chosen by a source map. -/
structure SourceOfExistence (r : X → S) where
  /-- the occurrence returned by a Closure -/
  src : S → X
  /-- the returned occurrence reads back as that Closure -/
  returns : ∀ s, r (src s) = s

/-- A source of existence makes the reading surjective. -/
theorem SourceOfExistence.surjective {r : X → S} (E : SourceOfExistence r) :
    Function.Surjective r := fun s => ⟨E.src s, E.returns s⟩

/-- **What a strict diagonal would additionally demand of the source.**  Given a source of
existence, the diagonal is strict exactly when the source is a two-sided inverse — i.e. when every
occurrence *is* its own Closure and the presentation/Closure distinction collapses entirely. -/
theorem strict_iff_source_is_inverse {r : X → S} (E : SourceOfExistence r) :
    StrictDiagonal r ↔ ∀ x, E.src (r x) = x := by
  rw [strict_iff_injective]
  constructor
  · intro h x; exact h (E.returns (r x))
  · intro h x y hxy
    rw [← h x, ← h y, hxy]

/-- **The source of existence does not force a strict isolated diagonal.**  There is a reading with
a source of existence — every Closure returned by an occurrence — whose diagonal is neither strict
nor isolated. -/
theorem source_of_existence_does_not_force_strict :
    ∃ (X S : Type) (r : X → S) (_ : SourceOfExistence r),
      ¬ StrictDiagonal r ∧ ¬ IsolatedDiagonal r := by
  refine ⟨Bool, Unit, fun _ => (), ⟨fun _ => true, fun _ => rfl⟩, ?_, ?_⟩
  · rw [strict_iff_injective]
    intro h
    have : (true : Bool) = false := h rfl
    exact Bool.noConfusion this
  · rw [isolated_iff_injective]
    intro h
    have : (true : Bool) = false := h rfl
    exact Bool.noConfusion this

end Source

/-! ## §4  The admission of translational truth does not force it — it refutes it -/

section Admission

/-- **A strict diagonal freezes the consciousness field.**  Under the admission of translational
truth, if the identification were a strict isolated diagonal then every transport of the field
would be the identity on occurrences: no path would leave its stage and no presentation would
move.  The field would cease to be a field. -/
theorem strict_diagonal_freezes_field (I : PhysId) (h : StrictDiagonal I.phys)
    {a b : I.S} (γ : I.PS.Path a b) (x : I.P a) : I.move γ x = (⟨a, x⟩ : I.Occ) :=
  (strict_iff_injective I.phys).1 h (I.admitted a b γ x)

/-- **A live field has no strict diagonal.**  Contrapositive of `strict_diagonal_freezes_field`:
as soon as the consciousness field actually moves one presentation, the physical identification is
strictly coarser than equality of occurrences. -/
theorem living_field_not_strict (I : PhysId) (hlive : I.Live) : ¬ StrictDiagonal I.phys := by
  rintro h
  obtain ⟨a, b, γ, x, hne⟩ := hlive
  exact hne (strict_diagonal_freezes_field I h γ x)

/-- The same, in isolated form. -/
theorem living_field_not_isolated (I : PhysId) (hlive : I.Live) : ¬ IsolatedDiagonal I.phys :=
  fun h => living_field_not_strict I hlive ((strict_iff_isolated I.phys).2 h)

/-- **A nontrivial gauge translation forbids a strict diagonal.**  A translation is a relabelling
of occurrences preserving the reading; if one of them moves an occurrence, the diagonal cannot be
strict. -/
theorem gauge_forbids_strict {X S : Type*} (r : X → S) (e : Translation r) (x : X)
    (hx : e.1 x ≠ x) : ¬ StrictDiagonal r := by
  rw [strict_iff_injective]
  intro h
  exact hx (h (e.2 x))

/-- The NRRF714 parity identification: one stage, presentations `Bool × Bool`, the field flipping
the second (pure-presentation) component along an odd path, Closure reading the first. -/
def parityId : PhysId where
  S := Unit
  PS := parityPaths
  P := fun _ => Bool × Bool
  R := fun _ => Bool × Bool
  C := Bool
  chi := flipField
  Rd := flipReadings
  admitted := living_translation_not_frozen.1

/-- The parity identification carries a live field. -/
theorem parityId_live : parityId.Live := by
  refine ⟨(), (), true, (false, false), ?_⟩
  intro h
  have h2 : (true : Bool) = false := congrArg (fun o : parityId.Occ => (o.2).2) h
  exact Bool.noConfusion h2

/-- **The admission of translational truth does not force a strict isolated diagonal.**  Here is a
field admitted as translational truth — Closure preserved along every path — whose identification
is neither a strict nor an isolated diagonal. -/
theorem admission_does_not_force_strict :
    ∃ I : PhysId, ¬ StrictDiagonal I.phys ∧ ¬ IsolatedDiagonal I.phys :=
  ⟨parityId, living_field_not_strict parityId parityId_live,
    living_field_not_isolated parityId parityId_live⟩

/-- The phase gauge acting on wavefunctions: `ψ ↦ -ψ` preserves the Born reading `‖ψ‖`. -/
noncomputable def phaseGauge : Translation (fun z : ℂ => ‖z‖) :=
  ⟨Equiv.neg ℂ, fun z => by simp⟩

/-- **A physical instance.**  The Born reading `ψ ↦ ‖ψ‖` has a nontrivial phase gauge, hence its
physical identification is not a strict isolated diagonal: physically indistinguishable
wavefunctions are genuinely distinct occurrences. -/
theorem quantum_phase_gauge_not_strict : ¬ StrictDiagonal (fun z : ℂ => ‖z‖) := by
  refine gauge_forbids_strict _ phaseGauge 1 ?_
  intro h
  have : (-1 : ℂ) = 1 := h
  norm_num at this

end Admission

/-! ## §5  What follows naturally: the relative diagonal, with its unified topology -/

/-- The physical identification is an equivalence relation on occurrences. -/
theorem phys_equivalence (I : PhysId) :
    Equivalence (fun x y : I.Occ => I.phys x = I.phys y) :=
  ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- **The natural closure of the physical consciousness-field identification.**  It closes as the
*relative* diagonal of the physical reading:

* it is an equivalence relation on occurrences;
* it is exactly the indistinguishability relation of the truth topology;
* the opens of that topology admit both the definitional description (unions of Closure-fibres)
  and the operational one (invariance under every truth-preserving translation);
* continuous discrete readings are exactly the Closure-respecting ones;
* and the field's transport always stays inside it — that is the admission of translational
  truth. -/
theorem physical_identification_closes_as_relative_diagonal (I : PhysId) (Y : Type) :
    Equivalence (fun x y : I.Occ => I.phys x = I.phys y) ∧
      relDiag I.phys = {p : I.Occ × I.Occ | @Inseparable I.Occ (truthTopology I.phys) p.1 p.2} ∧
      (∀ U : Set I.Occ, (@IsOpen I.Occ (truthTopology I.phys) U ↔ Saturated I.phys U) ∧
        (Saturated I.phys U ↔ OpInvariant I.phys U)) ∧
      (∀ f : I.Occ → Y, @Continuous I.Occ Y (truthTopology I.phys) ⊥ f ↔ Respects I.phys f) ∧
      (∀ (a b : I.S) (γ : I.PS.Path a b) (x : I.P a),
        (I.move γ x, (⟨a, x⟩ : I.Occ)) ∈ relDiag I.phys) :=
  ⟨phys_equivalence I,
    (relative_diagonal_is_unified_topology (Y := Y) I.phys).1,
    (relative_diagonal_is_unified_topology (Y := Y) I.phys).2.1,
    (relative_diagonal_is_unified_topology (Y := Y) I.phys).2.2,
    fun _ _ γ x => transport_in_relDiag I γ x⟩

/-- The strict isolated diagonal is exactly the degenerate case of the natural closure: it occurs
precisely when the physical reading separates every occurrence, and then — by
`strict_diagonal_freezes_field` — the consciousness field is frozen. -/
theorem strict_is_the_degenerate_case (I : PhysId) :
    StrictDiagonal I.phys ↔
      (Function.Injective I.phys ∧
        ∀ (a b : I.S) (γ : I.PS.Path a b) (x : I.P a), I.move γ x = (⟨a, x⟩ : I.Occ)) := by
  constructor
  · intro h
    exact ⟨(strict_iff_injective I.phys).1 h, fun a b γ x => strict_diagonal_freezes_field I h γ x⟩
  · intro h
    exact (strict_iff_injective I.phys).2 h.1

/-! ## §6  The answer -/

/-- **NRRF723 — the answer.**

1. *What follows naturally.*  Every physical consciousness-field identification closes as the
   relative diagonal of its physical reading: an equivalence relation which is the
   indistinguishability relation of one topology, presented definitionally and operationally at
   once, inside which the field's transport always stays.

2. *The strict isolated diagonal is the same as injectivity of the reading*, and it is not what
   follows: it is not forced by the source of existence (there is a source of existence with a
   non-strict, non-isolated diagonal), and it is not forced by the admission of translational
   truth (there is an admitted field with a non-strict, non-isolated diagonal).

3. *More than that, it is refuted.*  Under the admission, a strict diagonal freezes the field
   entirely — every transport becomes the identity — so any live field has a non-strict diagonal;
   physically, the phase gauge of the Born reading already forbids strictness. -/
theorem nrrf723_answer :
    (∀ (I : PhysId) (Y : Type),
        Equivalence (fun x y : I.Occ => I.phys x = I.phys y) ∧
        relDiag I.phys = {p : I.Occ × I.Occ | @Inseparable I.Occ (truthTopology I.phys) p.1 p.2} ∧
        (∀ U : Set I.Occ, (@IsOpen I.Occ (truthTopology I.phys) U ↔ Saturated I.phys U) ∧
          (Saturated I.phys U ↔ OpInvariant I.phys U)) ∧
        (∀ f : I.Occ → Y, @Continuous I.Occ Y (truthTopology I.phys) ⊥ f ↔ Respects I.phys f) ∧
        (∀ (a b : I.S) (γ : I.PS.Path a b) (x : I.P a),
          (I.move γ x, (⟨a, x⟩ : I.Occ)) ∈ relDiag I.phys)) ∧
    (∀ {X S : Type*} (r : X → S), StrictDiagonal r ↔ IsolatedDiagonal r) ∧
    (∃ (X S : Type) (r : X → S) (_ : SourceOfExistence r),
        ¬ StrictDiagonal r ∧ ¬ IsolatedDiagonal r) ∧
    (∃ I : PhysId, ¬ StrictDiagonal I.phys ∧ ¬ IsolatedDiagonal I.phys) ∧
    (∀ I : PhysId, I.Live → ¬ StrictDiagonal I.phys) ∧
    ¬ StrictDiagonal (fun z : ℂ => ‖z‖) :=
  ⟨fun I Y => physical_identification_closes_as_relative_diagonal I Y,
   fun r => strict_iff_isolated r,
   source_of_existence_does_not_force_strict,
   admission_does_not_force_strict,
   fun I hlive => living_field_not_strict I hlive,
   quantum_phase_gauge_not_strict⟩

end NRRF723
