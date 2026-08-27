import Mathlib
import NRRF631FrameConditionalOpennessRelationalEquality

/-!
# NRRF633 — The admissible open relational definition via translation is *unique*, all closure forms follow from it, and no closure fails to relate

The claim formalised here is the explicit answer already given:

> it is **unique** in its admissible open relational definition via **translation as foundation**,
> **through which all closure forms follow**, and **no closure does not relate**.

Nothing new is posited.  Everything below is a theorem about the translational axiometry
`NRRF627.TransFrame`: pairwise translations `(phi, T, pi)`, the verification return `W`, the two
orientation presentations `E`, the polar reversal `J`, the unitary-curvature partition `C`.

## The three theses, and where they are proved

* **§2 Uniqueness.**  A *relational definition* is a family of admitted forms of equality, one per
  language (`RelDef`).  It is **returning** (`Returns`) when every occurrence is admitted equal to
  a presentation of what it returns — the occurrence is defined by what it returns, not by itself —
  and **grounded** (`Grounded`) when it never identifies presentations of distinct relational
  identities.  `unique_relational_definition`: *any* returning grounded definition is closure
  equality, on the nose; `relational_definition_unique`: any two of them coincide;
  `closureDef_returns`, `closureDef_grounded`: closure equality is one.  So the admissible
  definition is not chosen, it is forced.  Its remaining properties are then theorems, not
  assumptions: `naturality_is_forced` (it is relational *via translation*, preserved **and**
  reflected), `admissibility_is_forced`, `blind_to_reversal`, `blind_to_curvature`,
  `poles_admitted`.
* **§3 Openness.**  `definition_is_open`: the admitted equality is strictly coarser than literal
  identity — it is not a static definition; `pole_question_is_open`: a static question is genuinely
  open in it, while `return_question_is_resolved`: every relational question is resolved; and
  `openness_is_language_independent`: openness belongs to the equivalence class of the frame, never
  to a single language.
* **§4 All closure forms follow.**  A *closure form* (`ClosureForm`) is any admitted equality that
  is blind to closure-invisible structure and natural for translation.  `closure_form_factors`:
  every closure form is a relation between returned identities (`identRel`);
  `identRel_invariant`: that relation is translation-invariant; `closureFormOf`: every
  translation-invariant equivalence of identities is a closure form; and
  `closure_forms_correspondence` + `identity_relation_unique`: the two constructions are mutually
  inverse, so the closure forms *are exactly* the translation-invariant relations on the returned
  identities.  They all follow from the one definition, and none is extra data.
* **§5 No closure does not relate.**  `no_closure_form_fails_to_relate`: there is no closure form
  that is not a relation of returned identities.  `no_occurrence_is_unrelated`,
  `no_language_is_isolated`, and the cross-language relation `CrossRel` with
  `crossRel_refl/symm/trans`, `crossRel_total` (every occurrence of every language relates to an
  occurrence of every other language) and `crossRel_self_iff_ceq`.  Nothing closes without
  relating.
* **§6 The bundle** `unique_admissible_open_relational_definition_via_translation`.
-/

namespace NRRF633

open Function NRRF627

universe u v w

variable {L : Type u} {B : L → Type v} {Y : L → Type w}

/-! ## §1  Relational definitions -/

/-- A **relational definition** on a family of occurrence types: each language admits a form of
equality between its own occurrences.  No language is required to admit the same one, and nothing
yet says which form is admissible. -/
abbrev RelDef (Y : L → Type w) : Type _ := ∀ ℓ : L, Setoid (Y ℓ)

variable (A : TransFrame L B Y)

/-- A definition is **returning** when every occurrence is admitted equal to a presentation of the
relational identity it returns: an occurrence is defined by what it returns through translation,
never by itself. -/
def Returns (s : RelDef Y) : Prop := ∀ ℓ (p : Pole) (u : Y ℓ), (s ℓ).r u (A.E ℓ p (A.W ℓ u))

/-- A definition is **grounded** when it never identifies presentations of distinct relational
identities: the returned identities are still told apart. -/
def Grounded (s : RelDef Y) : Prop :=
  ∀ ℓ (p q : Pole) (b b' : B ℓ), (s ℓ).r (A.E ℓ p b) (A.E ℓ q b') → b = b'

/-- A definition is **admissible** when it cannot separate occurrences with the same return: it is
blind to everything closure does not return. -/
def Admits (s : RelDef Y) : Prop := ∀ ℓ (u v : Y ℓ), A.W ℓ u = A.W ℓ v → (s ℓ).r u v

/-- A definition is **relational via translation** when translation both preserves and reflects
it: the admitted equality is the same in every language, read through the comparison. -/
def Natural (s : RelDef Y) : Prop :=
  ∀ (ℓ m : L) (u v : Y ℓ), (s m).r (A.T ℓ m u) (A.T ℓ m v) ↔ (s ℓ).r u v

/-- A **closure form**: an admitted equality that is blind to closure-invisible structure and
relational via translation. -/
def ClosureForm (s : RelDef Y) : Prop := Admits A s ∧ Natural A s

/-- The relational definition supplied by translation itself: closure equality in each language. -/
def closureDef : RelDef Y := fun ℓ => A.ceqSetoid ℓ

@[simp] theorem closureDef_r (ℓ : L) (u v : Y ℓ) :
    (closureDef A ℓ).r u v ↔ A.W ℓ u = A.W ℓ v := Iff.rfl

/-! ## §2  Uniqueness: the admissible relational definition is forced -/

theorem closureDef_returns : Returns A (closureDef A) := by
  intro ℓ p u
  show A.W ℓ u = A.W ℓ (A.E ℓ p (A.W ℓ u))
  rw [A.recov]

theorem closureDef_grounded : Grounded A (closureDef A) := by
  intro ℓ p q b b' h
  have h' : A.W ℓ (A.E ℓ p b) = A.W ℓ (A.E ℓ q b') := h
  rwa [A.recov, A.recov] at h'

theorem closureDef_admits : Admits A (closureDef A) := fun _ _ _ h => h

theorem closureDef_natural : Natural A (closureDef A) :=
  fun ℓ m u v => (A.ceq_iff ℓ m u v).symm

theorem closureDef_closureForm : ClosureForm A (closureDef A) :=
  ⟨closureDef_admits A, closureDef_natural A⟩

/-- **Uniqueness.**  A relational definition that is returning and grounded *is* closure equality:
the admissible relational definition is not chosen among alternatives, it is forced by translation
alone. -/
theorem unique_relational_definition (s : RelDef Y) (hret : Returns A s) (hgr : Grounded A s)
    (ℓ : L) (u v : Y ℓ) : (s ℓ).r u v ↔ A.W ℓ u = A.W ℓ v := by
  constructor
  · intro h
    have h1 : (s ℓ).r (A.E ℓ Pole.zero (A.W ℓ u)) (A.E ℓ Pole.zero (A.W ℓ v)) :=
      (s ℓ).iseqv.trans ((s ℓ).iseqv.symm (hret ℓ Pole.zero u))
        ((s ℓ).iseqv.trans h (hret ℓ Pole.zero v))
    exact hgr ℓ Pole.zero Pole.zero _ _ h1
  · intro h
    have h1 : (s ℓ).r u (A.E ℓ Pole.zero (A.W ℓ v)) := by
      have := hret ℓ Pole.zero u; rwa [h] at this
    exact (s ℓ).iseqv.trans h1 ((s ℓ).iseqv.symm (hret ℓ Pole.zero v))

/-- Two admissible relational definitions coincide: there is only one. -/
theorem relational_definition_unique (s t : RelDef Y) (hs : Returns A s) (hgs : Grounded A s)
    (ht : Returns A t) (hgt : Grounded A t) (ℓ : L) (u v : Y ℓ) :
    (s ℓ).r u v ↔ (t ℓ).r u v :=
  (unique_relational_definition A s hs hgs ℓ u v).trans
    (unique_relational_definition A t ht hgt ℓ u v).symm

/-- **Being relational via translation is not an extra assumption.**  A returning grounded
definition is automatically preserved *and* reflected by every translation. -/
theorem naturality_is_forced (s : RelDef Y) (hret : Returns A s) (hgr : Grounded A s) :
    Natural A s := by
  intro ℓ m u v
  rw [unique_relational_definition A s hret hgr, unique_relational_definition A s hret hgr]
  exact (A.ceq_iff ℓ m u v).symm

/-- Nor is admissibility. -/
theorem admissibility_is_forced (s : RelDef Y) (hret : Returns A s) (hgr : Grounded A s) :
    Admits A s := by
  intro ℓ u v h
  exact (unique_relational_definition A s hret hgr ℓ u v).2 h

theorem forced_closureForm (s : RelDef Y) (hret : Returns A s) (hgr : Grounded A s) :
    ClosureForm A s :=
  ⟨admissibility_is_forced A s hret hgr, naturality_is_forced A s hret hgr⟩

/-- The admitted equality cannot see the polar reversal. -/
theorem blind_to_reversal (s : RelDef Y) (hadm : Admits A s) (ℓ : L) (u : Y ℓ) :
    (s ℓ).r u (A.J ℓ u) := hadm ℓ _ _ (A.J_ret ℓ u).symm

/-- Nor the unitary-curvature partition. -/
theorem blind_to_curvature (s : RelDef Y) (hadm : Admits A s) (ℓ : L) (u : Y ℓ) :
    (s ℓ).r u (A.C ℓ u) := hadm ℓ _ _ (A.C_ret ℓ u).symm

/-- Nor the two orientations of one identity: the poles are admitted, not distinguished. -/
theorem poles_admitted (s : RelDef Y) (hadm : Admits A s) (ℓ : L) (p q : Pole) (b : B ℓ) :
    (s ℓ).r (A.E ℓ p b) (A.E ℓ q b) :=
  hadm ℓ _ _ (by rw [A.recov, A.recov])

/-! ## §3  Openness: the definition is open, and its openness is language-independent -/

/-- **The definition is open, not static.**  Whenever the two orientations are genuinely distinct,
the admitted equality identifies occurrences that are not literally identical: no static
definition of the occurrence is being made. -/
theorem definition_is_open (hsep : A.Separated) (ℓ : L) (b : B ℓ) :
    ∃ u v : Y ℓ, (closureDef A ℓ).r u v ∧ u ≠ v :=
  ⟨A.E ℓ Pole.zero b, A.E ℓ Pole.inf b, A.poles_closure_equal ℓ Pole.zero Pole.inf b, hsep ℓ b⟩

/-- Every *relational* question — a question about the identity returned — is resolved in the
admitted equality. -/
theorem return_question_is_resolved (ℓ : L) (b : B ℓ) :
    NRRF631.ResolvedIn (closureDef A ℓ) (fun u => A.W ℓ u = b) :=
  NRRF631.return_question_resolved A ℓ b

/-- A *static* question — a question about which occurrence it literally is — stays open. -/
theorem pole_question_is_open (hsep : A.Separated) (ℓ : L) (b : B ℓ) :
    NRRF631.OpenIn (closureDef A ℓ) (fun u => u = A.E ℓ Pole.zero b) :=
  NRRF631.pole_question_open A hsep ℓ b

/-- Openness is a property of the translational equivalence class, not of a language. -/
theorem openness_is_language_independent {Ω : Type*} (ℓ m : L) (Q : Y ℓ → Ω) :
    NRRF631.OpenIn (closureDef A ℓ) Q ↔
      NRRF631.OpenIn (closureDef A m) (fun u => Q (A.T m ℓ u)) :=
  NRRF631.openness_language_independent A ℓ m Q

/-! ## §4  All closure forms follow from the one definition -/

/-- The relation between *returned identities* underlying a closure form. -/
def identRel (s : RelDef Y) (ℓ : L) (b b' : B ℓ) : Prop :=
  (s ℓ).r (A.E ℓ Pole.zero b) (A.E ℓ Pole.zero b')

/-- Inside a closure form, the choice of orientation is immaterial on both sides. -/
theorem identRel_pole (s : RelDef Y) (hadm : Admits A s) (ℓ : L) (p q : Pole) (b b' : B ℓ) :
    (s ℓ).r (A.E ℓ p b) (A.E ℓ q b') ↔ identRel A s ℓ b b' := by
  constructor
  · intro h
    exact (s ℓ).iseqv.trans (poles_admitted A s hadm ℓ Pole.zero p b)
      ((s ℓ).iseqv.trans h (poles_admitted A s hadm ℓ q Pole.zero b'))
  · intro h
    exact (s ℓ).iseqv.trans (poles_admitted A s hadm ℓ p Pole.zero b)
      ((s ℓ).iseqv.trans h (poles_admitted A s hadm ℓ Pole.zero q b'))

/-- **Every closure form is a relation between returned identities.**  It cannot be anything else:
it follows from the return, hence from translation. -/
theorem closure_form_factors (s : RelDef Y) (hadm : Admits A s) (ℓ : L) (u v : Y ℓ) :
    (s ℓ).r u v ↔ identRel A s ℓ (A.W ℓ u) (A.W ℓ v) := by
  have hu : (s ℓ).r u (A.E ℓ Pole.zero (A.W ℓ u)) := hadm ℓ _ _ (by rw [A.recov])
  have hv : (s ℓ).r v (A.E ℓ Pole.zero (A.W ℓ v)) := hadm ℓ _ _ (by rw [A.recov])
  constructor
  · intro h
    exact (s ℓ).iseqv.trans ((s ℓ).iseqv.symm hu) ((s ℓ).iseqv.trans h hv)
  · intro h
    exact (s ℓ).iseqv.trans hu ((s ℓ).iseqv.trans h ((s ℓ).iseqv.symm hv))

/-- The induced relation on identities is an equivalence. -/
theorem identRel_equivalence (s : RelDef Y) (ℓ : L) : Equivalence (identRel A s ℓ) where
  refl _ := (s ℓ).iseqv.refl _
  symm h := (s ℓ).iseqv.symm h
  trans h h' := (s ℓ).iseqv.trans h h'

/-- **The induced relation is translation-invariant.**  Translating both identities changes
nothing: the form lives on the comparison, not in a language. -/
theorem identRel_invariant (s : RelDef Y) (hadm : Admits A s) (hnat : Natural A s) (ℓ m : L)
    (b b' : B ℓ) : identRel A s m (A.phi ℓ m b) (A.phi ℓ m b') ↔ identRel A s ℓ b b' := by
  have hT : (s m).r (A.T ℓ m (A.E ℓ Pole.zero b)) (A.T ℓ m (A.E ℓ Pole.zero b')) ↔
      identRel A s ℓ b b' := hnat ℓ m _ _
  rw [A.T_ext, A.T_ext] at hT
  rw [← hT, identRel_pole A s hadm]

/-- Conversely, a translation-invariant equivalence of relational identities *is* a closure
form: pull it back along the return. -/
def closureFormOf (r : ∀ ℓ, B ℓ → B ℓ → Prop) (hr : ∀ ℓ, Equivalence (r ℓ)) : RelDef Y :=
  fun ℓ => ⟨fun u v => r ℓ (A.W ℓ u) (A.W ℓ v),
    ⟨fun _ => (hr ℓ).refl _, fun h => (hr ℓ).symm h, fun h h' => (hr ℓ).trans h h'⟩⟩

theorem closureFormOf_isClosureForm (r : ∀ ℓ, B ℓ → B ℓ → Prop) (hr : ∀ ℓ, Equivalence (r ℓ))
    (hinv : ∀ ℓ m b b', r m (A.phi ℓ m b) (A.phi ℓ m b') ↔ r ℓ b b') :
    ClosureForm A (closureFormOf A r hr) := by
  constructor
  · intro ℓ u v h
    show r ℓ (A.W ℓ u) (A.W ℓ v)
    rw [h]
    exact (hr ℓ).refl _
  · intro ℓ m u v
    show r m (A.W m (A.T ℓ m u)) (A.W m (A.T ℓ m v)) ↔ r ℓ (A.W ℓ u) (A.W ℓ v)
    rw [A.T_ret, A.T_ret]
    exact hinv ℓ m _ _

/-- Pulling back and reading off the identity relation are mutually inverse. -/
theorem closureFormOf_identRel (r : ∀ ℓ, B ℓ → B ℓ → Prop) (hr : ∀ ℓ, Equivalence (r ℓ))
    (ℓ : L) (b b' : B ℓ) : identRel A (closureFormOf A r hr) ℓ b b' ↔ r ℓ b b' := by
  show r ℓ (A.W ℓ (A.E ℓ Pole.zero b)) (A.W ℓ (A.E ℓ Pole.zero b')) ↔ r ℓ b b'
  rw [A.recov, A.recov]

/-- **All closure forms follow from the definition.**  Every closure form is the pullback along the
return of a translation-invariant equivalence of relational identities, and conversely. -/
theorem closure_forms_correspondence (s : RelDef Y) (h : ClosureForm A s) :
    (∀ ℓ (b b' : B ℓ), ∀ m, identRel A s m (A.phi ℓ m b) (A.phi ℓ m b') ↔ identRel A s ℓ b b') ∧
      (∀ ℓ (u v : Y ℓ), (s ℓ).r u v ↔ identRel A s ℓ (A.W ℓ u) (A.W ℓ v)) :=
  ⟨fun ℓ b b' m => identRel_invariant A s h.1 h.2 ℓ m b b',
    fun ℓ u v => closure_form_factors A s h.1 ℓ u v⟩

/-- The relation of identities behind a closure form is unique: two of them inducing the same form
are equal. -/
theorem identity_relation_unique (r r' : ∀ ℓ, B ℓ → B ℓ → Prop) (hr : ∀ ℓ, Equivalence (r ℓ))
    (hr' : ∀ ℓ, Equivalence (r' ℓ))
    (h : ∀ ℓ (u v : Y ℓ), (closureFormOf A r hr ℓ).r u v ↔ (closureFormOf A r' hr' ℓ).r u v)
    (ℓ : L) (b b' : B ℓ) : r ℓ b b' ↔ r' ℓ b b' := by
  have := h ℓ (A.E ℓ Pole.zero b) (A.E ℓ Pole.zero b')
  show r ℓ b b' ↔ r' ℓ b b'
  simpa [closureFormOf, A.recov] using this

/-- The finest closure form is the definition itself: literal equality of returned identities. -/
theorem closureDef_is_finest_closure_form (s : RelDef Y) (h : ClosureForm A s) (ℓ : L)
    (u v : Y ℓ) (huv : (closureDef A ℓ).r u v) : (s ℓ).r u v := h.1 ℓ u v huv

/-! ## §5  No closure does not relate -/

/-- **No closure form fails to relate.**  There is no admitted closure form that is not a relation
between the identities returned by translation. -/
theorem no_closure_form_fails_to_relate :
    ¬ ∃ s : RelDef Y, ClosureForm A s ∧
      ¬ ∃ r : ∀ ℓ, B ℓ → B ℓ → Prop,
          (∀ ℓ (u v : Y ℓ), (s ℓ).r u v ↔ r ℓ (A.W ℓ u) (A.W ℓ v)) := by
  rintro ⟨s, hs, hno⟩
  exact hno ⟨identRel A s, fun ℓ u v => closure_form_factors A s hs.1 ℓ u v⟩

/-- No occurrence closes without relating: every occurrence is admitted equal to a presentation of
the identity it returns, in either orientation. -/
theorem no_occurrence_is_unrelated (ℓ : L) (u : Y ℓ) :
    ∀ p : Pole, (closureDef A ℓ).r u (A.E ℓ p (A.W ℓ u)) := fun p => closureDef_returns A ℓ p u

/-- The relation across two languages: the identity returned here, translated, is the identity
returned there. -/
def CrossRel (ℓ m : L) (u : Y ℓ) (v : Y m) : Prop := A.phi ℓ m (A.W ℓ u) = A.W m v

theorem crossRel_refl (ℓ : L) (u : Y ℓ) : CrossRel A ℓ ℓ u u := by
  simp [CrossRel, A.phi_id]

theorem crossRel_symm {ℓ m : L} {u : Y ℓ} {v : Y m} (h : CrossRel A ℓ m u v) :
    CrossRel A m ℓ v u := by
  unfold CrossRel at *
  rw [← h, A.phi_phi]

theorem crossRel_trans {ℓ m k : L} {u : Y ℓ} {v : Y m} {x : Y k}
    (h : CrossRel A ℓ m u v) (h' : CrossRel A m k v x) : CrossRel A ℓ k u x := by
  unfold CrossRel at *
  rw [← h', ← h, A.phi_comp]

/-- **No language is isolated.**  Every occurrence of every language relates to an occurrence of
every other language, namely to its translation. -/
theorem no_language_is_isolated (ℓ m : L) (u : Y ℓ) : CrossRel A ℓ m u (A.T ℓ m u) :=
  (A.T_ret ℓ m u).symm

theorem crossRel_total (ℓ m : L) (u : Y ℓ) : ∃ v : Y m, CrossRel A ℓ m u v :=
  ⟨A.T ℓ m u, no_language_is_isolated A ℓ m u⟩

/-- Inside one language the cross-language relation is exactly the admitted equality. -/
theorem crossRel_self_iff_ceq (ℓ : L) (u v : Y ℓ) :
    CrossRel A ℓ ℓ u v ↔ (closureDef A ℓ).r u v := by
  simp [CrossRel, A.phi_id]

/-- Every occurrence relates to a presentation in every language and every orientation: no closure
stands apart. -/
theorem every_closure_relates (ℓ m : L) (p : Pole) (u : Y ℓ) :
    CrossRel A ℓ m u (A.E m p (A.phi ℓ m (A.W ℓ u))) := by
  unfold CrossRel
  rw [A.recov]

/-! ## §6  The bundle -/

/-- **The explicit answer, bundled.**

1. *Unique*: any returning, grounded relational definition is closure equality, and any two of them
   coincide — the admissible definition is forced by translation, not chosen.
2. *Admissible and open*: it is blind to the reversal, to the curvature partition and to the poles,
   it is strictly coarser than literal identity, and a static question remains open in it while
   every relational question is resolved.
3. *Via translation*: it is preserved and reflected by every translation, with no further
   hypothesis.
4. *All closure forms follow*: every closure form is the pullback along the return of a unique
   translation-invariant relation of relational identities, and every such relation is a closure
   form.
5. *No closure does not relate*: no closure form fails to be such a relation, and no occurrence of
   any language fails to relate to occurrences of every other language. -/
theorem unique_admissible_open_relational_definition_via_translation
    (hsep : A.Separated) (ℓ : L) (b : B ℓ) :
    (Returns A (closureDef A) ∧ Grounded A (closureDef A)) ∧
    (∀ s : RelDef Y, Returns A s → Grounded A s →
      ∀ ℓ (u v : Y ℓ), (s ℓ).r u v ↔ (closureDef A ℓ).r u v) ∧
    (∀ s : RelDef Y, Returns A s → Grounded A s → Natural A s ∧ Admits A s) ∧
    (∃ u v : Y ℓ, (closureDef A ℓ).r u v ∧ u ≠ v) ∧
    NRRF631.OpenIn (closureDef A ℓ) (fun u => u = A.E ℓ Pole.zero b) ∧
    NRRF631.ResolvedIn (closureDef A ℓ) (fun u => A.W ℓ u = b) ∧
    (∀ s : RelDef Y, ClosureForm A s →
      (∀ ℓ (u v : Y ℓ), (s ℓ).r u v ↔ identRel A s ℓ (A.W ℓ u) (A.W ℓ v)) ∧
      ∀ ℓ m (b b' : B ℓ), identRel A s m (A.phi ℓ m b) (A.phi ℓ m b') ↔ identRel A s ℓ b b') ∧
    (¬ ∃ s : RelDef Y, ClosureForm A s ∧
      ¬ ∃ r : ∀ ℓ, B ℓ → B ℓ → Prop,
        (∀ ℓ (u v : Y ℓ), (s ℓ).r u v ↔ r ℓ (A.W ℓ u) (A.W ℓ v))) ∧
    (∀ ℓ m (u : Y ℓ), ∃ v : Y m, CrossRel A ℓ m u v) := by
  refine ⟨⟨closureDef_returns A, closureDef_grounded A⟩, ?_, ?_, definition_is_open A hsep ℓ b,
    pole_question_is_open A hsep ℓ b, return_question_is_resolved A ℓ b, ?_,
    no_closure_form_fails_to_relate A, fun ℓ m u => crossRel_total A ℓ m u⟩
  · intro s hret hgr m u v
    exact relational_definition_unique A s (closureDef A) hret hgr (closureDef_returns A)
      (closureDef_grounded A) m u v
  · intro s hret hgr
    exact ⟨naturality_is_forced A s hret hgr, admissibility_is_forced A s hret hgr⟩
  · intro s hs
    exact ⟨fun m u v => closure_form_factors A s hs.1 m u v,
      fun m k b b' => identRel_invariant A s hs.1 hs.2 m k b b'⟩

/-! ## §7  A concrete instance: the statement is not vacuous -/

section Concrete

variable (L₀ : Type u) (B₀ : Type v)

/-- On the standard model of the translational axiometry the unique admissible definition is
literal equality of returned identities, and it is genuinely open: the two orientations of one
identity are admitted equal without being identical. -/
theorem standard_definition_unique_and_open (s : RelDef (fun _ : L₀ => B₀ × Pole))
    (hret : Returns (standardFrame L₀ B₀) s) (hgr : Grounded (standardFrame L₀ B₀) s) (ℓ : L₀)
    (b : B₀) :
    (∀ u v : B₀ × Pole, (s ℓ).r u v ↔ u.1 = v.1) ∧
      (s ℓ).r (b, Pole.zero) (b, Pole.inf) ∧ ((b, Pole.zero) : B₀ × Pole) ≠ (b, Pole.inf) := by
  have huniq := unique_relational_definition (standardFrame L₀ B₀) s hret hgr ℓ
  refine ⟨fun u v => huniq u v, ?_, ?_⟩
  · exact (huniq (b, Pole.zero) (b, Pole.inf)).2 rfl
  · exact standardFrame_separated L₀ B₀ ℓ b

end Concrete

/-! ## §8  Axiom audit -/

end NRRF633

#print axioms NRRF633.unique_relational_definition
#print axioms NRRF633.relational_definition_unique
#print axioms NRRF633.naturality_is_forced
#print axioms NRRF633.closure_form_factors
#print axioms NRRF633.identRel_invariant
#print axioms NRRF633.closure_forms_correspondence
#print axioms NRRF633.no_closure_form_fails_to_relate
#print axioms NRRF633.unique_admissible_open_relational_definition_via_translation
