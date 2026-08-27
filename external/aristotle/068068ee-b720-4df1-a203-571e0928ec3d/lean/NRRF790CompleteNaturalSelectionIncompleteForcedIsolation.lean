import Mathlib
import NRRF775NaturalFormSelectorUnifaceRelationalDeterminationUnitaryPathPartitionTraces

/-!
# NRRF790 — Complete and incomplete are natural selections and forced isolations respectively

The reading being formalised:

> Complete, incomplete are natural selections and forced isolations respectively.

A **reading** of a datum is the predicate `P : S → Prop` recording which symbols of a field `S`
the datum admits.  Nothing else is assumed: no coding, no order, no measure.  The module proves
that the completeness of a reading is *exactly* the availability of a natural selection, and that
incompleteness is *exactly* the necessity of a forced isolation.

* **§1 Selection and isolation.**  A *natural selection* of `P` is an admissible symbol fixed by
  every symmetry of `P` (`NaturalSelection`); an *isolation* of `P` at `c` is the strengthening of
  `P` to the single symbol `c` (`Isolate`), and it is *forced* when `c` is admissible but the
  strengthening is strict (`ForcedIsolation`).
* **§2 Complete = naturally selected.**  `complete_iff_exists_naturalSelection`: a reading is
  complete iff it has a natural selection, and then that selection is unique
  (`naturalSelection_unique`) and is the completing symbol (`theSelection`, `theSelection_spec`).
* **§3 Incomplete = forced isolation.**  For a non-empty incomplete reading, *every* admissible
  symbol is a forced isolation (`forcedIsolation_of_not_complete`), each such choice is broken by
  an explicit symmetry of the reading (`exists_symmetry_moving`), and on an admissible symbol
  natural selection and forced isolation are exact negations of one another
  (`naturalSelection_iff_not_forcedIsolation`).  The completions of a reading are precisely its
  isolations (`complete_sub_iff_isolate`), so completing an incomplete reading is nothing but
  isolating one admissible symbol.  An empty reading admits no selection at all
  (`no_selection_of_empty`): total isolation from the field.
* **§4 The dichotomy, and naturality.**  `complete_dichotomy` splits every non-empty reading into
  the naturally selected and the forcibly isolated case, exclusively
  (`not_natural_and_forced`).  Selection is natural in the field: it is invariant under the
  symmetries of the reading (`theSelection_symm_fixed`) and equivariant under translations of the
  symbol field (`theSelection_map`).
* **§5 No selector without completeness.**  On a field with two symbols there is no equivariant
  selector defined on all non-empty readings (`no_natural_selector`): away from completeness every
  choice is an isolation imposed by fiat.
* **§6 The stagewise form.**  Rigidity of an NRRF775 constraint is stagewise completeness
  (`rigid_iff_forall_complete`), the NRRF775 natural form is the stagewise natural selection
  (`sel_naturalSelection`), and a non-rigid stage forces isolation (`forcedIsolation_of_not_rigid`).
* **§7 Concrete readings.**  On `Bool`, the reading `· = false` is complete with natural selection
  `false`; the total reading is incomplete and both of its symbols are forced isolations.

`nrrf790_answer` collects the clauses.
-/

namespace NRRF790

variable {S T : Type*}

/-! ## §1 Completeness, selection, isolation -/

/-- **A complete reading**: exactly one symbol of the field is admissible. -/
def Complete (P : S → Prop) : Prop := ∃! s, P s

/-- A **symmetry** of a reading: a permutation of the symbol field preserving admissibility. -/
def Symmetry (P : S → Prop) (e : Equiv.Perm S) : Prop := ∀ s, P (e s) ↔ P s

/-- **A natural selection**: an admissible symbol that every symmetry of the reading fixes.  The
selection is then made by the reading itself, not by a choice on top of it. -/
def NaturalSelection (P : S → Prop) (c : S) : Prop :=
  P c ∧ ∀ e : Equiv.Perm S, Symmetry P e → e c = c

/-- **The isolation of a symbol**: the reading strengthened to the single symbol `c`. -/
def Isolate (c : S) : S → Prop := fun s => s = c

/-- One reading strengthens another. -/
def Stronger (Q P : S → Prop) : Prop := ∀ s, Q s → P s

/-- **A forced isolation**: `c` is admissible, and isolating it *strictly* strengthens the reading —
symbols the reading admits are cut away by the choice.  The isolation is forced in that the reading
does not itself perform it. -/
def ForcedIsolation (P : S → Prop) (c : S) : Prop :=
  P c ∧ Stronger (Isolate c) P ∧ ¬ Stronger P (Isolate c)

theorem isolate_stronger {P : S → Prop} {c : S} (hc : P c) : Stronger (Isolate c) P := by
  intro s hs; rw [show s = c from hs]; exact hc

theorem complete_isolate (c : S) : Complete (Isolate c) := ⟨c, rfl, fun _ h => h⟩

/-! ## §2 Complete readings are the naturally selected ones -/

/-- A complete reading naturally selects its unique symbol: no symmetry can move it. -/
theorem naturalSelection_of_complete {P : S → Prop} (h : Complete P) :
    NaturalSelection P h.choose := by
  obtain ⟨c, hc, huniq⟩ := id h
  have hch : h.choose = c := huniq _ h.choose_spec.1
  refine ⟨by rw [hch]; exact hc, fun e he => ?_⟩
  have : P (e h.choose) := (he _).mpr h.choose_spec.1
  rw [huniq _ this, huniq _ h.choose_spec.1]

/-- A natural selection forces completeness: if two symbols were admissible, the transposition
exchanging them would be a symmetry of the reading moving the selection. -/
theorem complete_of_naturalSelection [DecidableEq S] {P : S → Prop} {c : S}
    (h : NaturalSelection P c) : Complete P := by
  classical
  refine ⟨c, h.1, fun d hd => ?_⟩
  by_contra hne
  have hsym : Symmetry P (Equiv.swap c d) := by
    intro s
    by_cases hsc : s = c
    · subst hsc; simpa using iff_of_true hd h.1
    · by_cases hsd : s = d
      · subst hsd
        rw [Equiv.swap_apply_right]
        exact iff_of_true h.1 hd
      · rw [Equiv.swap_apply_of_ne_of_ne hsc hsd]
  have := h.2 _ hsym
  rw [Equiv.swap_apply_left] at this
  exact hne (this.symm ▸ rfl)

/-- **Complete is naturally selected.** -/
theorem complete_iff_exists_naturalSelection [DecidableEq S] {P : S → Prop} :
    Complete P ↔ ∃ c, NaturalSelection P c :=
  ⟨fun h => ⟨_, naturalSelection_of_complete h⟩, fun ⟨_, hc⟩ => complete_of_naturalSelection hc⟩

/-- A natural selection is unique. -/
theorem naturalSelection_unique [DecidableEq S] {P : S → Prop} {c d : S}
    (hc : NaturalSelection P c) (hd : NaturalSelection P d) : c = d := by
  obtain ⟨_, _, huniq⟩ := complete_of_naturalSelection hc
  rw [huniq _ hc.1, huniq _ hd.1]

/-- The symbol selected by a complete reading. -/
noncomputable def theSelection {P : S → Prop} (h : Complete P) : S := h.choose

theorem theSelection_spec {P : S → Prop} (h : Complete P) : P (theSelection h) := h.choose_spec.1

theorem theSelection_eq {P : S → Prop} (h : Complete P) {c : S} (hc : P c) :
    theSelection h = c := (h.choose_spec.2 _ hc).symm

/-- The selection of a complete reading is its natural selection. -/
theorem naturalSelection_theSelection {P : S → Prop} (h : Complete P) :
    NaturalSelection P (theSelection h) := naturalSelection_of_complete h

/-- The selection of a complete reading is fixed by every symmetry of it: it is natural. -/
theorem theSelection_symm_fixed {P : S → Prop} (h : Complete P) (e : Equiv.Perm S)
    (he : Symmetry P e) : e (theSelection h) = theSelection h :=
  (naturalSelection_of_complete h).2 e he

/-! ## §3 Incomplete readings force isolation -/

/-- An empty reading selects nothing: it is isolated from the whole symbol field. -/
theorem no_selection_of_empty {P : S → Prop} (h : ∀ s, ¬ P s) : ¬ ∃ c, NaturalSelection P c := by
  rintro ⟨c, hc, -⟩; exact h c hc

/-- **Incomplete is forced isolation**: in an incomplete reading, every admissible symbol can only
be chosen by cutting away other admissible symbols. -/
theorem forcedIsolation_of_not_complete {P : S → Prop} {c : S} (hc : P c) (h : ¬ Complete P) :
    ForcedIsolation P c := by
  refine ⟨hc, isolate_stronger hc, fun hstr => h ⟨c, hc, fun d hd => hstr d hd⟩⟩

/-- Conversely a forced isolation witnesses incompleteness. -/
theorem not_complete_of_forcedIsolation {P : S → Prop} {c : S} (h : ForcedIsolation P c) :
    ¬ Complete P := by
  obtain ⟨hc, -, hstr⟩ := h
  rintro ⟨d, hd, huniq⟩
  exact hstr fun s hs => by rw [huniq _ hs, huniq _ hc]; rfl

/-- A forced isolation cuts away a genuinely admissible symbol. -/
theorem exists_other_admissible {P : S → Prop} {c : S} (h : ForcedIsolation P c) :
    ∃ d, P d ∧ d ≠ c := by
  obtain ⟨-, -, hstr⟩ := h
  by_contra hno
  exact hstr fun s hs => not_not.mp fun hne => hno ⟨s, hs, hne⟩

/-- A forced isolation is broken by an explicit symmetry of the reading: the choice is not carried
by the reading itself. -/
theorem exists_symmetry_moving [DecidableEq S] {P : S → Prop} {c : S} (h : ForcedIsolation P c) :
    ∃ e : Equiv.Perm S, Symmetry P e ∧ e c ≠ c := by
  classical
  obtain ⟨d, hd, hne⟩ := exists_other_admissible h
  refine ⟨Equiv.swap c d, fun s => ?_, ?_⟩
  · by_cases hsc : s = c
    · subst hsc; simpa using iff_of_true hd h.1
    · by_cases hsd : s = d
      · subst hsd; rw [Equiv.swap_apply_right]; exact iff_of_true h.1 hd
      · rw [Equiv.swap_apply_of_ne_of_ne hsc hsd]
  · rw [Equiv.swap_apply_left]; exact hne

/-- **The exact opposition.**  On an admissible symbol, being a natural selection and being a forced
isolation are negations of one another. -/
theorem naturalSelection_iff_not_forcedIsolation [DecidableEq S] {P : S → Prop} {c : S}
    (hc : P c) : NaturalSelection P c ↔ ¬ ForcedIsolation P c := by
  constructor
  · intro hnat hforced
    exact not_complete_of_forcedIsolation hforced (complete_of_naturalSelection hnat)
  · intro hforced
    by_cases hcomp : Complete P
    · have := naturalSelection_theSelection hcomp
      rwa [theSelection_eq hcomp hc] at this
    · exact absurd (forcedIsolation_of_not_complete hc hcomp) hforced

/-- **Completions are isolations.**  A strengthening of a reading is complete exactly when it is the
isolation of one admissible symbol. -/
theorem complete_sub_iff_isolate {P Q : S → Prop} :
    (Complete Q ∧ Stronger Q P) ↔ ∃ c, P c ∧ ∀ s, Q s ↔ Isolate c s := by
  constructor
  · rintro ⟨⟨c, hc, huniq⟩, hsub⟩
    exact ⟨c, hsub _ hc, fun s => ⟨fun hs => huniq _ hs, fun hs => by rw [show s = c from hs]; exact hc⟩⟩
  · rintro ⟨c, hc, hQ⟩
    refine ⟨⟨c, (hQ c).mpr rfl, fun d hd => (hQ d).mp hd⟩, fun s hs => ?_⟩
    rw [show s = c from (hQ s).mp hs]; exact hc

/-! ## §4 The dichotomy and the naturality of selection -/

/-- No symbol is at once naturally selected and forcibly isolated. -/
theorem not_natural_and_forced [DecidableEq S] {P : S → Prop} {c : S} :
    ¬ (NaturalSelection P c ∧ ForcedIsolation P c) := by
  rintro ⟨hnat, hforced⟩
  exact not_complete_of_forcedIsolation hforced (complete_of_naturalSelection hnat)

/-- **The dichotomy.**  A reading is either complete — and then it has a unique natural selection —
or incomplete, and then every admissible symbol it has is a forced isolation. -/
theorem complete_dichotomy [DecidableEq S] (P : S → Prop) :
    (Complete P ∧ ∃! c, NaturalSelection P c) ∨
      (¬ Complete P ∧ ∀ c, P c → ForcedIsolation P c) := by
  by_cases h : Complete P
  · refine Or.inl ⟨h, ⟨theSelection h, naturalSelection_theSelection h, fun d hd => ?_⟩⟩
    exact naturalSelection_unique hd (naturalSelection_theSelection h)
  · exact Or.inr ⟨h, fun c hc => forcedIsolation_of_not_complete hc h⟩

/-- Selection is equivariant under a translation of the symbol field: a reading transported along
an injection with the same admissible symbols has the transported selection. -/
theorem complete_map {f : S → T} {P : S → Prop} {Q : T → Prop}
    (hf : Function.Injective f) (hQ : ∀ s, Q (f s) ↔ P s) (hsurj : ∀ t, Q t → ∃ s, t = f s) :
    Complete P ↔ Complete Q := by
  constructor
  · rintro ⟨c, hc, huniq⟩
    refine ⟨f c, (hQ c).mpr hc, fun t ht => ?_⟩
    obtain ⟨s, rfl⟩ := hsurj t ht
    exact congrArg f (huniq s ((hQ s).mp ht))
  · rintro ⟨t, ht, huniq⟩
    obtain ⟨c, rfl⟩ := hsurj t ht
    exact ⟨c, (hQ c).mp ht, fun d hd => hf (huniq (f d) ((hQ d).mpr hd))⟩

theorem theSelection_map {f : S → T} {P : S → Prop} {Q : T → Prop}
    (hf : Function.Injective f) (hQ : ∀ s, Q (f s) ↔ P s) (hsurj : ∀ t, Q t → ∃ s, t = f s)
    (hP : Complete P) :
    theSelection ((complete_map hf hQ hsurj).mp hP) = f (theSelection hP) :=
  theSelection_eq _ ((hQ _).mpr (theSelection_spec hP))

/-! ## §5 No selector where there is no completeness -/

/-- **There is no natural selector on incomplete readings.**  On a field with two symbols, no
choice defined on all non-empty readings can be equivariant: away from completeness, selection is
always an isolation imposed from outside. -/
theorem no_natural_selector (S : Type*) [DecidableEq S] [Nontrivial S] :
    ¬ ∃ F : (S → Prop) → S, (∀ P : S → Prop, (∃ s, P s) → P (F P)) ∧
      ∀ (e : Equiv.Perm S) (P : S → Prop), F (fun s => P (e.symm s)) = e (F P) := by
  classical
  rintro ⟨F, hmem, hnat⟩
  obtain ⟨a, b, hab⟩ := exists_pair_ne S
  set P : S → Prop := fun s => s = a ∨ s = b with hP
  have hPa : P a := Or.inl rfl
  have hstable : (fun s => P ((Equiv.swap a b).symm s)) = P := by
    funext s
    refine propext ⟨fun hs => ?_, fun hs => ?_⟩
    · rcases hs with hs | hs
      · right
        have := congrArg (Equiv.swap a b) hs
        rwa [Equiv.apply_symm_apply, Equiv.swap_apply_left] at this
      · left
        have := congrArg (Equiv.swap a b) hs
        rwa [Equiv.apply_symm_apply, Equiv.swap_apply_right] at this
    · rcases hs with hs | hs
      · right
        rw [Equiv.symm_swap, hs, Equiv.swap_apply_left]
      · left
        rw [Equiv.symm_swap, hs, Equiv.swap_apply_right]
  have hfix : F P = (Equiv.swap a b) (F P) := by
    have := hnat (Equiv.swap a b) P
    rwa [hstable] at this
  rcases hmem P ⟨a, hPa⟩ with h | h
  · rw [h, Equiv.swap_apply_left] at hfix; exact hab hfix
  · rw [h, Equiv.swap_apply_right] at hfix; exact hab hfix.symm

/-! ## §6 The stagewise form: NRRF775 constraints -/

open NRRF775 (Constraint Rigid sel sel_admissible sel_eq_of_admissible)

/-- Rigidity of a constraint is stagewise completeness of its readings. -/
theorem rigid_iff_forall_complete {R : Constraint S} : Rigid R ↔ ∀ n, Complete (R n) := Iff.rfl

/-- The NRRF775 natural form is, stage by stage, the natural selection of the stage's reading. -/
theorem sel_naturalSelection {R : Constraint S} (hR : Rigid R) (n : ℕ) :
    NaturalSelection (R n) (sel R hR n) := by
  refine ⟨sel_admissible R hR n, fun e he => ?_⟩
  have : R n (e (sel R hR n)) := (he _).mpr (sel_admissible R hR n)
  rw [sel_eq_of_admissible hR this, sel_eq_of_admissible hR (sel_admissible R hR n)]

/-- At a stage where a constraint is not rigid, every admissible symbol is a forced isolation:
the form there is not selected, it is imposed. -/
theorem forcedIsolation_of_not_rigid {R : Constraint S} {n : ℕ} (h : ¬ Complete (R n)) {a : S}
    (ha : R n a) : ForcedIsolation (R n) a := forcedIsolation_of_not_complete ha h

/-- A non-rigid constraint has a stage carrying no natural selection at all. -/
theorem exists_stage_without_selection [DecidableEq S] {R : Constraint S} (h : ¬ Rigid R) :
    ∃ n, ¬ ∃ c, NaturalSelection (R n) c := by
  rw [rigid_iff_forall_complete] at h
  push_neg at h
  obtain ⟨n, hn⟩ := h
  exact ⟨n, fun hc => hn (complete_iff_exists_naturalSelection.mpr hc)⟩

/-! ## §7 Concrete readings -/

/-- The reading of `Bool` admitting only `false` is complete. -/
theorem complete_falseOnly : Complete (fun b : Bool => b = false) := ⟨false, rfl, fun _ h => h⟩

/-- Its natural selection is `false`. -/
theorem naturalSelection_falseOnly : NaturalSelection (fun b : Bool => b = false) false := by
  have := naturalSelection_theSelection complete_falseOnly
  rwa [theSelection_eq complete_falseOnly (show (false : Bool) = false from rfl)] at this

/-- The total reading of `Bool` is incomplete. -/
theorem not_complete_total : ¬ Complete (fun _ : Bool => True) := by
  rintro ⟨c, -, huniq⟩
  have h1 := huniq true trivial
  have h2 := huniq false trivial
  have : (true : Bool) = false := h1.trans h2.symm
  simp at this

/-- Both of its symbols are forced isolations: neither is selected, each is imposed. -/
theorem forcedIsolation_total (b : Bool) : ForcedIsolation (fun _ : Bool => True) b :=
  forcedIsolation_of_not_complete trivial not_complete_total

/-- And it carries no natural selection. -/
theorem no_naturalSelection_total : ¬ ∃ b, NaturalSelection (fun _ : Bool => True) b := by
  intro h
  exact not_complete_total (complete_iff_exists_naturalSelection.mpr h)

/-! ## The answer -/

/-- **The clauses of NRRF790.**  For every reading of a symbol field:

* completeness is exactly the existence of a natural selection, and the selection is then unique
  and fixed by every symmetry of the reading;
* incompleteness is exactly forced isolation — for a non-empty incomplete reading every admissible
  symbol is a forced isolation, and on an admissible symbol natural selection and forced isolation
  are exact negations;
* the completions of a reading are precisely its isolations. -/
theorem nrrf790_answer [DecidableEq S] (P : S → Prop) :
    (Complete P ↔ ∃ c, NaturalSelection P c) ∧
    (∀ h : Complete P, NaturalSelection P (theSelection h) ∧
      ∀ e : Equiv.Perm S, Symmetry P e → e (theSelection h) = theSelection h) ∧
    (∀ c d, NaturalSelection P c → NaturalSelection P d → c = d) ∧
    (¬ Complete P → ∀ c, P c → ForcedIsolation P c) ∧
    (∀ c, P c → (NaturalSelection P c ↔ ¬ ForcedIsolation P c)) ∧
    (∀ Q : S → Prop, (Complete Q ∧ Stronger Q P) ↔ ∃ c, P c ∧ ∀ s, Q s ↔ Isolate c s) :=
  ⟨complete_iff_exists_naturalSelection,
   fun h => ⟨naturalSelection_theSelection h, fun e he => theSelection_symm_fixed h e he⟩,
   fun _ _ hc hd => naturalSelection_unique hc hd,
   fun hnc _ hc => forcedIsolation_of_not_complete hc hnc,
   fun _ hc => naturalSelection_iff_not_forcedIsolation hc,
   fun _ => complete_sub_iff_isolate⟩

end NRRF790

/-! ## Audit

Every headline result of this module, checked against the ambient axioms only. -/

section Audit

/-- info: 'NRRF790.complete_iff_exists_naturalSelection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF790.complete_iff_exists_naturalSelection

/-- info: 'NRRF790.naturalSelection_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF790.naturalSelection_unique

/-- info: 'NRRF790.forcedIsolation_of_not_complete' does not depend on any axioms -/
#guard_msgs in #print axioms NRRF790.forcedIsolation_of_not_complete

/-- info: 'NRRF790.naturalSelection_iff_not_forcedIsolation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF790.naturalSelection_iff_not_forcedIsolation

/-- info: 'NRRF790.complete_sub_iff_isolate' does not depend on any axioms -/
#guard_msgs in #print axioms NRRF790.complete_sub_iff_isolate

/-- info: 'NRRF790.complete_dichotomy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF790.complete_dichotomy

/-- info: 'NRRF790.no_natural_selector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF790.no_natural_selector

/-- info: 'NRRF790.nrrf790_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF790.nrrf790_answer

end Audit
