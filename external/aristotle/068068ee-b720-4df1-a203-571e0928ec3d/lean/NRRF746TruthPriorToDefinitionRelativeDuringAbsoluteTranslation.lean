import Mathlib
import NRRF740FullUnifiedClosureEquationsAdmissibleDerivationsForms

/-!
# NRRF746 — Truth prior to definition is contradictory; relative definition is *during*, and truth is its absolute translation

The questions formalized here are the user's:

> Can you define truth prior to definition?  If so, you have a contradiction.  However, there
> exists undefined truth.  Is there a partial relative definition of truth?  Perhaps relative
> definition is not prior or past absolute definition, but during.  Then truth would be the
> absolute translation of relative definition, assuming defined truth is a continuous unification
> of shared understanding, meaning, and perspective.

## The reading

* **claim.**  An element of a type `C`.  Nothing is assumed about `C`.
* **a definition of truth** is a *verdict map* `d : C → Option Bool`: on some claims it says
  `some true` / `some false`, on the rest it says nothing (`none`).  A definition is **total** when
  it never says nothing, **partial** otherwise, and **sound** for a truth `T` when its verdicts
  agree with `T` where it gives them.
* **prior to definition** means: the truth predicate is already settled over the *whole* language,
  and that same language names every condition on claims — including the conditions that mention
  truth.  No staging, no "during": the definition is complete before, and independently of, the
  definitional process.
* **relative definition** is a stage `d n` of a monotone family of partial definitions, each one
  sound but none complete.  A stage is a perspective *inside* the process.
* **absolute translation** is the colimit `colim` of the family: the verdict a claim eventually
  receives.  "Continuous unification of shared understanding, meaning, and perspective" is read as
  the three hypotheses that make the colimit exist and be well-defined: *coherence* (shared
  understanding: no two stages contradict), *soundness* (meaning: a verdict is about the claim),
  and *cofinality in the stages* (perspective: every claim is reached at some stage).  Continuity
  is `eventually_stable`: the absolute verdict of any claim is already the verdict of some finite
  stage, so nothing is decided only "at infinity".

## The answers

1. **No.**  `prior_definition_contradiction`: a truth predicate defined prior to definition — total
   over a language that names all of its own conditions — is contradictory (the liar, in diagonal
   form).  `no_definitionally_complete_language` is the same obstruction without any truth
   predicate: no language applies to itself completely.
2. **Yet there is undefined truth.**  `exists_undefined_truth`, `no_stage_is_total`: in a stage
   system every stage leaves some *true* claim without a verdict.  Truth outruns each definition.
3. **Yes, there is a partial relative definition.**  `StageSystem` is exactly that, and
   `evenSystem` is a concrete non-vacuous one, so §§2–5 are not empty.
4. **Relative definition is neither prior nor past absolute definition, but during.**
   `stage_extends_abs` + `stage_strictly_during` (every stage is strictly inside the absolute
   definition) and `no_definition_past_absolute` (nothing sound extends beyond it: the absolute
   definition is the terminal point of the process, so there is no "past").
5. **Truth is the absolute translation of relative definition.**  `abs_eq_truth`:
   `T c ↔ ∃ n, d n c = some true` — the absolute truth predicate *is* the colimit of the relative
   partial definitions, nothing more; `absDef_total`, `absDef_sound`, `absDef_true_iff`.
6. **The three assumptions are load-bearing.**  `no_shared_truth_of_incoherent` (without shared
   understanding there is no truth for two perspectives to be sound for) and
   `abs_unique_of_coherent` (with it, two stage systems over the same claims define the *same*
   truth: the translation is absolute, not perspectival).  `eventually_stable` is the continuity.
7. **In the closure equations of NRRF740.**  `transClosure`: relative definition ↦ absolute
   translation is a closure — the return equation `eval ∘ encode = id` holds (`0`), while the
   closing equation fails (`trans_not_closes`, the `inf` side): the absolute translation forgets
   *when* a claim was defined, and that forgotten "during" is exactly the failure of closing.

`nrrf746_answer` collects the headline statements.
-/

namespace NRRF746

universe u

/-! ## §1  Definitions of truth, total and partial -/

/-- A **definition of truth** on claims `C`: a verdict on some claims, silence on the rest. -/
def PDef (C : Type u) : Type u := C → Option Bool

/-- The definition `d` has a verdict on the claim `c`. -/
def Defined {C : Type u} (d : PDef C) (c : C) : Prop := (d c).isSome

/-- A **total** definition: a verdict on every claim. -/
def Total {C : Type u} (d : PDef C) : Prop := ∀ c, Defined d c

/-- A definition is **sound** for the truth `T` when its verdicts are true of the claim.  This is
the "meaning" side: a verdict is *about* the claim it is given on. -/
def Sound {C : Type u} (T : C → Prop) (d : PDef C) : Prop :=
  ∀ c b, d c = some b → (T c ↔ b = true)

/-- `Extends d e`: `e` extends `d` — it keeps every verdict `d` has already given, and may give
more.  Definition proceeds by extension only. -/
def Extends {C : Type u} (d e : PDef C) : Prop := ∀ c b, d c = some b → e c = some b

/-- Two definitions are **coherent** when they never contradict each other where both speak.  This
is the "shared understanding" side. -/
def Coherent {C : Type u} (d e : PDef C) : Prop :=
  ∀ c b b', d c = some b → e c = some b' → b = b'

variable {C : Type u}

theorem defined_iff_exists {d : PDef C} {c : C} : Defined d c ↔ ∃ b, d c = some b :=
  Option.isSome_iff_exists

theorem not_defined_iff {d : PDef C} {c : C} : ¬ Defined d c ↔ d c = none := by
  cases h : d c <;> simp [Defined, h]

theorem Extends.refl (d : PDef C) : Extends d d := fun _ _ h => h

theorem Extends.trans {d e f : PDef C} (h₁ : Extends d e) (h₂ : Extends e f) : Extends d f :=
  fun c b hb => h₂ c b (h₁ c b hb)

theorem Extends.defined {d e : PDef C} (h : Extends d e) {c : C} (hc : Defined d c) :
    Defined e c := by
  obtain ⟨b, hb⟩ := defined_iff_exists.mp hc
  exact defined_iff_exists.mpr ⟨b, h c b hb⟩

/-- **Soundness is shared understanding.**  Two definitions sound for the same truth are
automatically coherent: meaning already forces agreement. -/
theorem coherent_of_sound {T : C → Prop} {d e : PDef C} (hd : Sound T d) (he : Sound T e) :
    Coherent d e := by
  intro c b b' hb hb'
  have h1 := hd c b hb
  have h2 := he c b' hb'
  cases b <;> cases b' <;> simp_all

/-- **Without shared understanding there is no truth at all.**  If two definitions contradict each
other on one claim, no truth predicate is sound for both. -/
theorem no_shared_truth_of_incoherent {d e : PDef C} {c : C}
    (hd : d c = some true) (he : e c = some false)
    {T : C → Prop} (h1 : Sound T d) (h2 : Sound T e) : False := by
  have := h1 c true hd
  have := h2 c false he
  simp_all

/-- A sound total definition is *determined* by the truth it defines: there is at most one. -/
theorem sound_total_ext {T : C → Prop} {d e : PDef C}
    (hd : Sound T d) (hdt : Total d) (he : Sound T e) (het : Total e) : d = e := by
  funext c
  obtain ⟨b, hb⟩ := defined_iff_exists.mp (hdt c)
  obtain ⟨b', hb'⟩ := defined_iff_exists.mp (het c)
  rw [hb, hb']
  exact congrArg some (coherent_of_sound hd he c b b' hb hb')

/-! ## §2  Can truth be defined prior to definition?  No. -/

/-- **Truth defined prior to definition.**  The truth predicate `T` is already settled on every
claim, and the same language *names* every condition on claims — including the conditions that
mention `T` — with the naming satisfying the diagonal equation: the claim named by `p` is true
exactly when `p` holds of it.  This is what it is for the definition to be complete *before* and
*independently of* any definitional stage. -/
structure PriorDefinition (C : Type u) where
  /-- the truth predicate, settled in advance on all of `C` -/
  T : C → Prop
  /-- the language names every condition on claims -/
  name : (C → Prop) → C
  /-- the diagonal equation for the naming -/
  diag : ∀ p : C → Prop, T (name p) ↔ p (name p)

/-- **The first answer: no.**  There is no definition of truth prior to definition — the
assumption is outright contradictory (this is the liar, in diagonal form). -/
theorem prior_definition_contradiction (P : PriorDefinition C) : False := by
  have h := P.diag (fun c => ¬ P.T c)
  simp only at h
  tauto

/-- The same obstruction with no truth predicate mentioned: **no language applies to itself
completely.**  If every condition on claims were the condition expressed by some claim, the
diagonal condition would have no expression. -/
theorem no_definitionally_complete_language (app : C → C → Prop)
    (complete : ∀ p : C → Prop, ∃ c, ∀ x, app c x ↔ p x) : False := by
  obtain ⟨c, hc⟩ := complete (fun x => ¬ app x x)
  have := hc c
  tauto

/-- Priority is what fails, not definition as such: *partial* definitions always exist (the empty
one, and, on a decidable truth, any restriction of it). -/
theorem partial_definitions_exist (T : C → Prop) (U : Set C) [DecidablePred T]
    [DecidablePred (· ∈ U)] :
    ∃ d : PDef C, Sound T d ∧ (∀ c, Defined d c ↔ c ∈ U) := by
  refine ⟨fun c => if c ∈ U then some (decide (T c)) else none, ?_, ?_⟩
  · intro c b hb
    by_cases hc : c ∈ U <;> simp [hc] at hb
    subst hb; simp
  · intro c
    by_cases hc : c ∈ U <;> simp [Defined, hc]

/-! ## §3  The colimit: the absolute translation of a family of relative definitions -/

open Classical in
/-- The **absolute translation** of a family of relative definitions: the verdict a claim receives
at some stage, if it receives one at all. -/
noncomputable def colim (f : ℕ → PDef C) : PDef C := fun c =>
  if h : ∃ n, (f n c).isSome then f (Nat.find h) c else none

/-- A family that never moves translates to itself. -/
theorem colim_const (d : PDef C) : colim (fun _ => d) = d := by
  funext c
  unfold colim
  split
  · rfl
  · next h => exact (not_defined_iff.mp (fun hc => h ⟨0, hc⟩)).symm

/-- Monotone families extend along `≤`. -/
theorem extends_le {f : ℕ → PDef C} (hm : ∀ n, Extends (f n) (f (n + 1))) {m n : ℕ}
    (h : m ≤ n) : Extends (f m) (f n) := by
  induction n, h using Nat.le_induction with
  | base => exact Extends.refl _
  | succ n hn ih => exact ih.trans (hm n)

/-- **Continuity, pointwise.**  A verdict once given at a stage is the absolute verdict: the
translation of a monotone family adds nothing to what the stages already say. -/
theorem colim_eq_of_mono {f : ℕ → PDef C} (hm : ∀ n, Extends (f n) (f (n + 1)))
    {c : C} {b : Bool} {n : ℕ} (hn : f n c = some b) : colim f c = some b := by
  have hex : ∃ k, (f k c).isSome := ⟨n, by rw [hn]; rfl⟩
  unfold colim
  rw [dif_pos hex]
  obtain ⟨b', hb'⟩ := defined_iff_exists.mp (Nat.find_spec hex)
  rw [hb']
  rcases le_total (Nat.find hex) n with h | h
  · have := extends_le hm h c b' hb'
    rw [hn] at this
    exact this.symm
  · have := extends_le hm h c b hn
    rw [hb'] at this
    exact this

/-- If no stage speaks, the translation is silent too. -/
theorem colim_eq_none {f : ℕ → PDef C} {c : C} (h : ∀ n, f n c = none) : colim f c = none := by
  unfold colim
  rw [dif_neg]
  rintro ⟨n, hn⟩
  rw [h n] at hn
  exact absurd hn (by simp)

/-! ## §4  Relative definition: partial, sound, staged — *during* -/

/-- A **stage system**: a partial relative definition of truth, unfolding in stages.

* `sound` — meaning: every verdict is about its claim;
* `mono` — definition proceeds by extension: nothing already defined is withdrawn;
* `reached` — perspective: every claim is reached at some stage, so the process is not *past*
  anything;
* `proper` — no stage is complete: at every stage some *true* claim is still undefined, so the
  process is not *prior* to anything either. -/
structure StageSystem (C : Type u) where
  /-- the truth being defined -/
  T : C → Prop
  /-- the stages: partial relative definitions -/
  d : ℕ → PDef C
  /-- every verdict is sound -/
  sound : ∀ n, Sound T (d n)
  /-- the stages only extend -/
  mono : ∀ n, Extends (d n) (d (n + 1))
  /-- every claim is reached at some stage -/
  reached : ∀ c, ∃ n, Defined (d n) c
  /-- no stage is complete: undefined truth at every stage -/
  proper : ∀ n, ∃ c, T c ∧ d n c = none

namespace StageSystem

variable (S : StageSystem C)

theorem extends_le' {m n : ℕ} (h : m ≤ n) : Extends (S.d m) (S.d n) := extends_le S.mono h

/-- **Shared understanding between stages** is automatic from soundness. -/
theorem stages_coherent (m n : ℕ) : Coherent (S.d m) (S.d n) :=
  coherent_of_sound (S.sound m) (S.sound n)

/-- **There exists undefined truth.**  At every stage there is a true claim with no verdict. -/
theorem exists_undefined_truth (n : ℕ) : ∃ c, S.T c ∧ ¬ Defined (S.d n) c := by
  obtain ⟨c, hc, hn⟩ := S.proper n
  exact ⟨c, hc, by simp [not_defined_iff, hn]⟩

/-- No relative definition is total: definition never catches up with truth at any stage. -/
theorem no_stage_is_total (n : ℕ) : ¬ Total (S.d n) := by
  intro h
  obtain ⟨c, _, hc⟩ := S.exists_undefined_truth n
  exact hc (h c)

/-- **Truth is the absolute translation of the relative definitions.**  A claim is true exactly
when some stage gives it the verdict `true`; truth is the colimit of the relative definitions and
nothing besides. -/
theorem abs_eq_truth (c : C) : S.T c ↔ ∃ n, S.d n c = some true := by
  constructor
  · intro hc
    obtain ⟨n, hn⟩ := S.reached c
    obtain ⟨b, hb⟩ := defined_iff_exists.mp hn
    have := (S.sound n c b hb).mp hc
    exact ⟨n, by rw [hb, this]⟩
  · rintro ⟨n, hn⟩
    exact (S.sound n c true hn).mpr rfl

/-- The **absolute definition**: the total definition obtained by translating the whole process. -/
noncomputable def absDef : PDef C := colim S.d

theorem absDef_eq_of_stage {c : C} {b : Bool} {n : ℕ} (h : S.d n c = some b) :
    S.absDef c = some b := colim_eq_of_mono S.mono h

/-- The absolute definition is total: nothing is left undefined by the *whole* process. -/
theorem absDef_total : Total S.absDef := by
  intro c
  obtain ⟨n, hn⟩ := S.reached c
  obtain ⟨b, hb⟩ := defined_iff_exists.mp hn
  exact defined_iff_exists.mpr ⟨b, S.absDef_eq_of_stage hb⟩

/-- The absolute definition is sound. -/
theorem absDef_sound : Sound S.T S.absDef := by
  intro c b hb
  obtain ⟨n, hn⟩ := S.reached c
  obtain ⟨b', hb'⟩ := defined_iff_exists.mp hn
  have : S.absDef c = some b' := S.absDef_eq_of_stage hb'
  rw [hb] at this
  have hbb : b' = b := (Option.some.injEq _ _ ▸ this).symm
  subst hbb
  exact S.sound n c b' hb'

/-- The absolute definition says `true` exactly of the truths. -/
theorem absDef_true_iff (c : C) : S.absDef c = some true ↔ S.T c := by
  constructor
  · intro h; exact (S.absDef_sound c true h).mpr rfl
  · intro h
    obtain ⟨n, hn⟩ := (S.abs_eq_truth c).mp h
    exact S.absDef_eq_of_stage hn

/-- **Relative definition is not past absolute definition**: every stage lies inside it. -/
theorem stage_extends_abs (n : ℕ) : Extends (S.d n) S.absDef :=
  fun _ _ h => S.absDef_eq_of_stage h

/-- **Relative definition is not prior to absolute definition either**: every stage is *strictly*
inside it, so no stage is the absolute definition.  Relative definition happens **during**. -/
theorem stage_strictly_during (n : ℕ) :
    Extends (S.d n) S.absDef ∧ ∃ c, Defined S.absDef c ∧ ¬ Defined (S.d n) c := by
  obtain ⟨c, _, hc⟩ := S.exists_undefined_truth n
  exact ⟨S.stage_extends_abs n, ⟨c, S.absDef_total c, hc⟩⟩

theorem stage_ne_absDef (n : ℕ) : S.d n ≠ S.absDef := by
  intro h
  exact S.no_stage_is_total n (h ▸ S.absDef_total)

/-- **Nothing is past the absolute definition.**  Any sound total definition of the same truth *is*
the absolute translation: the process has a terminal point and it is the colimit. -/
theorem no_definition_past_absolute {e : PDef C} (he : Sound S.T e) (het : Total e) :
    e = S.absDef :=
  sound_total_ext he het S.absDef_sound S.absDef_total

/-- **Continuity.**  Every claim's absolute verdict is already the verdict of some finite stage,
and of all later ones: nothing is decided only in the limit. -/
theorem eventually_stable (c : C) : ∃ n, ∀ m, n ≤ m → S.d m c = S.absDef c := by
  obtain ⟨n, hn⟩ := S.reached c
  obtain ⟨b, hb⟩ := defined_iff_exists.mp hn
  refine ⟨n, fun m hm => ?_⟩
  rw [S.extends_le' hm c b hb, S.absDef_eq_of_stage hb]

end StageSystem

/-- **The translation is absolute, not perspectival.**  Two stage systems over the same claims
whose stages never contradict each other define *the same truth*: shared understanding across
perspectives forces one truth, which is therefore the absolute translation of either process. -/
theorem abs_unique_of_coherent (S S' : StageSystem C)
    (h : ∀ n m, Coherent (S.d n) (S'.d m)) : S.T = S'.T := by
  funext c
  obtain ⟨n, hn⟩ := S.reached c
  obtain ⟨m, hm⟩ := S'.reached c
  obtain ⟨b, hb⟩ := defined_iff_exists.mp hn
  obtain ⟨b', hb'⟩ := defined_iff_exists.mp hm
  have hbb : b = b' := h n m c b b' hb hb'
  subst hbb
  exact propext ((S.sound n c b hb).trans (S'.sound m c b hb').symm)

/-- The same conclusion for the total definitions: coherent perspectives translate to one and the
same absolute definition. -/
theorem absDef_unique_of_coherent (S S' : StageSystem C)
    (h : ∀ n m, Coherent (S.d n) (S'.d m)) : S.absDef = S'.absDef := by
  have hT : S.T = S'.T := abs_unique_of_coherent S S' h
  refine sound_total_ext S.absDef_sound S.absDef_total ?_ S'.absDef_total
  rw [hT]; exact S'.absDef_sound

/-! ## §5  A concrete stage system: nothing above is vacuous -/

/-- Stage `n` decides parity for the claims below `n`, and says nothing about the rest. -/
def evenStage (n : ℕ) : PDef ℕ := fun c => if c < n then some (decide (Even c)) else none

/-- A concrete partial relative definition of truth whose absolute translation is "is even". -/
def evenSystem : StageSystem ℕ where
  T := fun c => Even c
  d := evenStage
  sound := by
    intro n c b hb
    by_cases hc : c < n
    · simp only [evenStage, if_pos hc, Option.some.injEq] at hb
      subst hb; simp
    · simp [evenStage, hc] at hb
  mono := by
    intro n c b hb
    by_cases hc : c < n
    · have : c < n + 1 := by omega
      simpa [evenStage, this] using by simpa [evenStage, hc] using hb
    · simp [evenStage, hc] at hb
  reached := by
    intro c
    exact ⟨c + 1, by simp [Defined, evenStage]⟩
  proper := by
    intro n
    refine ⟨2 * n + 2 * n + 2, ⟨n + n + 1, by ring⟩, ?_⟩
    have : ¬ (2 * n + 2 * n + 2 < n) := by omega
    simp [evenStage, this]

theorem evenSystem_absDef (c : ℕ) : evenSystem.absDef c = some (decide (Even c)) :=
  evenSystem.absDef_eq_of_stage (n := c + 1)
    (show evenStage (c + 1) c = some (decide (Even c)) by simp [evenStage])

/-! ## §6  The translation as a closure of NRRF740 -/

open NRRF739 NRRF740

/-- **Relative definition ↦ absolute translation is a closure.**  Encoding a definition as the
process that already holds it, and evaluating a process by its absolute translation, satisfies the
return equation `eval ∘ encode = id` — the `0` side. -/
noncomputable def transClosure (C : Type u) : Closure (PDef C) (ℕ → PDef C) where
  encode := fun d _ => d
  eval := colim
  eval_encode := colim_const

/-- **The closing equation fails.**  The absolute translation forgets *when* a claim was defined:
distinct processes with the same translation exist, so `encode ∘ eval ≠ id`.  That forgotten
"during" is precisely the failure of closing — the `inf` side. -/
theorem trans_not_closes [Nonempty C] : ¬ Closes (transClosure C) := by
  intro h
  obtain ⟨c⟩ := ‹Nonempty C›
  set f : ℕ → PDef C := fun n _ => if n = 0 then none else some true with hf
  have hfun : (fun _ : ℕ => colim f) = f := congrFun h f
  have e0 : colim f c = f 0 c := congrFun (congrFun hfun 0) c
  have e1 : colim f c = f 1 c := congrFun (congrFun hfun 1) c
  rw [e0] at e1
  simp [hf] at e1

/-! ## §7  The answer -/

/-- **The answers to the user's questions, in one statement.**

1. Truth cannot be defined prior to definition: the assumption is contradictory.
2. There is undefined truth: every relative stage leaves a true claim without a verdict.
3. There *is* a partial relative definition, and it is neither prior to nor past the absolute
   definition: every stage extends into it strictly, and nothing sound goes beyond it.
4. Truth is the absolute translation of relative definition: it is the colimit of the stages.
5. That translation is continuous, and absolute rather than perspectival. -/
theorem nrrf746_answer (S : StageSystem C) :
    -- 1  no definition of truth prior to definition
    (PriorDefinition C → False) ∧
    -- 2  undefined truth at every stage
    (∀ n, ∃ c, S.T c ∧ ¬ Defined (S.d n) c) ∧
    -- 3  during: strictly inside the absolute definition, and nothing past it
    (∀ n, Extends (S.d n) S.absDef ∧ S.d n ≠ S.absDef) ∧
    (∀ e : PDef C, Sound S.T e → Total e → e = S.absDef) ∧
    -- 4  truth is the absolute translation of the relative definitions
    (∀ c, S.T c ↔ ∃ n, S.d n c = some true) ∧
    -- 5  continuity, and absoluteness across coherent perspectives
    (∀ c, ∃ n, ∀ m, n ≤ m → S.d m c = S.absDef c) ∧
    (∀ S' : StageSystem C, (∀ n m, Coherent (S.d n) (S'.d m)) → S.T = S'.T) :=
  ⟨prior_definition_contradiction,
   S.exists_undefined_truth,
   fun n => ⟨S.stage_extends_abs n, S.stage_ne_absDef n⟩,
   fun _ he het => S.no_definition_past_absolute he het,
   S.abs_eq_truth,
   S.eventually_stable,
   fun S' h => abs_unique_of_coherent S S' h⟩

end NRRF746
