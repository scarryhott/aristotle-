import Mathlib
import NRRF775NaturalFormSelectorUnifaceRelationalDeterminationUnitaryPathPartitionTraces

/-!
# NRRF789 — Continuation and halting of a computer: encoding is the universe of halting,
evaluation is the canon of continuation

The reading being formalised:

> Of a computer, encode the substrate and evaluate the operation in an equally natural manner,
> where encoding is the universe of halting and evaluation is the canon of continuation.

A **computer** here is nothing more than the partial step of NRRF775: an operation
`step : σ → Option σ` on a substrate `σ`, where `none` is the report "stopped".  Two readings are
taken of the very same datum, and the whole content of the module is that they are *equally
natural*: neither is prior, each is the unique thing satisfying its own law, and both are carried
along by any simulation of the computer.

* **§1 Encoding is the universe of halting.**  The encoding `enc` of the substrate assigns to a
  datum the stage at which its run stops.  Its domain of definition is *exactly* the halting set
  (`enc_universe`), it is characterised stage-by-stage (`enc_eq_some_iff`), and it is the **unique**
  reading satisfying that characterisation (`enc_unique`).  So the encoding is not a choice of code:
  it is the universe of halting, read off.
* **§2 Evaluation is the canon of continuation.**  Evaluation `eval` is the run itself.  It is the
  unique function obeying the two evaluation laws (`eval_unique`); on a continuing datum it is a
  total trajectory (`traj`) with `step (traj n) = some (traj (n+1))` (`step_traj`), and *any*
  trajectory through the datum is that one (`traj_unique`), while conversely a trajectory forces
  continuation (`continues_of_trajectory`).  So continuation has a canon, and evaluation is it.
* **§3 The two readings partition the substrate.**  Halting and continuation are complementary
  (`continues_iff_enc_eq_none`, `substrate_partition`); the encoded universe is the complement of
  the canonical one.
* **§4 Equally natural.**  Under a simulation `f` (`step' (f x) = (step x).map f`) evaluation is
  equivariant (`run_map`, `eval_map`) and the encoding is *invariant* (`enc_sim`): the halting
  universe does not move, the continuation canon moves along.  Naturality is the same statement for
  both readings, which is the sense in which they are equally natural.
* **§5 Mutual determination, and no collapse.**  Evaluation determines the encoding
  (`enc_eq_of_none_pattern`), but the encoding does not determine evaluation
  (`enc_does_not_determine_eval`): equally natural, not equal.
* **§6 A concrete computer.**  The countdown machine halts from every datum with encoding `x + 1`
  (`enc_countdown`); the climbing machine continues from every datum with empty encoding and
  canonical trajectory `x + n` (`enc_climb`, `traj_climb`); the fibring `n ↦ (n, b)` is a simulation
  and hence leaves the encoding fixed (`enc_countdownPair`).

`nrrf789_answer` collects the clauses.
-/

namespace NRRF789

open NRRF775 (run run_zero run_succ Halts Continues run_none_succ run_none_of_le
  not_halts_and_continues halts_or_continues)

variable {σ τ : Type*}

/-! ## §0 The operation and its stages -/

/-- Running `m + n` stages is running `m` stages and then `n` more: the operation composes. -/
theorem run_add (step : σ → Option σ) (x : σ) (m n : ℕ) :
    run step x (m + n) = (run step x m).bind (fun y => run step y n) := by
  induction n with
  | zero => cases h : run step x m <;> simp [h]
  | succ k ih =>
      have hmk : m + (k + 1) = (m + k) + 1 := by ring
      rw [hmk, run_succ, ih]
      cases h : run step x m with
      | none => simp
      | some y => simp [run_succ]

theorem continues_iff_not_halts {step : σ → Option σ} {x : σ} :
    Continues step x ↔ ¬ Halts step x := by
  constructor
  · intro hc hh; exact not_halts_and_continues ⟨hh, hc⟩
  · intro hh
    rcases halts_or_continues step x with h | h
    · exact absurd h hh
    · exact h

theorem run_ne_none_of_continues {step : σ → Option σ} {x : σ} (h : Continues step x) (n : ℕ) :
    run step x n ≠ none := by
  intro hn
  have := h n
  rw [hn] at this
  exact absurd this (by simp)

/-! ## §1 Encoding: the universe of halting -/

open Classical in
/-- **The encoding of the substrate.**  A datum is encoded by the stage at which its run stops —
and by nothing at all when it never stops. -/
noncomputable def enc (step : σ → Option σ) (x : σ) : Option ℕ :=
  if h : Halts step x then some (Nat.find h) else none

/-- The encoding is defined exactly at a stopping stage, minimally. -/
theorem enc_eq_some_iff {step : σ → Option σ} {x : σ} {n : ℕ} :
    enc step x = some n ↔ run step x n = none ∧ ∀ m < n, run step x m ≠ none := by
  classical
  constructor
  · intro h
    rw [enc] at h
    split at h
    · rename_i hh
      have hn : Nat.find hh = n := by simpa using h
      subst hn
      exact ⟨Nat.find_spec hh, fun m hm => Nat.find_min hh hm⟩
    · exact absurd h (by simp)
  · rintro ⟨hn, hmin⟩
    have hh : Halts step x := ⟨n, hn⟩
    have hfind : Nat.find hh = n := by
      refine le_antisymm (Nat.find_le hn) ?_
      by_contra hlt
      exact hmin _ (by omega) (Nat.find_spec hh)
    rw [enc, dif_pos hh, hfind]

theorem enc_eq_none_iff {step : σ → Option σ} {x : σ} :
    enc step x = none ↔ Continues step x := by
  classical
  rw [continues_iff_not_halts, enc]
  by_cases hh : Halts step x <;> simp [hh]

theorem enc_isSome_iff {step : σ → Option σ} {x : σ} :
    (enc step x).isSome ↔ Halts step x := by
  classical
  rw [enc]
  by_cases hh : Halts step x <;> simp [hh]

/-- **Encoding is the universe of halting**: the domain of the encoding is the halting set, on the
nose. -/
theorem enc_universe (step : σ → Option σ) :
    {x : σ | (enc step x).isSome} = {x : σ | Halts step x} := by
  ext x; exact enc_isSome_iff

/-- The specification the encoding satisfies: report a minimal stopping stage, and report nothing
exactly on continuing data. -/
def EncSpec (step : σ → Option σ) (e : σ → Option ℕ) : Prop :=
  ∀ x : σ, (∀ n, e x = some n → run step x n = none ∧ ∀ m < n, run step x m ≠ none) ∧
    (e x = none → Continues step x)

theorem enc_spec (step : σ → Option σ) : EncSpec step (enc step) := by
  intro x
  exact ⟨fun _ h => enc_eq_some_iff.mp h, fun h => enc_eq_none_iff.mp h⟩

/-- **The encoding is the unique such reading.**  Nothing is chosen in the encoding: it is forced by
the halting universe. -/
theorem enc_unique {step : σ → Option σ} {e : σ → Option ℕ} (he : EncSpec step e) :
    e = enc step := by
  funext x
  rcases hx : e x with _ | n
  · exact ((enc_eq_none_iff.mpr ((he x).2 hx))).symm ▸ rfl
  · exact (enc_eq_some_iff.mpr ((he x).1 n hx)).symm

theorem enc_exists_unique (step : σ → Option σ) : ∃! e : σ → Option ℕ, EncSpec step e :=
  ⟨enc step, enc_spec step, fun _ h => enc_unique h⟩

/-! ## §2 Evaluation: the canon of continuation -/

/-- **The evaluation of the operation**: the stage-by-stage run of the computer. -/
def eval (step : σ → Option σ) (x : σ) : ℕ → Option σ := run step x

@[simp] theorem eval_zero (step : σ → Option σ) (x : σ) : eval step x 0 = some x := rfl

@[simp] theorem eval_succ (step : σ → Option σ) (x : σ) (n : ℕ) :
    eval step x (n + 1) = (eval step x n).bind step := rfl

/-- The two evaluation laws. -/
def EvalSpec (step : σ → Option σ) (E : σ → ℕ → Option σ) : Prop :=
  (∀ x, E x 0 = some x) ∧ ∀ x n, E x (n + 1) = (E x n).bind step

theorem eval_evalSpec (step : σ → Option σ) : EvalSpec step (eval step) :=
  ⟨eval_zero step, eval_succ step⟩

/-- **Evaluation is the canon**: it is the unique reading obeying the evaluation laws. -/
theorem eval_unique {step : σ → Option σ} {E : σ → ℕ → Option σ} (hE : EvalSpec step E) :
    E = eval step := by
  funext x n
  induction n with
  | zero => rw [hE.1 x, eval_zero]
  | succ k ih => rw [hE.2 x k, ih, eval_succ]

theorem eval_exists_unique (step : σ → Option σ) : ∃! E : σ → ℕ → Option σ, EvalSpec step E :=
  ⟨eval step, eval_evalSpec step, fun _ h => eval_unique h⟩

/-- **The canonical trajectory of a continuing datum.** -/
def traj (step : σ → Option σ) {x : σ} (h : Continues step x) (n : ℕ) : σ :=
  (run step x n).get (h n)

theorem run_eq_traj {step : σ → Option σ} {x : σ} (h : Continues step x) (n : ℕ) :
    run step x n = some (traj step h n) := (Option.some_get (h n)).symm

@[simp] theorem traj_zero {step : σ → Option σ} {x : σ} (h : Continues step x) :
    traj step h 0 = x := by
  have := run_eq_traj h 0
  rw [run_zero] at this
  exact (Option.some.inj this).symm

/-- The trajectory is a genuine orbit of the operation: the computer never stops on it. -/
theorem step_traj {step : σ → Option σ} {x : σ} (h : Continues step x) (n : ℕ) :
    step (traj step h n) = some (traj step h (n + 1)) := by
  have h1 : run step x (n + 1) = (some (traj step h n)).bind step := by
    rw [run_succ, run_eq_traj h n]
  rw [run_eq_traj h (n + 1)] at h1
  simpa using h1.symm

/-- A trajectory through a datum forces continuation, and computes the run. -/
theorem run_eq_of_trajectory {step : σ → Option σ} {x : σ} {t : ℕ → σ} (h0 : t 0 = x)
    (hs : ∀ n, step (t n) = some (t (n + 1))) (n : ℕ) : run step x n = some (t n) := by
  induction n with
  | zero => rw [run_zero, h0]
  | succ k ih => rw [run_succ, ih]; simpa using hs k

theorem continues_of_trajectory {step : σ → Option σ} {x : σ} {t : ℕ → σ} (h0 : t 0 = x)
    (hs : ∀ n, step (t n) = some (t (n + 1))) : Continues step x := by
  intro n
  rw [run_eq_of_trajectory h0 hs n]
  simp

/-- **The canon of continuation is unique**: a continuing datum has exactly one trajectory. -/
theorem traj_unique {step : σ → Option σ} {x : σ} (h : Continues step x) {t : ℕ → σ}
    (h0 : t 0 = x) (hs : ∀ n, step (t n) = some (t (n + 1))) : t = traj step h := by
  funext n
  have := run_eq_of_trajectory h0 hs n
  rw [run_eq_traj h n] at this
  exact (Option.some.inj this).symm

theorem trajectory_exists_unique {step : σ → Option σ} {x : σ} (h : Continues step x) :
    ∃! t : ℕ → σ, t 0 = x ∧ ∀ n, step (t n) = some (t (n + 1)) :=
  ⟨traj step h, ⟨traj_zero h, step_traj h⟩, fun _ ht => traj_unique h ht.1 ht.2⟩

/-! ## §3 The two readings partition the substrate -/

theorem continues_iff_enc_eq_none {step : σ → Option σ} {x : σ} :
    Continues step x ↔ enc step x = none := enc_eq_none_iff.symm

/-- The halting universe (where the encoding is defined) and the continuation canon (where the
trajectory is defined) are exactly complementary. -/
theorem substrate_partition (step : σ → Option σ) :
    {x : σ | Continues step x} = {x : σ | (enc step x).isSome}ᶜ := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, enc_isSome_iff]
  exact continues_iff_not_halts

/-! ## §4 Equally natural: both readings are carried by simulations -/

/-- **Evaluation is equivariant under simulation.** -/
theorem run_map {step : σ → Option σ} {step' : τ → Option τ} {f : σ → τ}
    (hf : ∀ x, step' (f x) = (step x).map f) (x : σ) (n : ℕ) :
    run step' (f x) n = (run step x n).map f := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [run_succ, ih, run_succ]
      cases h : run step x k with
      | none => simp
      | some y => simp [hf y]

theorem eval_map {step : σ → Option σ} {step' : τ → Option τ} {f : σ → τ}
    (hf : ∀ x, step' (f x) = (step x).map f) (x : σ) (n : ℕ) :
    eval step' (f x) n = (eval step x n).map f := run_map hf x n

/-- The encoding depends only on the pattern of stopping stages: evaluation determines the
encoding. -/
theorem enc_eq_of_none_pattern {step₁ : σ → Option σ} {step₂ : τ → Option τ} {x : σ} {y : τ}
    (h : ∀ n, run step₁ x n = none ↔ run step₂ y n = none) : enc step₁ x = enc step₂ y := by
  rcases hx : enc step₁ x with _ | n
  · have hc : Continues step₁ x := enc_eq_none_iff.mp hx
    refine (enc_eq_none_iff.mpr ?_).symm
    intro m
    have : run step₂ y m ≠ none := fun hm => run_ne_none_of_continues hc m ((h m).mpr hm)
    cases hm : run step₂ y m with
    | none => exact absurd hm this
    | some _ => simp
  · obtain ⟨hn, hmin⟩ := enc_eq_some_iff.mp hx
    refine (enc_eq_some_iff.mpr ⟨(h n).mp hn, ?_⟩).symm
    intro m hm hcon
    exact hmin m hm ((h m).mpr hcon)

/-- **The encoding is invariant under simulation**: the halting universe does not move. -/
theorem enc_sim {step : σ → Option σ} {step' : τ → Option τ} {f : σ → τ}
    (hf : ∀ x, step' (f x) = (step x).map f) (x : σ) : enc step' (f x) = enc step x := by
  refine enc_eq_of_none_pattern (fun n => ?_)
  rw [run_map hf x n]
  cases h : run step x n <;> simp

/-! ## §5 Mutual determination, and no collapse -/

/-- Two data with the same evaluation have the same encoding. -/
theorem eval_determines_enc {step : σ → Option σ} {x y : σ} (h : ∀ n, eval step x n = eval step y n) :
    enc step x = enc step y :=
  enc_eq_of_none_pattern (fun n => by rw [show run step x n = run step y n from h n])

/-! ## §6 Concrete computers -/

/-- The countdown computer: step down by one, and stop at the bottom. -/
def countdown : ℕ → Option ℕ := fun n => if n = 0 then none else some (n - 1)

theorem run_countdown (x n : ℕ) : run countdown x n = if n ≤ x then some (x - n) else none := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [run_succ, ih]
      by_cases hk : k ≤ x
      · simp only [hk, if_true]
        by_cases hx : x - k = 0
        · have : ¬ (k + 1 ≤ x) := by omega
          simp [countdown, hx, this]
        · have hle : k + 1 ≤ x := by omega
          have : x - k - 1 = x - (k + 1) := by omega
          simp [countdown, hx, hle, this]
      · have : ¬ (k + 1 ≤ x) := by omega
        simp [hk, this]

/-- The countdown computer halts from every datum, with encoding `x + 1`. -/
theorem enc_countdown (x : ℕ) : enc countdown x = some (x + 1) := by
  refine enc_eq_some_iff.mpr ⟨?_, ?_⟩
  · rw [run_countdown]
    have : ¬ (x + 1 ≤ x) := by omega
    simp [this]
  · intro m hm
    rw [run_countdown]
    have : m ≤ x := by omega
    simp [this]

/-- The climbing computer: never stop. -/
def climb : ℕ → Option ℕ := fun n => some (n + 1)

theorem run_climb (x n : ℕ) : run climb x n = some (x + n) := by
  induction n with
  | zero => simp
  | succ k ih => rw [run_succ, ih]; simp [climb, Nat.add_assoc]

theorem continues_climb (x : ℕ) : Continues climb x := by
  intro n; rw [run_climb]; simp

/-- The climbing computer has empty encoding: it lies wholly outside the universe of halting. -/
theorem enc_climb (x : ℕ) : enc climb x = none := enc_eq_none_iff.mpr (continues_climb x)

/-- Its canonical trajectory is the obvious one. -/
theorem traj_climb (x n : ℕ) : traj climb (continues_climb x) n = x + n := by
  have := run_eq_traj (continues_climb x) n
  rw [run_climb] at this
  exact (Option.some.inj this).symm

/-- The countdown computer fibred over a tag: the same operation, carried on a second component. -/
def countdownPair : ℕ × Bool → Option (ℕ × Bool) :=
  fun p => if p.1 = 0 then none else some (p.1 - 1, p.2)

theorem countdownPair_sim (b : Bool) (n : ℕ) :
    countdownPair (n, b) = (countdown n).map (fun m => (m, b)) := by
  by_cases h : n = 0 <;> simp [countdownPair, countdown, h]

/-- Fibring is a simulation, so the encoding is untouched by it. -/
theorem enc_countdownPair (x : ℕ) (b : Bool) : enc countdownPair (x, b) = some (x + 1) := by
  rw [enc_sim (f := fun n => (n, b)) (fun n => countdownPair_sim b n) x, enc_countdown]

/-- **Equally natural, but not equal**: the encoding does not determine the evaluation.  Two data of
the fibred countdown machine share their encoding while their evaluations differ. -/
theorem enc_does_not_determine_eval :
    ∃ x y : ℕ × Bool, enc countdownPair x = enc countdownPair y ∧
      eval countdownPair x ≠ eval countdownPair y := by
  refine ⟨(1, true), (1, false), by rw [enc_countdownPair, enc_countdownPair], ?_⟩
  intro h
  have h0 := congrFun h 0
  rw [eval_zero, eval_zero] at h0
  simp at h0

/-! ## The answer -/

/-- **The clauses of NRRF789.**  For any computer on any substrate: the encoding's universe is the
halting set and the encoding is the unique reading of it; evaluation is the unique reading obeying
the evaluation laws and the unique trajectory canon of continuation; the two readings partition the
substrate; and both are carried by simulation — the encoding invariantly, the evaluation
equivariantly. -/
theorem nrrf789_answer (step : σ → Option σ) :
    ({x : σ | (enc step x).isSome} = {x : σ | Halts step x}) ∧
    (∃! e : σ → Option ℕ, EncSpec step e) ∧
    (∃! E : σ → ℕ → Option σ, EvalSpec step E) ∧
    (∀ {x : σ}, Continues step x →
      ∃! t : ℕ → σ, t 0 = x ∧ ∀ n, step (t n) = some (t (n + 1))) ∧
    ({x : σ | Continues step x} = {x : σ | (enc step x).isSome}ᶜ) ∧
    (∀ {τ : Type*} (step' : τ → Option τ) (f : σ → τ),
      (∀ x, step' (f x) = (step x).map f) →
        (∀ x, enc step' (f x) = enc step x) ∧
          ∀ x n, eval step' (f x) n = (eval step x n).map f) :=
  ⟨enc_universe step, enc_exists_unique step, eval_exists_unique step,
   fun h => trajectory_exists_unique h, substrate_partition step,
   fun _ _ hf => ⟨fun x => enc_sim hf x, fun x n => eval_map hf x n⟩⟩

end NRRF789

/-! ## Audit

Every headline result of this module, checked against the ambient axioms only. -/

section Audit

/-- info: 'NRRF789.enc_universe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF789.enc_universe

/-- info: 'NRRF789.enc_exists_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF789.enc_exists_unique

/-- info: 'NRRF789.eval_exists_unique' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms NRRF789.eval_exists_unique

/-- info: 'NRRF789.trajectory_exists_unique' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms NRRF789.trajectory_exists_unique

/-- info: 'NRRF789.substrate_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF789.substrate_partition

/-- info: 'NRRF789.enc_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF789.enc_sim

/-- info: 'NRRF789.enc_does_not_determine_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF789.enc_does_not_determine_eval

/-- info: 'NRRF789.nrrf789_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF789.nrrf789_answer

end Audit
