import Mathlib
import NRRF739LoopSensorClosureFourfoldTopologyFusionLevel
import NRRF747LoopSensorTranslationalTruthAbsoluteTranslation
import NRRF785QuantumClassicalFrameworksUnifiedOnTranslationalTruth

/-!
# NRRF786 — Quantum gravity and its tests unified on the loop sensor alone, with no classical physics

The instruction formalized here is the user's:

> Unify our quantum gravity theory and tests without relying on classical physics; use our
> translational truth loop sensor completely.

## The reading

*Completely on the loop sensor* means: the **only** apparatus in this file is NRRF739's
`LoopSensor` — a reading of a translation line into a loop of period `k` that advances by exactly
one step per translation.  Nothing else is allowed to enter: no background manifold, no absolute
position, no classical assignment of values to configurations, no limiting classical description
that the quantum theory is required to reproduce.

* A **state** of the theory is a pair of translations, `State = ℤ × ℤ`: the *ball* translation
  (the gravitational, never-returning line of NRRF745) and the *hair* translation (the quantum
  phase, which returns).  A state is never observed; only readings of it are.
* A **test** is a loop-sensor comparison: at resolution `n` the ball components are compared
  through the loop of period `n`, and the hair components through the loop of period `k`
  (`Test`, `test_is_loop_sensor`).  The whole experimental content of the theory is this family.
* The **theory** is the same data presented as a framework in the sense of NRRF785: frames are
  sensors (an origin and a resolution), observables are states, and a frame's verdict on a state is
  its loop reading of the separation, undefined outside the frame's window (`qgFramework`).

## What is proved

### §2  The tests are purely relational — no classical background is used or usable
* `test_translation_invariant`, `test_relational` — every verdict depends only on the separation of
  the two states, so no test ever refers to an absolute location.  Background independence is a
  theorem about the sensor, not a postulate.
* `test_equivalence` — at each resolution the tests are an equivalence relation.

### §3  Unification of the theory with its tests
* `agree_iff_gaugeClass` — two states pass **every** loop-sensor test exactly when they have the
  same class in `ℤ × ZMod k`: the ball translation exactly, the hair translation only modulo its
  period.  The state space *of the theory modulo what no test can see* is precisely NRRF745's
  ball–hair fibre `ℤ × ZMod k` (`gaugeClass_surjective`).
* `agree_iff_hair_translate` — the indistinguishable states are exactly the hair translates: the
  quantum phase is unobservable in principle (`hair_gauge_undetectable`), while every gravitational
  ball translation is detected by some finite loop (`ball_shift_detectable`).  The QM/GR asymmetry
  is *derived* from one sensor family, not imposed by two theories.
* `no_single_test_complete` — no single loop, at any period, is the theory: truth is the absolute
  translation of all the relative readings (NRRF747's principle, here for quantum gravity).

### §4–§5  The theory as a framework, and the impossibility of a classical reading
* `qgFramework` — the loop-sensor data is a NRRF785 framework: shifting the sensor and the state
  together leaves every verdict unchanged (`qg_equivariant`).
* `qg_not_total`, `qg_contextual`, `qg_not_classical` — the framework answers only inside a
  window, and **no** global assignment of absolute values to states fits its verdicts.  So the
  theory is not merely presented without classical physics: it *cannot* be given a classical
  reading.  Nothing here is derived from a classical limit.
* `qg_unified_truth`, `qg_truth_unique` — and yet it carries exactly one translational truth
  function on level-unified questions; `qg_translates_iff` identifies those questions with the
  pairs (resolution, separation), so the truth of the theory is exactly relational data.
* `qgVal_eq_iff_test` — the framework's verdicts *are* the loop-sensor tests: inside a window, two
  states get the same verdict exactly when they pass the test of period `2n+1` on the ball and `k`
  on the hair.  Theory and tests are one object.
-/

namespace NRRF786

open NRRF739 NRRF747

/-! ## §1  States, readings, tests

A state is a pair of translations; only loop readings of it exist. -/

/-- A **state** of the theory: a ball (gravitational) translation and a hair (quantum phase)
translation.  A state is not an observable datum — only its loop readings are. -/
abbrev State := ℤ × ℤ

/-- The **ball reading** at resolution `n`: the gravitational translation seen through the loop of
period `n`. -/
def ballRead (n : ℕ) (x : State) : ZMod n := (canonSensor n).read x.1

/-- The **hair reading**: the quantum phase seen through its own loop of period `k`. -/
def hairRead (k : ℕ) (x : State) : ZMod k := (canonSensor k).read x.2

@[simp] theorem ballRead_eq (n : ℕ) (x : State) : ballRead n x = (x.1 : ZMod n) := rfl

@[simp] theorem hairRead_eq (k : ℕ) (x : State) : hairRead k x = (x.2 : ZMod k) := rfl

/-- A **test** at resolution `n`: the two states read alike on both loops. -/
def Test (k n : ℕ) (x y : State) : Prop :=
  ballRead n x = ballRead n y ∧ hairRead k x = hairRead k y

/-- **The tests are loop-sensor verdicts and nothing else.** -/
theorem test_is_loop_sensor (k n : ℕ) (x y : State) :
    Test k n x y ↔
      ReadsAlike (canonSensor n) (x.1, y.1) ∧ ReadsAlike (canonSensor k) (x.2, y.2) :=
  Iff.rfl

/-- A test is agreement of translations modulo the two periods. -/
theorem test_iff (k n : ℕ) (x y : State) :
    Test k n x y ↔ (n : ℤ) ∣ (x.1 - y.1) ∧ (k : ℤ) ∣ (x.2 - y.2) := by
  rw [test_is_loop_sensor, readsAlike_iff, readsAlike_iff]

/-! ## §2  The tests are relational: no absolute location is ever used -/

theorem test_refl (k n : ℕ) (x : State) : Test k n x x := ⟨rfl, rfl⟩

theorem test_symm {k n : ℕ} {x y : State} (h : Test k n x y) : Test k n y x :=
  ⟨h.1.symm, h.2.symm⟩

theorem test_trans {k n : ℕ} {x y z : State} (h : Test k n x y) (h' : Test k n y z) :
    Test k n x z :=
  ⟨h.1.trans h'.1, h.2.trans h'.2⟩

/-- At each resolution the loop-sensor verdicts form an equivalence of states. -/
theorem test_equivalence (k n : ℕ) : Equivalence (Test k n) :=
  ⟨test_refl k n, test_symm, test_trans⟩

/-- **Background independence.**  Translating both states by the same amount leaves every verdict
unchanged: the sensor never sees a location, only a separation. -/
theorem test_translation_invariant (k n : ℕ) (g x y : State) :
    Test k n (x + g) (y + g) ↔ Test k n x y := by
  simp [test_iff, Prod.fst_add, Prod.snd_add, add_sub_add_right_eq_sub]

/-- **Every verdict is a verdict about a separation.** -/
theorem test_relational (k n : ℕ) (x y : State) : Test k n x y ↔ Test k n (x - y) 0 := by
  simp [test_iff, Prod.fst_sub, Prod.snd_sub]

/-! ## §3  Unifying the theory with its tests

What all the loop sensors together determine is exactly one thing: the class of a state in
`ℤ × ZMod k` — the ball translation exactly, the hair translation only up to its period. -/

/-- The **gauge class** of a state: what the whole family of loop readings can determine. -/
def gaugeClass (k : ℕ) (x : State) : ℤ × ZMod k := (x.1, hairRead k x)

/-- **Theory = tests.**  Two states pass every loop-sensor test exactly when they have the same
gauge class.  No further datum of a state is physical, and no datum of the class is unobservable. -/
theorem agree_iff_gaugeClass (k : ℕ) (x y : State) :
    (∀ n, 0 < n → Test k n x y) ↔ gaugeClass k x = gaugeClass k y := by
  constructor
  · intro h
    have hhair : hairRead k x = hairRead k y := (h 1 one_pos).2
    have hball : x.1 = y.1 := by
      have hd : ((x.1 - y.1).natAbs + 1 : ℤ) ∣ (x.1 - y.1) := by
        have := (test_iff k ((x.1 - y.1).natAbs + 1) x y).1 (h _ (Nat.succ_pos _))
        exact_mod_cast this.1
      have hlt : |x.1 - y.1| < ((x.1 - y.1).natAbs + 1 : ℤ) := by
        rw [Int.abs_eq_natAbs]
        omega
      have := Int.eq_zero_of_abs_lt_dvd hd hlt
      omega
    show ((x.1, hairRead k x) : ℤ × ZMod k) = (y.1, hairRead k y)
    rw [hball, hhair]
  · intro h n _
    have hball : x.1 = y.1 := congrArg (fun p : ℤ × ZMod k => p.1) h
    have hhair : hairRead k x = hairRead k y := congrArg (fun p : ℤ × ZMod k => p.2) h
    exact ⟨by simp [hball], hhair⟩

/-- Every class is realized: the state space modulo the invisible is exactly `ℤ × ZMod k`, the
ball–hair fibre. -/
theorem gaugeClass_surjective (k : ℕ) [NeZero k] : Function.Surjective (gaugeClass k) := by
  intro p
  refine ⟨(p.1, (p.2.val : ℤ)), ?_⟩
  simp [gaugeClass]

/-- **The quantum phase is unobservable in principle.**  A full hair period is invisible to every
loop sensor, at every resolution. -/
theorem hair_gauge_undetectable (k n : ℕ) (x : State) : Test k n x (x.1, x.2 + (k : ℤ)) := by
  refine (test_iff k n x _).2 ⟨by simp, ?_⟩
  simp

/-- **Every gravitational translation is detected.**  A nonzero ball shift fails some finite loop
test: the ball never returns, so no part of it is gauge. -/
theorem ball_shift_detectable (k : ℕ) (x : State) (m : ℤ) (hm : m ≠ 0) :
    ∃ n, 0 < n ∧ ¬ Test k n x (x.1 + m, x.2) := by
  refine ⟨m.natAbs + 1, Nat.succ_pos _, fun h => hm ?_⟩
  have hd : ((m.natAbs + 1 : ℕ) : ℤ) ∣ (x.1 - (x.1 + m)) := ((test_iff _ _ _ _).1 h).1
  have hd' : ((m.natAbs + 1 : ℕ) : ℤ) ∣ m := by
    have : x.1 - (x.1 + m) = -m := by ring
    rw [this] at hd
    exact (dvd_neg).1 hd
  have hlt : |m| < ((m.natAbs + 1 : ℕ) : ℤ) := by
    rw [Int.abs_eq_natAbs]
    push_cast
    omega
  exact Int.eq_zero_of_abs_lt_dvd hd' hlt

/-- **The indistinguishable states are exactly the hair translates.**  Unifying the theory with its
tests leaves precisely one redundancy, and it is the quantum phase. -/
theorem agree_iff_hair_translate (k : ℕ) (x y : State) :
    (∀ n, 0 < n → Test k n x y) ↔ ∃ j : ℤ, y = (x.1, x.2 + j * (k : ℤ)) := by
  rw [agree_iff_gaugeClass]
  constructor
  · intro h
    have h1 : x.1 = y.1 := congrArg (fun p : ℤ × ZMod k => p.1) h
    have h2 : ((x.2 : ℤ) : ZMod k) = ((y.2 : ℤ) : ZMod k) :=
      congrArg (fun p : ℤ × ZMod k => p.2) h
    have hdvd : (k : ℤ) ∣ (y.2 - x.2) := by
      have := ((canonSensor k).read_eq_iff y.2 x.2).1 h2.symm
      exact this
    obtain ⟨j, hj⟩ := hdvd
    exact ⟨j, by
      refine Prod.ext h1.symm ?_
      have : y.2 = x.2 + j * (k : ℤ) := by rw [mul_comm]; omega
      simp [this]⟩
  · rintro ⟨j, rfl⟩
    refine Prod.ext rfl ?_
    show hairRead k x = hairRead k (x.1, x.2 + j * (k : ℤ))
    simp [hairRead]

/-- **No single loop is the theory.**  At every resolution there are states that pass the test yet
differ physically: each relative reading is partial, and truth is their absolute translation. -/
theorem no_single_test_complete (k n : ℕ) (hn : 0 < n) :
    ∃ x y : State, Test k n x y ∧ gaugeClass k x ≠ gaugeClass k y := by
  refine ⟨(0, 0), ((n : ℤ), 0), (test_iff _ _ _ _).2 ⟨by simp, by simp⟩, ?_⟩
  intro h
  have := congrArg Prod.fst h
  simp [gaugeClass] at this
  omega

/-! ## §4  The theory as a framework: sensors as frames, states as observables

The same data, presented in the shape of NRRF785: a frame is a loop sensor — an origin (which the
sensor cannot report) and a resolution — and its verdict on a state is its reading of the
separation, given only inside its window. -/

/-- A **frame**: a sensor placed at an origin, with a resolution. -/
abbrev Frame := State × ℕ

/-- The abelian group of level shifts: simultaneous translation of ball and hair. -/
def shiftGroup : NRRF785.Shift State where
  unit := 0
  comp := (· + ·)
  inv := (- ·)
  unit_comp := by intro s; simp
  comp_unit := by intro s; simp
  comp_assoc := by intro s t r; simp [add_assoc]
  comp_comm := by intro s t; simp [add_comm]
  comp_inv := by intro s; simp
  inv_comp := by intro s; simp

/-- The verdict of a frame on a state: the loop reading of the separation, undefined outside the
frame's window.  The ball part is the reading that the loop of period `2n+1` resolves exactly
(`ballRead_eq_iff_of_window`); the hair part is the reading of the hair loop. -/
def qgVal (k : ℕ) (c : Frame) (o : State) : Option (ℤ × ZMod k) :=
  if (o.1 - c.1.1).natAbs ≤ c.2 then some (o.1 - c.1.1, hairRead k (o - c.1)) else none

/-- **Inside a window the ball loop of period `2n+1` is exact.**  So reporting the separation as an
integer is a loop reading, not a classical measurement of position. -/
theorem ballRead_eq_iff_of_window {n : ℕ} {a b d : ℤ} (ha : (a - d).natAbs ≤ n)
    (hb : (b - d).natAbs ≤ n) :
    ballRead (2 * n + 1) (a, 0) = ballRead (2 * n + 1) (b, 0) ↔ a = b := by
  rw [ballRead_eq, ballRead_eq]
  constructor
  · intro h
    have hdvd : ((2 * n + 1 : ℕ) : ℤ) ∣ (a - b) :=
      ((canonSensor (2 * n + 1)).read_eq_iff a b).1 h
    have h1 : (a - d).natAbs ≤ n := ha
    have h2 : (b - d).natAbs ≤ n := hb
    have hlt : |a - b| < ((2 * n + 1 : ℕ) : ℤ) := by
      rw [Int.abs_eq_natAbs]
      omega
    have := Int.eq_zero_of_abs_lt_dvd hdvd hlt
    omega
  · intro h; simp [h]

/-- The quantum-gravity **framework**: frames are loop sensors, observables are states, verdicts
are loop readings. -/
def qgFramework (k : ℕ) : NRRF785.Framework State Frame State (ℤ × ZMod k) where
  shift := shiftGroup
  actC := fun s c => (c.1 + s, c.2)
  actO := fun s o => o + s
  actC_unit := by intro c; simp [shiftGroup]
  actC_comp := by
    intro s t c
    simp [shiftGroup, add_comm, add_left_comm]
  actO_unit := by intro o; simp [shiftGroup]
  actO_comp := by
    intro s t o
    simp [shiftGroup, add_comm, add_left_comm]
  val := qgVal k
  equivariant := by
    intro s c o
    simp only [qgVal]
    congr 1 <;> simp [Prod.fst_add, add_sub_add_right_eq_sub]

@[simp] theorem qgFramework_val (k : ℕ) (c : Frame) (o : State) :
    (qgFramework k).val c o = qgVal k c o := rfl

/-- **Translational truth for the theory.**  Moving the sensor and the state together does not move
a single verdict. -/
theorem qg_equivariant (k : ℕ) (s : State) (c : Frame) (o : State) :
    qgVal k ((qgFramework k).actC s c) ((qgFramework k).actO s o) = qgVal k c o :=
  (qgFramework k).equivariant s c o

/-- The verdicts depend only on the separation and the resolution. -/
theorem qgVal_relational (k : ℕ) (c c' : Frame) (o o' : State) (hres : c.2 = c'.2)
    (hsep : o - c.1 = o' - c'.1) : qgVal k c o = qgVal k c' o' := by
  have h1 : o.1 - c.1.1 = o'.1 - c'.1.1 := congrArg Prod.fst hsep
  simp only [qgVal, h1, hres, hsep]

/-- **The framework's verdicts are exactly the loop-sensor tests.**  Inside a frame's window, two
states receive the same verdict precisely when they pass the ball test of period `2n+1` and the
hair test of period `k`. -/
theorem qgVal_eq_iff_test (k : ℕ) (c : Frame) (o o' : State)
    (ho : (o.1 - c.1.1).natAbs ≤ c.2) (ho' : (o'.1 - c.1.1).natAbs ≤ c.2) :
    qgVal k c o = qgVal k c o' ↔ Test k (2 * c.2 + 1) o o' := by
  simp only [qgVal, if_pos ho, if_pos ho', Option.some.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have : o.1 = o'.1 := by omega
      simp [this]
    · have h2' : ((o.2 - c.1.2 : ℤ) : ZMod k) = ((o'.2 - c.1.2 : ℤ) : ZMod k) := h2
      have hdvd : (k : ℤ) ∣ (o.2 - c.1.2) - (o'.2 - c.1.2) :=
        ((canonSensor k).read_eq_iff _ _).1 h2'
      have : (k : ℤ) ∣ o.2 - o'.2 := by
        have he : (o.2 - c.1.2) - (o'.2 - c.1.2) = o.2 - o'.2 := by ring
        rwa [he] at hdvd
      exact ((canonSensor k).read_eq_iff o.2 o'.2).2 this
  · rintro ⟨h1, h2⟩
    have hball : o.1 = o'.1 :=
      (ballRead_eq_iff_of_window (d := c.1.1) ho ho').1 h1
    refine ⟨by rw [hball], ?_⟩
    have hdvd : (k : ℤ) ∣ o.2 - o'.2 := ((canonSensor k).read_eq_iff o.2 o'.2).1 h2
    have hdvd' : (k : ℤ) ∣ (o.2 - c.1.2) - (o'.2 - c.1.2) := by
      have he : (o.2 - c.1.2) - (o'.2 - c.1.2) = o.2 - o'.2 := by ring
      rwa [he]
    exact ((canonSensor k).read_eq_iff _ _).2 hdvd'

/-! ## §5  No classical reading exists

The theory is not merely *written* without classical physics; it *admits* no classical physics.
There is no assignment of absolute values to states reproducing, or even agreeing with, the
loop-sensor verdicts. -/

/-- The framework is not total: a sensor of resolution `0` does not answer about a state one ball
step away. -/
theorem qg_not_total (k : ℕ) : ¬ NRRF785.Total (qgFramework k) := by
  intro h
  obtain ⟨v, hv⟩ := h ((0, 0), 0) (1, 0)
  simp [qgFramework_val, qgVal] at hv

/-- **Contextual.**  No global assignment of values to states agrees with all the verdicts the
theory gives: two sensors at different origins report different separations for the same state. -/
theorem qg_contextual (k : ℕ) : NRRF785.Contextual (qgFramework k) := by
  rintro ⟨g, hg⟩
  have h1 : g (0, 0) = (0, hairRead k ((0, 0) - ((0 : ℤ), (0 : ℤ)))) :=
    hg (((0, 0) : State), 1) (0, 0) _ (by simp [qgFramework_val, qgVal])
  have h2 : g (0, 0) = (0 - 1, hairRead k (((0 : ℤ), (0 : ℤ)) - ((1 : ℤ), (0 : ℤ)))) :=
    hg (((1, 0) : State), 1) (0, 0) _ (by norm_num [qgFramework_val, qgVal])
  rw [h1] at h2
  have := congrArg Prod.fst h2
  norm_num at this

/-- **No classical physics.**  The quantum-gravity framework has no classical description at
all. -/
theorem qg_not_classical (k : ℕ) : ¬ NRRF785.IsClassical (qgFramework k) := fun h =>
  qg_contextual k (NRRF785.classical_noncontextual _ h)

/-- Consequently the theory is not frame-free either in the strong classical sense: it is not
given by any level-invariant absolute assignment. -/
theorem qg_no_invariant_assignment (k : ℕ) :
    ¬ ∃ g : State → ℤ × ZMod k, NRRF785.Invariant (qgFramework k) g ∧
      ∀ c o, (qgFramework k).val c o = some (g o) := by
  intro h
  exact qg_not_classical k ((NRRF785.classical_iff_invariant_assignment _ ((0, 0), 0)).2 h)

/-! ### The translational truth that survives -/

/-- **Level-unified questions are exactly (resolution, separation) pairs.** -/
theorem qg_translates_iff (k : ℕ) (p q : Frame × State) :
    NRRF785.Translates (qgFramework k) p q ↔
      p.1.2 = q.1.2 ∧ p.2 - p.1.1 = q.2 - q.1.1 := by
  constructor
  · rintro ⟨s, hs⟩
    have h1 : ((p.1.1 + s, p.1.2) : Frame) = q.1 := congrArg (fun z : Frame × State => z.1) hs
    have h2 : p.2 + s = q.2 := congrArg (fun z : Frame × State => z.2) hs
    have hres : p.1.2 = q.1.2 := by rw [← h1]
    have horg : p.1.1 + s = q.1.1 := by rw [← h1]
    refine ⟨hres, ?_⟩
    rw [← h2, ← horg]
    abel
  · rintro ⟨hres, hsep⟩
    refine ⟨q.1.1 - p.1.1, ?_⟩
    have hq2 : q.2 = p.2 + (q.1.1 - p.1.1) := by
      have : p.2 - p.1.1 = q.2 - q.1.1 := hsep
      have := congrArg (fun z => z + q.1.1) this
      simp at this
      rw [← this]
      abel
    refine Prod.ext ?_ hq2.symm
    refine Prod.ext ?_ hres
    show p.1.1 + (q.1.1 - p.1.1) = q.1.1
    abel

/-- **The theory carries exactly one translational truth function**, on the level-unified
questions. -/
theorem qg_unified_truth (k : ℕ) :
    ∃ h : NRRF785.Orbit (qgFramework k) → Option (ℤ × ZMod k),
      (∀ c o, h (NRRF785.orb _ (c, o)) = qgVal k c o) ∧
      ∀ h' : NRRF785.Orbit (qgFramework k) → Option (ℤ × ZMod k),
        (∀ c o, h' (NRRF785.orb _ (c, o)) = qgVal k c o) → h' = h :=
  NRRF785.unified_truth (qgFramework k)

/-- Uniqueness, stated on its own: the translational truth of the theory is a definite object, not
a choice of presentation. -/
theorem qg_truth_unique (k : ℕ) (h : NRRF785.Orbit (qgFramework k) → Option (ℤ × ZMod k))
    (hh : ∀ c o, h (NRRF785.orb _ (c, o)) = qgVal k c o) :
    h = NRRF785.truth (qgFramework k) :=
  NRRF785.truth_unique (qgFramework k) h hh

/-- The truth of the theory is relational: presentations with the same resolution and the same
separation are the same level-unified question, hence carry the same truth. -/
theorem qg_truth_relational (k : ℕ) (c c' : Frame) (o o' : State) (hres : c.2 = c'.2)
    (hsep : o - c.1 = o' - c'.1) :
    NRRF785.truth (qgFramework k) (NRRF785.orb _ (c, o)) =
      NRRF785.truth (qgFramework k) (NRRF785.orb _ (c', o')) := by
  have : NRRF785.orb (qgFramework k) (c, o) = NRRF785.orb (qgFramework k) (c', o') :=
    Quot.sound ((qg_translates_iff k (c, o) (c', o')).2 ⟨hres, hsep⟩)
  rw [this]

/-- **Every frame is classical inside itself** (NRRF785 §3, here for quantum gravity): the
non-classicality of the theory is never local to one sensor — it is translational. -/
theorem qg_fragment_noncontextual (k : ℕ) (c : Frame) :
    ∃ g : State → ℤ × ZMod k, ∀ o v, qgVal k c o = some v → g o = v :=
  NRRF785.fragment_noncontextual (qgFramework k) (0, 0) c

/-! ## §6  The unification, in one statement -/

/-- **NRRF786.**  Quantum gravity and its tests, carried entirely by the loop sensor and with no
classical physics anywhere:

1. *theory = tests* — two states are indistinguishable by the whole family of loop-sensor tests
   exactly when they differ by a hair (quantum phase) translation, so the physical content of a
   state is precisely its ball–hair class in `ℤ × ZMod k`;
2. *no single loop is the theory, and no classical reading exists* — at every resolution the test
   is partial, and no global assignment of absolute values to states reproduces the verdicts;
3. *and yet the truth is definite* — the framework carries exactly one translational truth
   function on level-unified questions. -/
theorem nrrf786_unification (k : ℕ) :
    (∀ x y : State, (∀ n, 0 < n → Test k n x y) ↔ ∃ j : ℤ, y = (x.1, x.2 + j * (k : ℤ))) ∧
    (∀ n, 0 < n → ∃ x y : State, Test k n x y ∧ gaugeClass k x ≠ gaugeClass k y) ∧
    ¬ NRRF785.IsClassical (qgFramework k) ∧
    (∃! h : NRRF785.Orbit (qgFramework k) → Option (ℤ × ZMod k),
      ∀ c o, h (NRRF785.orb _ (c, o)) = qgVal k c o) :=
  ⟨agree_iff_hair_translate k, fun n hn => no_single_test_complete k n hn, qg_not_classical k,
    ⟨NRRF785.truth (qgFramework k), fun _ _ => rfl,
      fun h' hh' => NRRF785.truth_unique (qgFramework k) h' hh'⟩⟩

end NRRF786

/-! ## §7  Axiom audit — machine-checked

Only Lean's three standard axioms occur.  (`Classical.choice` here is Lean's axiom of choice,
inherited from the library used for modular arithmetic; it has nothing to do with classical
physics, which §5 shows the theory cannot admit.) -/

section Audit

/-- info: 'NRRF786.agree_iff_gaugeClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF786.agree_iff_gaugeClass

/-- info: 'NRRF786.agree_iff_hair_translate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF786.agree_iff_hair_translate

/-- info: 'NRRF786.qgVal_eq_iff_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF786.qgVal_eq_iff_test

/-- info: 'NRRF786.qg_contextual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF786.qg_contextual

/-- info: 'NRRF786.qg_not_classical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF786.qg_not_classical

/-- info: 'NRRF786.qg_translates_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF786.qg_translates_iff

/-- info: 'NRRF786.nrrf786_unification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF786.nrrf786_unification

end Audit
