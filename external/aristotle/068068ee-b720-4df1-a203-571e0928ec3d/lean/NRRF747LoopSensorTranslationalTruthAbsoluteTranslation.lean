import Mathlib
import NRRF739LoopSensorClosureFourfoldTopologyFusionLevel
import NRRF740FullUnifiedClosureEquationsAdmissibleDerivationsForms
import NRRF746TruthPriorToDefinitionRelativeDuringAbsoluteTranslation

/-!
# NRRF747 — The loop sensor as the relative definition whose absolute translation is truth

This module carries the principle of NRRF746 (*truth cannot be defined prior to definition; a
relative definition is partial and happens **during**; truth is the absolute translation of the
relative definitions*) through the **loop sensor / sensor loop** translational-truth idea of
NRRF739.

## The reading

* A **site** is an element `m : ℤ` of the line; a **claim** is an identity assertion between two
  sites, `p : ℤ × ℤ`, and its truth is `p.1 = p.2`.
* A **loop sensor of period `k`** (`NRRF739.LoopSensor k`) reads the line into `ZMod k`, advancing
  by one per translation step.  It is the concrete *relative* definition: it never sees a site, only
  translations, and it sees them only modulo `k`.
* A sensor's verdict on a claim is *readings alike / readings apart*.  Apart is always sound
  (`sites_ne_of_reads_apart`); alike is **not** (`no_single_loop_defines_truth`): a single loop is a
  partial definition, and its false positives are exactly the multiples of its period.
* Widening the period together with the window of sites being compared gives a **stage system** in
  the sense of NRRF746 (`sensorSystem`): sound, monotone, cofinal, and never complete.
* Its **absolute translation** is the truth of site identity itself (`sensorSystem_absDef`,
  `site_truth_is_absolute_translation`): truth is what all the loop readings say together, and no
  single reading is it.

## The results

1. **Relative.**  `canonSensor_eq_lineLoop_eval` — the sensor is literally the evaluation half of
   NRRF739's line→loop closure, so "loop" and "sensor" are one relative definition seen twice; and
   `readsAlike_sensor_independent` — the verdict does not depend on which sensor of the period is
   used (translational truth is prior to the identification of a site).
2. **Partial.**  `no_single_loop_defines_truth`, `loop_reading_not_sound`: no loop reading, at any
   period, is a sound definition of site identity.  `sensorStage_undefined_outside_window`.
3. **During.**  `sensorSystem` is a `NRRF746.StageSystem`; hence `sensor_undefined_truth` (every
   stage leaves a true identity without a verdict), `sensor_stage_strictly_during`,
   `sensor_no_definition_past_absolute`.
4. **Absolute translation.**  `sensorSystem_absDef`, `site_truth_is_absolute_translation`,
   `eq_iff_forall_loop_reading` (a site identity is exactly the agreement of *all* loop readings),
   `sensor_eventually_stable`.
5. **The sensor loop as a closure.**  `towerClosure` reads the line into the whole tower of loops;
   the return equation holds (`towerClosure.eval_encode`) but the closing equation fails
   (`tower_not_closes`, `towerRead_not_surjective`): the tower has readings no site realizes, so the
   absolute translation is approached from strictly inside — *during*, never *past*.
-/

namespace NRRF747

open NRRF739 NRRF746

/-! ## §1  Sites, claims, and the canonical loop sensor -/

/-- A **claim**: the assertion that two sites of the line are the same site. -/
abbrev SiteClaim := ℤ × ℤ

/-- The truth of a claim: the two sites really are one site. -/
def SiteTruth (p : SiteClaim) : Prop := p.1 = p.2

instance : DecidablePred SiteTruth := fun p => inferInstanceAs (Decidable (p.1 = p.2))

/-- The **canonical loop sensor** of period `k`: reduction of the line modulo `k`, normalized at
the origin. -/
def canonSensor (k : ℕ) : LoopSensor k where
  read := fun m => (m : ZMod k)
  read_succ := by intro m; push_cast; ring

@[simp] theorem canonSensor_read (k : ℕ) (m : ℤ) : (canonSensor k).read m = (m : ZMod k) := rfl

/-- **Loop and sensor are one relative definition.**  The canonical sensor of period `k` is exactly
the evaluation half of NRRF739's line→loop closure. -/
theorem canonSensor_eq_lineLoop_eval (k : ℕ) [NeZero k] :
    (canonSensor k).read = (lineLoopClosure k).eval :=
  loopSensor_is_lineLoop_eval _ (by simp)

/-- A sensor's verdict on a claim: the two sites read alike. -/
def ReadsAlike {k : ℕ} (s : LoopSensor k) (p : SiteClaim) : Prop := s.read p.1 = s.read p.2

instance {k : ℕ} (s : LoopSensor k) (p : SiteClaim) : Decidable (ReadsAlike s p) :=
  inferInstanceAs (Decidable (s.read p.1 = s.read p.2))

/-- Reading alike is reading the same translation: divisibility by the period. -/
theorem readsAlike_iff {k : ℕ} (s : LoopSensor k) (p : SiteClaim) :
    ReadsAlike s p ↔ (k : ℤ) ∣ (p.1 - p.2) := s.read_eq_iff p.1 p.2

/-- **The verdict is sensor-independent.**  Any two loop sensors of the same period return the same
verdict on every claim: the relative definition belongs to the period, not to the sensor's
identification of the origin. -/
theorem readsAlike_sensor_independent {k : ℕ} (s t : LoopSensor k) (p : SiteClaim) :
    ReadsAlike s p ↔ ReadsAlike t p := by
  rw [readsAlike_iff, readsAlike_iff]

/-! ## §2  A single loop is only a partial definition -/

/-- **Apart is sound.**  If the readings differ, the sites really differ: what a loop sensor
positively separates, it separates truly. -/
theorem sites_ne_of_reads_apart {k : ℕ} (s : LoopSensor k) (p : SiteClaim)
    (h : ¬ ReadsAlike s p) : ¬ SiteTruth p := by
  intro hp
  exact h (by simp [ReadsAlike, SiteTruth] at hp ⊢; rw [hp])

/-- **Alike is not sound.**  At every period `k ≥ 1` and for every sensor of that period there are
distinct sites that read alike: a single loop reading is never a definition of truth. -/
theorem no_single_loop_defines_truth {k : ℕ} (hk : 0 < k) (s : LoopSensor k) :
    ∃ p : SiteClaim, ReadsAlike s p ∧ ¬ SiteTruth p :=
  ⟨(0, (k : ℤ)), by simp [readsAlike_iff], by simp [SiteTruth]; omega⟩

/-- The total definition "true iff the readings agree" is **not sound** for site identity, at any
period. -/
theorem loop_reading_not_sound {k : ℕ} (hk : 0 < k) (s : LoopSensor k) :
    ¬ Sound SiteTruth (fun p => some (decide (ReadsAlike s p))) := by
  intro hsound
  obtain ⟨p, hp, hnp⟩ := no_single_loop_defines_truth hk s
  exact hnp ((hsound p true (by simp [hp])).mpr rfl)

/-! ## §3  Widening loops: the relative definition unfolds in stages -/

/-- The window of stage `n`: the claims whose two sites both lie within `n` of the origin. -/
def Window (n : ℕ) (p : SiteClaim) : Prop := p.1.natAbs ≤ n ∧ p.2.natAbs ≤ n

instance (n : ℕ) (p : SiteClaim) : Decidable (Window n p) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **Inside its window, the loop reading is exact.**  Two sites within `n` of the origin read
alike in the loop of period `2n+1` exactly when they are the same site. -/
theorem readsAlike_iff_eq_of_window {n : ℕ} {p : SiteClaim} (hp : Window n p) :
    ReadsAlike (canonSensor (2 * n + 1)) p ↔ SiteTruth p := by
  rw [readsAlike_iff]
  constructor
  · intro h
    have habs : |p.1 - p.2| < ((2 * n + 1 : ℕ) : ℤ) := by
      have h1 := hp.1
      have h2 := hp.2
      have e : |p.1 - p.2| = ((p.1 - p.2).natAbs : ℤ) := Int.abs_eq_natAbs _
      rw [e]
      push_cast
      omega
    have hz : p.1 - p.2 = 0 := Int.eq_zero_of_abs_lt_dvd h habs
    show p.1 = p.2
    omega
  · intro h
    simp [SiteTruth] at h
    simp [h]

/-- Stage `n` of the loop-sensor definition of truth: inside the window of radius `n`, the verdict
of the loop of period `2n+1`; outside it, silence. -/
def sensorStage (n : ℕ) : PDef SiteClaim := fun p =>
  if Window n p then some (decide (ReadsAlike (canonSensor (2 * n + 1)) p)) else none

theorem sensorStage_eq (n : ℕ) (p : SiteClaim) :
    sensorStage n p = if Window n p then some (decide (SiteTruth p)) else none := by
  unfold sensorStage
  by_cases h : Window n p
  · simp only [if_pos h]
    congr 1
    simp [readsAlike_iff_eq_of_window h]
  · simp [h]

theorem sensorStage_undefined_outside_window {n : ℕ} {p : SiteClaim} (h : ¬ Window n p) :
    sensorStage n p = none := by simp [sensorStage_eq, h]

/-- **The loop-sensor stage system.**  A partial relative definition of site identity, unfolding in
loops of growing period: sound, only extending, reaching every claim, and complete at no stage. -/
def sensorSystem : StageSystem SiteClaim where
  T := SiteTruth
  d := sensorStage
  sound := by
    intro n p b hb
    rw [sensorStage_eq] at hb
    by_cases h : Window n p
    · rw [if_pos h] at hb
      have : decide (SiteTruth p) = b := Option.some.injEq _ _ ▸ hb
      subst this
      simp
    · rw [if_neg h] at hb
      exact absurd hb (by simp)
  mono := by
    intro n p b hb
    rw [sensorStage_eq] at hb ⊢
    by_cases h : Window n p
    · have h' : Window (n + 1) p := ⟨by have := h.1; omega, by have := h.2; omega⟩
      rw [if_pos h] at hb
      rw [if_pos h']
      exact hb
    · rw [if_neg h] at hb
      exact absurd hb (by simp)
  reached := by
    intro p
    refine ⟨max p.1.natAbs p.2.natAbs, ?_⟩
    have h : Window (max p.1.natAbs p.2.natAbs) p := ⟨le_max_left _ _, le_max_right _ _⟩
    simp [Defined, sensorStage_eq, h]
  proper := by
    intro n
    refine ⟨((n : ℤ) + 1, (n : ℤ) + 1), rfl, ?_⟩
    have h : ¬ Window n (((n : ℤ) + 1, (n : ℤ) + 1) : SiteClaim) := by
      simp only [Window, not_and_or]
      left
      have : ((n : ℤ) + 1).natAbs = n + 1 := by omega
      omega
    simp [sensorStage_eq, h]

/-! ## §4  The absolute translation of the loop readings is the truth of site identity -/

/-- **Undefined truth at every loop.**  At every stage there is a true site identity on which the
loop sensor is silent. -/
theorem sensor_undefined_truth (n : ℕ) :
    ∃ p : SiteClaim, SiteTruth p ∧ ¬ Defined (sensorStage n) p :=
  sensorSystem.exists_undefined_truth n

theorem sensor_no_stage_is_total (n : ℕ) : ¬ Total (sensorStage n) :=
  sensorSystem.no_stage_is_total n

/-- **Truth is the absolute translation of the loop readings.**  Two sites are the same site
exactly when some loop stage reads them alike inside its window. -/
theorem site_truth_is_absolute_translation (p : SiteClaim) :
    SiteTruth p ↔ ∃ n, sensorStage n p = some true := sensorSystem.abs_eq_truth p

/-- The absolute definition produced by the tower of loops is the decision of site identity. -/
theorem sensorSystem_absDef (p : SiteClaim) :
    sensorSystem.absDef p = some (decide (SiteTruth p)) := by
  refine sensorSystem.absDef_eq_of_stage (n := max p.1.natAbs p.2.natAbs) ?_
  have h : Window (max p.1.natAbs p.2.natAbs) p := ⟨le_max_left _ _, le_max_right _ _⟩
  show sensorStage (max p.1.natAbs p.2.natAbs) p = _
  rw [sensorStage_eq, if_pos h]

/-- Each loop stage is strictly inside the absolute translation: relative definition is **during**,
never prior and never past. -/
theorem sensor_stage_strictly_during (n : ℕ) :
    Extends (sensorStage n) sensorSystem.absDef ∧
      ∃ p, Defined sensorSystem.absDef p ∧ ¬ Defined (sensorStage n) p :=
  sensorSystem.stage_strictly_during n

theorem sensor_no_definition_past_absolute {e : PDef SiteClaim} (he : Sound SiteTruth e)
    (het : Total e) : e = sensorSystem.absDef :=
  sensorSystem.no_definition_past_absolute he het

/-- Continuity: every claim's absolute verdict is already the verdict of some finite loop, and of
all wider ones. -/
theorem sensor_eventually_stable (p : SiteClaim) :
    ∃ n, ∀ m, n ≤ m → sensorStage m p = sensorSystem.absDef p :=
  sensorSystem.eventually_stable p

/-- **Truth as the agreement of all loop readings.**  Two sites are one site exactly when every
loop sensor, at every period, reads them alike — the absolute translation stated directly in the
sensors' own language. -/
theorem eq_iff_forall_loop_reading (m n : ℤ) :
    m = n ↔ ∀ k : ℕ, 0 < k → (canonSensor k).read m = (canonSensor k).read n := by
  constructor
  · rintro rfl _ _; rfl
  · intro h
    have hk := h (m - n).natAbs.succ (Nat.succ_pos _)
    have hdvd : (((m - n).natAbs.succ : ℕ) : ℤ) ∣ (m - n) :=
      ((canonSensor _).read_eq_iff m n).mp hk
    have habs : |m - n| < (((m - n).natAbs.succ : ℕ) : ℤ) := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast Nat.lt_succ_self _
    have := Int.eq_zero_of_abs_lt_dvd hdvd habs
    omega

/-! ## §5  The sensor loop as a closure: the return holds, the closing fails -/

/-- The **sensor loop tower**: reading a site in every loop at once. -/
def towerRead (m : ℤ) : ∀ k : ℕ, ZMod (k + 1) := fun k => (m : ZMod (k + 1))

/-- The tower of loop readings is a faithful relative definition of the site: distinct sites are
separated somewhere in the tower. -/
theorem towerRead_injective : Function.Injective towerRead := by
  intro m n h
  refine (eq_iff_forall_loop_reading m n).mpr ?_
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact congrFun h j

/-- No site realizes the reading that is odd in the loop of period `2` and zero in the loop of
period `4`: the tower has readings that are not translations of the origin. -/
theorem towerRead_not_surjective : ¬ Function.Surjective towerRead := by
  intro hsurj
  obtain ⟨m, hm⟩ := hsurj (fun k => if k = 1 then (1 : ZMod (k + 1)) else 0)
  have h2 : ((m : ZMod 2)) = 1 := by
    have := congrFun hm 1
    simpa [towerRead] using this
  have h4 : ((m : ZMod 4)) = 0 := by
    have := congrFun hm 3
    simpa [towerRead] using this
  have hd4 : (4 : ℤ) ∣ m := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd m 4).mp h4
    exact_mod_cast this
  have hd2 : ¬ ((2 : ℤ) ∣ m) := by
    intro hd
    have : ((m : ZMod 2)) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact_mod_cast hd
    rw [h2] at this
    exact absurd this (by decide)
  exact hd2 (dvd_trans (by norm_num) hd4)

open Classical in
/-- The **sensor loop closure**: the line encodes into the tower of loops, and the tower evaluates
back to the site it reads.  The return equation `eval ∘ encode = id` holds. -/
noncomputable def towerClosure : Closure ℤ (∀ k : ℕ, ZMod (k + 1)) where
  encode := towerRead
  eval := fun b => if h : ∃ m, towerRead m = b then h.choose else 0
  eval_encode := by
    intro m
    have h : ∃ m', towerRead m' = towerRead m := ⟨m, rfl⟩
    rw [dif_pos h]
    exact towerRead_injective h.choose_spec

/-- **The closing equation fails.**  The sensor loop tower is not transparent: it carries readings
no site realizes, so the absolute translation is reached from strictly inside the relative
readings — the loop sensor works *during*, never past. -/
theorem tower_not_closes : ¬ NRRF740.Closes towerClosure := by
  rw [NRRF740.closes_iff_transparent, Closure.transparent_iff_bijective]
  intro h
  exact towerRead_not_surjective h.2

/-! ## §6  No reading is prior to the reading -/

/-- The NRRF746 obstruction in the sensors' own language: **no language of sites applies to itself
completely**, so no reading of the line is settled prior to the readings. -/
theorem no_complete_site_language (app : SiteClaim → SiteClaim → Prop)
    (complete : ∀ p : SiteClaim → Prop, ∃ c, ∀ x, app c x ↔ p x) : False :=
  no_definitionally_complete_language app complete

/-! ## §7  The answer -/

/-- **The principle of NRRF746, carried through the loop sensor.**

1. No single loop reading, at any period, defines the truth of site identity: alike is unsound and
   the loop is only a partial, relative definition.
2. Yet what the loop separates, it separates truly, and the verdict belongs to the period rather
   than to any sensor's identification of the origin.
3. The widening loops form a stage system: at every stage some true identity is still undefined.
4. Truth is the absolute translation of these relative readings — the agreement of all loops — and
   every stage sits strictly inside it, with nothing sound beyond it.
5. The tower of loops returns every site it encodes, but does not close: readings exist that no
   site realizes. -/
theorem nrrf747_answer :
    (∀ k : ℕ, 0 < k → ∀ s : LoopSensor k, ∃ p : SiteClaim, ReadsAlike s p ∧ ¬ SiteTruth p) ∧
    (∀ (k : ℕ) (s : LoopSensor k) (p : SiteClaim), ¬ ReadsAlike s p → ¬ SiteTruth p) ∧
    (∀ (k : ℕ) (s t : LoopSensor k) (p : SiteClaim), ReadsAlike s p ↔ ReadsAlike t p) ∧
    (∀ n, ∃ p : SiteClaim, SiteTruth p ∧ ¬ Defined (sensorStage n) p) ∧
    (∀ p : SiteClaim, SiteTruth p ↔ ∃ n, sensorStage n p = some true) ∧
    (∀ m n : ℤ, m = n ↔ ∀ k : ℕ, 0 < k → (canonSensor k).read m = (canonSensor k).read n) ∧
    (∀ n, Extends (sensorStage n) sensorSystem.absDef ∧ sensorStage n ≠ sensorSystem.absDef) ∧
    (∀ e : PDef SiteClaim, Sound SiteTruth e → Total e → e = sensorSystem.absDef) ∧
    (Function.Injective towerRead ∧ ¬ NRRF740.Closes towerClosure) :=
  ⟨fun _ hk s => no_single_loop_defines_truth hk s,
   fun _ s p h => sites_ne_of_reads_apart s p h,
   fun _ s t p => readsAlike_sensor_independent s t p,
   sensor_undefined_truth,
   site_truth_is_absolute_translation,
   eq_iff_forall_loop_reading,
   fun n => ⟨sensorSystem.stage_extends_abs n, sensorSystem.stage_ne_absDef n⟩,
   fun _ he het => sensor_no_definition_past_absolute he het,
   ⟨towerRead_injective, tower_not_closes⟩⟩

end NRRF747
