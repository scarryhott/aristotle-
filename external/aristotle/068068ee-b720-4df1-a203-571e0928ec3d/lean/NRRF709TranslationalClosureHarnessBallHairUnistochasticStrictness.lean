import Mathlib
import NRRF707BAdmissionRegressClosedReturnDesign

/-!
# NRRF709 — Translational closure as a harness: physical topology = digital evaluation, and the
strictness of the ball–hair return over unistochasticity

## The request

The user is not claiming that the path-ellipse picture *is* the square Cantor / Diósi–Penrose
material of NRRF708.  The claim is a *new translational closure*:

* the closure of a translation is the **relative ball–hair encoding** (ball) together with its
  **evaluation** (hair), whose return origin is the further translation;
* the closure operation is the *translational closure of the physical topology equal to its digital
  evaluation as one optomechanical harness*;
* **relative closure defines the ball–hair return**;
* the closure is *stronger* than a unistochastic matrix: it is not an absolute value, and not a
  `0`-double-contact in the `0 ∼ ∞` closure, but a translation of truth into unitary curvature as a
  topologically unified partition.

This module states and proves the mathematical content of those four sentences.  Nothing physical is
asserted: the types are arbitrary and the concrete instance is a finite complex matrix.

## §1  The harness

`Harness r e : ∀ x y, r x = r y ↔ e x = e y` — the physical return `r` and the digital evaluation
`e` induce *the same partition* of occurrences.  This is an equivalence relation on evaluations
(`harness_refl/symm/trans`), and — the precise sense of "one harness" —

* `harness_translation_existsUnique` : over a surjective return there is **exactly one** translation
  `t` with `t ∘ r = e`, and
* `harness_translation_injective` : it is injective, so the two readings are mutually recoverable —
  equal interpretability, in both directions, by the user;
* `harness_iff_injective_translation` : the converse holds too, so "same partition" and "a unique
  invertible dictionary between the two readings" are the *same* statement.

Closure is preserved by relabelling on either side (`harness_comp_injective`, `harness_precomp`):
a translation of truth does not change the closure.

## §2  Relative closure defines the ball–hair return

`ballHair r h x = (r x, h x)`.  Its kernel is exactly the intersection of the ball kernel with the
hair kernel (`ballHair_harness_iff`), it refines both (`ballHair_refines_ball`,
`ballHair_refines_hair`), and it is the **coarsest** such return: any evaluation that cannot
distinguish two occurrences with equal ball and equal hair factors through it
(`ballHair_universal`).  Consequently the ball–hair return is determined by the relative closure up
to a *unique bijective translation* (`ball_hair_return_unique_up_to_translation`): the relative
closure defines the ball–hair return, and the return origin of that definition is exactly the
further translation `t`.

## §3  Light and dark: the mirror is a hair phenomenon

On `B × Bool` (a based path together with its light/dark traversal sense) the mirror involution
`mirrorFlip` leaves the ball return invariant (`ball_mirror_invariant`) but is detected by the
ball–hair return (`ballHair_mirror_not_invariant`, `mirror_pair_ball_indistinguishable`), and the
ball–hair return of the pair is a harness for the identity reading
(`ballHair_pathSense_harness_id`).  So light/dark is not extra data added to the topology: it is
precisely the hair of the same closure.

## §4  Strictly stronger than unistochastic

For a complex square matrix, `unistoch U i j = ‖U i j‖ ^ 2` (the unistochastic reading, an absolute
value), `ballM U i j = ‖U i j‖` and `hairM U i j = U i j / ‖U i j‖` (the phase, with the convention
`1` at a zero entry).

* `ball_hair_reconstruct` : `ballM U i j * hairM U i j = U i j` — the ball–hair return *is* the
  matrix; `ballHairM_injective` : it is injective.
* `unistoch_eq_ballM_sq` : the unistochastic reading factors through the ball alone.
* `unistoch_col_sum` : for `Uᴴ * U = 1` the columns of `unistoch U` sum to `1` (the doubly
  stochastic content that the unistochastic reading does retain).
* `unistoch_diagonal_gauge` : `unistoch` is invariant under the diagonal phase gauge group, and
  `hairM_detects_gauge` : the hair is not — the hair is exactly the gauge datum.
* `unistoch_not_injective` : two genuinely different unitaries with the same unistochastic matrix.
* `closure_strictly_stronger_than_unistochastic` bundles it: the ball–hair closure separates
  everything the unistochastic absolute value conflates.
-/

namespace NRRF709

open Function Matrix

/-! ## §1  Closure as a harness: physical return and digital evaluation, one partition -/

variable {A B C D K K' : Type*}

/-- **The harness.**  A return `r` (the physical topology) and an evaluation `e` (the digital
reading) are *one harness* when they induce the same partition of occurrences. -/
def Harness (r : A → B) (e : A → D) : Prop := ∀ x y, r x = r y ↔ e x = e y

theorem harness_refl (r : A → B) : Harness r r := fun _ _ => Iff.rfl

theorem harness_symm {r : A → B} {e : A → D} (h : Harness r e) : Harness e r :=
  fun x y => (h x y).symm

theorem harness_trans {r : A → B} {e : A → D} {f : A → C}
    (h₁ : Harness r e) (h₂ : Harness e f) : Harness r f :=
  fun x y => (h₁ x y).trans (h₂ x y)

/-- An injective translation between the two readings produces a harness. -/
theorem harness_of_injective_translation {r : A → B} {e : A → D} {t : B → D}
    (ht : ∀ x, t (r x) = e x) (hinj : Injective t) : Harness r e := by
  intro x y
  constructor
  · intro h; rw [← ht, ← ht, h]
  · intro h; exact hinj (by rw [ht, ht]; exact h)

/-- **The translation exists and is unique.**  Over a surjective return, a harness is the same
thing as a single dictionary `t` carrying the physical return to the digital evaluation. -/
theorem harness_translation_existsUnique {r : A → B} {e : A → D}
    (hr : Surjective r) (h : Harness r e) : ∃! t : B → D, ∀ x, t (r x) = e x := by
  refine ⟨fun b => e (surjInv hr b), fun x => (h _ _).1 (surjInv_eq hr (r x)), ?_⟩
  intro t ht
  funext b
  obtain ⟨x, rfl⟩ := hr b
  rw [ht x]
  exact ((h _ _).1 (surjInv_eq hr (r x))).symm

/-- The translation of a harness is injective: the two readings are mutually recoverable. -/
theorem harness_translation_injective {r : A → B} {e : A → D} {t : B → D}
    (hr : Surjective r) (h : Harness r e) (ht : ∀ x, t (r x) = e x) : Injective t := by
  intro b₁ b₂ hb
  obtain ⟨x, rfl⟩ := hr b₁
  obtain ⟨y, rfl⟩ := hr b₂
  rw [ht x, ht y] at hb
  exact (h x y).2 hb

/-- **Equal interpretability.**  Over a surjective return, "physical topology and digital evaluation
are one harness" is *equivalent* to the existence of an injective translation between them. -/
theorem harness_iff_injective_translation {r : A → B} {e : A → D} (hr : Surjective r) :
    Harness r e ↔ ∃ t : B → D, Injective t ∧ ∀ x, t (r x) = e x := by
  constructor
  · intro h
    obtain ⟨t, ht, -⟩ := harness_translation_existsUnique hr h
    exact ⟨t, harness_translation_injective hr h ht, ht⟩
  · rintro ⟨t, hinj, ht⟩
    exact harness_of_injective_translation ht hinj

/-- Relabelling the evaluation by an injection preserves the closure. -/
theorem harness_comp_injective {r : A → B} {e : A → D} {f : D → C}
    (h : Harness r e) (hf : Injective f) : Harness r (f ∘ e) := by
  intro x y
  exact (h x y).trans ⟨fun hh => congrArg f hh, fun hh => hf hh⟩

/-- Restricting along any reparametrisation of occurrences preserves the closure. -/
theorem harness_precomp {r : A → B} {e : A → D} (h : Harness r e) (g : C → A) :
    Harness (r ∘ g) (e ∘ g) := fun x y => h (g x) (g y)

/-! ### The harness is exactly an equality of admissions

Bridge to the existing layer (NRRF707B): the admissions for a physical return and for a digital
evaluation coincide precisely on the harness relation. -/

/-- Under a harness, a relation admits the physical return iff it admits the digital evaluation. -/
theorem harness_adm_iff {r : A → B} {e : A → D} (h : Harness r e) (R : Setoid A) :
    (∀ x y : A, r x = r y → R.r x y) ↔ (∀ x y : A, e x = e y → R.r x y) := by
  constructor
  · intro hR x y hxy; exact hR x y ((h x y).2 hxy)
  · intro hR x y hxy; exact hR x y ((h x y).1 hxy)

/-- Hence the two readings have literally the same type of admissions: one harness, one supply of
admissible identities. -/
theorem harness_adm_eq {A : Type*} {B D : Type*} {r : A → B} {e : A → D} (h : Harness r e) :
    NRRF707B.Adm r = NRRF707B.Adm e := by
  unfold NRRF707B.Adm
  have hfun : (fun R : Setoid A => ∀ x y : A, r x = r y → R.r x y)
      = (fun R : Setoid A => ∀ x y : A, e x = e y → R.r x y) :=
    funext fun R => propext (harness_adm_iff h R)
  rw [hfun]

/-! ## §2  Relative closure defines the ball–hair return -/

/-- **The ball–hair return**: the total (ball) return recorded together with its relative
evaluation (hair). -/
def ballHair (r : A → B) (h : A → C) : A → B × C := fun x => (r x, h x)

@[simp] theorem ballHair_apply (r : A → B) (h : A → C) (x : A) :
    ballHair r h x = (r x, h x) := rfl

/-- The ball–hair return identifies exactly the occurrences with equal ball *and* equal hair. -/
theorem ballHair_eq_iff (r : A → B) (h : A → C) (x y : A) :
    ballHair r h x = ballHair r h y ↔ (r x = r y ∧ h x = h y) := by
  simp [ballHair, Prod.ext_iff]

theorem ballHair_refines_ball (r : A → B) (h : A → C) {x y : A}
    (hxy : ballHair r h x = ballHair r h y) : r x = r y := ((ballHair_eq_iff r h x y).1 hxy).1

theorem ballHair_refines_hair (r : A → B) (h : A → C) {x y : A}
    (hxy : ballHair r h x = ballHair r h y) : h x = h y := ((ballHair_eq_iff r h x y).1 hxy).2

/-- A return is a harness for the ball–hair return exactly when it separates precisely the
ball-and-hair data. -/
theorem ballHair_harness_iff (r : A → B) (h : A → C) (k : A → K) :
    Harness k (ballHair r h) ↔ ∀ x y, k x = k y ↔ (r x = r y ∧ h x = h y) := by
  constructor
  · intro hk x y; exact (hk x y).trans (ballHair_eq_iff r h x y)
  · intro hk x y; exact (hk x y).trans (ballHair_eq_iff r h x y).symm

/-- **Universal property of the ball–hair return.**  Any evaluation that cannot distinguish two
occurrences of equal ball and equal hair factors through the ball–hair return. -/
theorem ballHair_universal [Nonempty A] (r : A → B) (h : A → C) (g : A → D)
    (hg : ∀ x y, r x = r y → h x = h y → g x = g y) :
    ∃ t : B × C → D, ∀ x, t (ballHair r h x) = g x := by
  classical
  obtain ⟨a₀⟩ := ‹Nonempty A›
  refine ⟨fun p => if hp : ∃ x, ballHair r h x = p then g hp.choose else g a₀, ?_⟩
  intro x
  have hx : ∃ y, ballHair r h y = ballHair r h x := ⟨x, rfl⟩
  show (if hp : ∃ y, ballHair r h y = ballHair r h x then g hp.choose else g a₀) = g x
  rw [dif_pos hx]
  have hc := hx.choose_spec
  exact hg _ _ (ballHair_refines_ball r h hc) (ballHair_refines_hair r h hc)

/-- Two returns that both realise the relative closure are related by a *unique* bijective
translation: **the relative closure defines the ball–hair return**, and the return origin of that
definition is the further translation. -/
theorem ball_hair_return_unique_up_to_translation {r : A → B} {h : A → C}
    {k : A → K} {k' : A → K'} (hk : Surjective k) (hk' : Surjective k')
    (h₁ : Harness k (ballHair r h)) (h₂ : Harness k' (ballHair r h)) :
    ∃! t : K → K', Bijective t ∧ ∀ x, t (k x) = k' x := by
  have hkk' : Harness k k' := harness_trans h₁ (harness_symm h₂)
  obtain ⟨t, ht, huniq⟩ := harness_translation_existsUnique hk hkk'
  refine ⟨t, ⟨⟨harness_translation_injective hk hkk' ht, ?_⟩, ht⟩, ?_⟩
  · intro b
    obtain ⟨x, rfl⟩ := hk' b
    exact ⟨k x, ht x⟩
  · rintro s ⟨-, hs⟩
    exact huniq s hs

/-! ## §3  Light and dark: the mirror is exactly the hair -/

/-- A based path together with its traversal sense: `false` = dark, `true` = light. -/
abbrev PathSense (B : Type*) : Type _ := B × Bool

/-- The mirror involution: same path, reversed light/dark sense. -/
def mirrorFlip (p : PathSense B) : PathSense B := (p.1, !p.2)

theorem mirrorFlip_involutive (p : PathSense B) : mirrorFlip (mirrorFlip p) = p := by
  simp [mirrorFlip]

/-- The ball return (the path alone) does not see the mirror. -/
theorem ball_mirror_invariant (p : PathSense B) : (mirrorFlip p).1 = p.1 := rfl

/-- The hair (the light/dark sense) is exactly what the mirror moves. -/
theorem hair_mirror_flips (p : PathSense B) : (mirrorFlip p).2 = !p.2 := rfl

/-- The ball–hair return does see the mirror. -/
theorem ballHair_mirror_not_invariant (p : PathSense B) :
    ballHair Prod.fst Prod.snd (mirrorFlip p) ≠ ballHair Prod.fst Prod.snd p := by
  simp [ballHair, mirrorFlip, Prod.ext_iff]

/-- A mirror pair is invisible to the ball return alone. -/
theorem mirror_pair_ball_indistinguishable (p : PathSense B) :
    (Prod.fst (mirrorFlip p) : B) = Prod.fst p := rfl

/-- On `PathSense B` the ball–hair return is a harness for the identity reading: the pair
(path, light/dark) is the whole occurrence, nothing further is admitted. -/
theorem ballHair_pathSense_harness_id :
    Harness (ballHair (Prod.fst : PathSense B → B) Prod.snd) (id : PathSense B → PathSense B) := by
  intro x y
  simp [ballHair, Prod.ext_iff]

/-! ## §4  Strictly stronger than the unistochastic absolute value -/

section Unistochastic

variable {n : ℕ}

/-- The unistochastic reading of a matrix: entrywise squared absolute value. -/
noncomputable def unistoch (U : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ‖U i j‖ ^ 2

/-- The **ball** of a matrix: entrywise modulus (the partition datum). -/
noncomputable def ballM (U : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ‖U i j‖

/-- The **hair** of a matrix: the entrywise phase (unitary curvature), with the convention `1` at a
vanishing entry. -/
noncomputable def hairM (U : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if U i j = 0 then 1 else U i j / (‖U i j‖ : ℂ)

/-- **The ball–hair return is the matrix.**  Modulus times phase reconstructs every entry. -/
theorem ball_hair_reconstruct (U : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (ballM U i j : ℂ) * hairM U i j = U i j := by
  unfold ballM hairM
  by_cases h : U i j = 0
  · simp [h]
  · rw [if_neg h]
    have hne : (‖U i j‖ : ℂ) ≠ 0 := by
      simpa using (norm_ne_zero_iff.mpr h)
    field_simp

/-- The ball–hair return is injective: it loses nothing. -/
theorem ballHairM_injective {U V : Matrix (Fin n) (Fin n) ℂ}
    (hb : ballM U = ballM V) (hh : hairM U = hairM V) : U = V := by
  ext i j
  rw [← ball_hair_reconstruct U i j, ← ball_hair_reconstruct V i j,
    congrFun (congrFun hb i) j, congrFun (congrFun hh i) j]

/-- The unistochastic reading factors through the ball alone — it is an absolute value, and the
hair is discarded. -/
theorem unistoch_eq_ballM_sq (U : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    unistoch U i j = ballM U i j ^ 2 := rfl

/-- What the unistochastic reading does retain: for `Uᴴ * U = 1` its columns sum to `1`. -/
theorem unistoch_col_sum {U : Matrix (Fin n) (Fin n) ℂ} (hU : Uᴴ * U = 1) (j : Fin n) :
    ∑ i, unistoch U i j = 1 := by
  have h := congrFun (congrFun hU j) j
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  have hcast : ((∑ i, unistoch U i j : ℝ) : ℂ) = (1 : ℂ) := by
    push_cast
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    show ((unistoch U i j : ℝ) : ℂ) = Uᴴ j i * U i j
    rw [unistoch, Matrix.conjTranspose_apply, Complex.star_def, mul_comm, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
  exact_mod_cast hcast

/-- **Phase gauge invariance of the unistochastic reading.**  Multiplying by a diagonal unitary
changes nothing that `unistoch` can see. -/
theorem unistoch_diagonal_gauge (U : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ)
    (hd : ∀ i, ‖d i‖ = 1) : unistoch (Matrix.diagonal d * U) = unistoch U := by
  funext i j
  simp [unistoch, Matrix.diagonal_mul, hd i]

end Unistochastic

/-- Two genuinely different unitaries with the same unistochastic matrix: the absolute value is not
injective. -/
theorem unistoch_not_injective :
    ∃ U V : Matrix (Fin 1) (Fin 1) ℂ, Uᴴ * U = 1 ∧ Vᴴ * V = 1 ∧
      unistoch U = unistoch V ∧ U ≠ V := by
  refine ⟨1, -1, by simp, by simp, ?_, ?_⟩
  · funext i j
    fin_cases i; fin_cases j; simp [unistoch]
  · intro h
    have := congrFun (congrFun h 0) 0
    simp at this
    norm_num at this

/-- The hair is exactly the gauge datum the unistochastic reading throws away. -/
theorem hairM_detects_gauge :
    ∃ U V : Matrix (Fin 1) (Fin 1) ℂ, unistoch U = unistoch V ∧ hairM U ≠ hairM V := by
  refine ⟨1, -1, ?_, ?_⟩
  · funext i j
    fin_cases i; fin_cases j; simp [unistoch]
  · intro h
    have := congrFun (congrFun h 0) 0
    simp [hairM] at this
    norm_num at this

/-- **Closure is strictly stronger than unistochasticity.**  The ball–hair closure is injective —
it translates the whole relation, phase included — whereas the unistochastic absolute value
conflates unitaries that differ by a phase.  This is the precise sense in which the translational
closure is not an absolute value. -/
theorem closure_strictly_stronger_than_unistochastic :
    (∀ (n : ℕ) (U V : Matrix (Fin n) (Fin n) ℂ), ballM U = ballM V → hairM U = hairM V → U = V) ∧
    (∃ U V : Matrix (Fin 1) (Fin 1) ℂ, Uᴴ * U = 1 ∧ Vᴴ * V = 1 ∧
      unistoch U = unistoch V ∧ U ≠ V) :=
  ⟨fun _ _ _ hb hh => ballHairM_injective hb hh, unistoch_not_injective⟩

/-! ## §5  The whole statement in one theorem -/

/-- **NRRF709.**  For a surjective physical return `k` whose closure is the relative ball–hair
closure of `(r, h)`, and any digital evaluation `e` inducing the same partition:

1. there is exactly one translation carrying the physical return to the digital evaluation, and it
   is injective — the two are *one optomechanical harness*, equally interpretable in both
   directions;
2. that partition is exactly "equal ball and equal hair" — the relative closure defines the
   ball–hair return;
3. the closure so defined is strictly stronger than the unistochastic absolute value. -/
theorem nrrf709_translational_closure_is_the_ball_hair_harness
    {r : A → B} {h : A → C} {k : A → K} {e : A → D}
    (hk : Surjective k) (hclosure : Harness k (ballHair r h)) (he : Harness k e) :
    (∃! t : K → D, ∀ x, t (k x) = e x) ∧
    (∀ t : K → D, (∀ x, t (k x) = e x) → Injective t) ∧
    (∀ x y, k x = k y ↔ (r x = r y ∧ h x = h y)) ∧
    ((∀ (n : ℕ) (U V : Matrix (Fin n) (Fin n) ℂ),
        ballM U = ballM V → hairM U = hairM V → U = V) ∧
      (∃ U V : Matrix (Fin 1) (Fin 1) ℂ, Uᴴ * U = 1 ∧ Vᴴ * V = 1 ∧
        unistoch U = unistoch V ∧ U ≠ V)) :=
  ⟨harness_translation_existsUnique hk he,
   fun _ ht => harness_translation_injective hk he ht,
   (ballHair_harness_iff r h k).1 hclosure,
   closure_strictly_stronger_than_unistochastic⟩

/-! ## Axiom audit -/

#print axioms harness_translation_existsUnique
#print axioms harness_iff_injective_translation
#print axioms harness_adm_eq
#print axioms ballHair_universal
#print axioms ball_hair_return_unique_up_to_translation
#print axioms ballHair_mirror_not_invariant
#print axioms ball_hair_reconstruct
#print axioms unistoch_col_sum
#print axioms unistoch_diagonal_gauge
#print axioms closure_strictly_stronger_than_unistochastic
#print axioms nrrf709_translational_closure_is_the_ball_hair_harness

end NRRF709
