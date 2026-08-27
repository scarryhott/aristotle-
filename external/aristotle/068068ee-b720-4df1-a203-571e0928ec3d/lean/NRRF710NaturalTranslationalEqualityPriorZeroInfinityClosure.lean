import Mathlib
import NRRF708EllipseReturnCantorSquareConjugacyDiosiPenroseSeparation
import NRRF709TranslationalClosureHarnessBallHairUnistochasticStrictness

/-!
# NRRF710 — Natural translational equality: the prior `0 ↔ ∞` closure, no absolute relative
contact, and NRRF708 as a boundary theorem

The target of this module is **not** computational universality.  It is *natural translational
equality*:

> different presentations of one relation ⟶ one returned identity, without reduction to one
> language.

## §1  Natural translational equality

For return maps `rA : A → RA`, `rB : B → RB` and Closure maps `qA : RA → Om`, `qB : RB → Om`, a
translation `T : A → B` is a **natural translational equality** when the square commutes:
`NatEq rA qA rB qB T : ∀ x, qB (rB (T x)) = qA (rA x)`.

It is reflexive (`natEq_id`), composes (`natEq_comp`), and inverts along a bijective translation
(`natEq_symm_of_bijective`).  The reason the translation must be **frozen before the held-out
return is measured** is proved, not assumed: `posthoc_translation_always_exists` shows that if the
translation may be chosen after the fact, a commuting square always exists (so the test is empty),
while `frozen_translation_can_fail` shows that for a translation fixed in advance the condition is
a real constraint.

## §2  The Black Mirror return hierarchy `r₂ ≻ r₁ ≻ r₀`

On the ordered weave `W = (+,-,+,+,-,-,+)` (`blackMirrorWeave : List Bool`):

* `r0` — total return (final intensity), `r1` — coarse class hair `(4+, 3-)`, `r2` — the ordered
  weave itself.
* `r1_refines_r0`, `r2_refines_r1` and the two strictness witnesses
  (`r0_not_refines_r1`, `r1_not_refines_r2`) give `r2 ≻ r1 ≻ r0` (`return_hierarchy_strict`).
* The **relative ball encoding** `relBall W = (r0 W, r0 ⁻¹' {r0 W}, r2 W)` satisfies the ball–hair
  equality `hairEval_eq_relBall` in the exact NRRF709 sense (`NRRF709.Harness`).
* `brightness_does_not_determine_closure` : `r0 W = r0 W'` and even `r1 W = r1 W'` with
  `r2 W ≠ r2 W'` — bright = 1 does not imply Closure.

## §3  The physical–digital commuting harness

Stagewise conjugators `M_i^D = K_i M_i^P K_{i-1}⁻¹` telescope
(`partialHolonomy_telescope`), so for a closed path (`K_n = K_0`) the final ordered holonomies are
conjugate (`holonomy_isConj_of_closed_path`) and every gauge-invariant reading of them agrees
(`holonomy_class_eq_of_closed_path`, `holonomy_natEq_of_closed_path`).  The physical and digital
matrices need not be literally identical.

## §4  The Closure verdict and the five cases

`dC` is the gauge infimum `⨅_{g ∈ G} d(τ_P, ρ_g τ_D)` over a finite admitted presentation group,
and `verdict eps d` is `TRUE / APPROXIMATE / FALSE`.  `dC_eq_zero_iff` proves that `d_C = 0` is
exactly gauge equivalence of the enriched returns.  The five reported cases are then re-run as
theorems on a concrete return type `Weave × ℝ` (`case1_exact`, `case2_admissible_gauge`,
`case3_reordered_weave`, `case4_crossing_changed`, `case5_small_phase_error`).

## §5  Three levels: natural equality, conjugacy, universality

`dynReturn_natural_iff_semiconj` shows an orbit-valued return is natural exactly when the
translation is a semiconjugacy — so *dynamical conjugacy is the level above natural equality*.
`NRRF708`'s obstruction is imported as a **boundary theorem**: a rigid rotation return admits no
natural orbit translation from the Baker shift (`rigid_rotation_no_natural_orbit_translation`),
while a return that forgets orbit structure identifies everything
(`coarse_return_natEq_trivial`).  Hence `levels_strictly_ordered`: the formalism does not erase
universality — a return lacking orbit structure does.

## §6  The `0 ↔ ∞` reciprocal chart

Inversion conjugates dilation by `a` into dilation by `a⁻¹` (`inversion_conj_dilation`), so the two
dilations are naturally translationally equal.  On `ℝ≥0∞` the reciprocal relation is an equivalence
(`recipSetoid`) whose class identifies `0` and `∞` (`zero_closureClass_eq_top`) although they are
*relatively* distinct (`zero_ne_top_absolutely`): `[0]_C = [∞]_C` while `0 ≠ ∞`.

## §6b  Diósi–Penrose as a separation test

`parameter_rate_cannot_separate` and `closure_rate_separating_is_path_dependent` make the bridge
condition exact: a rate factoring through masses, separations, durations and environmental controls
predicts the *same* value for two protocols with identical parameters, so a Closure-specific rate
that separates them cannot factor through that parameter return — it must be path dependent.
`separating_protocol_pair_exists` supplies the required pair of protocols with equal coarse hair and
different ordered return.

## §7  Admission factors through return; isolations are local admissions

`admission_factorsThrough_iff` and `same_return_indistinguishable` make precise that once two forms
have the same return, no admissible judgment at that resolution separates them, and
`isolations_are_local_admissions` exhibits materially distinct presentations with one returned
identity.
-/

namespace NRRF710

open Function

/-! ## §1  Natural translational equality -/

section NatEq

variable {A B C RA RB RC Om : Type*}

/-- **Natural translational equality.**  The translation `T : A → B` carries the returned Closure
class of `A` to the returned Closure class of `B`: the square of returns and Closure maps
commutes. -/
def NatEq (rA : A → RA) (qA : RA → Om) (rB : B → RB) (qB : RB → Om) (T : A → B) : Prop :=
  ∀ x, qB (rB (T x)) = qA (rA x)

/-- A presentation is naturally equal to itself under the identity translation. -/
theorem natEq_id (rA : A → RA) (qA : RA → Om) : NatEq rA qA rA qA id := fun _ => rfl

/-- Natural translational equalities compose. -/
theorem natEq_comp {rA : A → RA} {qA : RA → Om} {rB : B → RB} {qB : RB → Om}
    {rC : C → RC} {qC : RC → Om} {T : A → B} {S : B → C}
    (h₁ : NatEq rA qA rB qB T) (h₂ : NatEq rB qB rC qC S) : NatEq rA qA rC qC (S ∘ T) :=
  fun x => (h₂ (T x)).trans (h₁ x)

/-- Along a bijective translation, natural equality is symmetric. -/
theorem natEq_symm_of_bijective {rA : A → RA} {qA : RA → Om} {rB : B → RB} {qB : RB → Om}
    {T : A → B} (hT : Bijective T) (h : NatEq rA qA rB qB T) :
    NatEq rB qB rA qA (surjInv hT.2) := by
  intro b
  have := h (surjInv hT.2 b)
  rw [surjInv_eq hT.2 b] at this
  exact this.symm

/-- Natural equality is exactly equality of the two returned Closure classes, pointwise. -/
theorem natEq_iff_returned_classes_agree (rA : A → RA) (qA : RA → Om) (rB : B → RB)
    (qB : RB → Om) (T : A → B) :
    NatEq rA qA rB qB T ↔ ∀ x, (qA ∘ rA) x = (qB ∘ rB) (T x) :=
  ⟨fun h x => (h x).symm, fun h x => (h x).symm⟩

/-- **Why the translation must be frozen.**  If the translation may be chosen *after* the returns
are known, then — whenever the digital side can realise every physical Closure class — a commuting
square always exists.  A post-hoc square therefore tests nothing. -/
theorem posthoc_translation_always_exists (rA : A → RA) (qA : RA → Om) (rB : B → RB)
    (qB : RB → Om) (hcov : ∀ x : A, ∃ b : B, qB (rB b) = qA (rA x)) :
    ∃ T : A → B, NatEq rA qA rB qB T := by
  classical
  exact ⟨fun x => (hcov x).choose, fun x => (hcov x).choose_spec⟩

/-- The same statement under a surjective digital Closure reading. -/
theorem posthoc_translation_of_surjective (rA : A → RA) (qA : RA → Om) (rB : B → RB)
    (qB : RB → Om) (hsurj : Surjective (qB ∘ rB)) : ∃ T : A → B, NatEq rA qA rB qB T :=
  posthoc_translation_always_exists rA qA rB qB fun x => hsurj (qA (rA x))

/-- **A frozen translation is a real constraint.**  There are presentations and a translation fixed
in advance for which the Closure square does not commute. -/
theorem frozen_translation_can_fail :
    ∃ (rA : Bool → Bool) (qA : Bool → Bool) (rB : Bool → Bool) (qB : Bool → Bool) (T : Bool → Bool),
      ¬ NatEq rA qA rB qB T := by
  refine ⟨id, id, id, id, not, ?_⟩
  intro h
  exact Bool.noConfusion (h true)

end NatEq

/-! ## §2  The Black Mirror return object: `r₂ ≻ r₁ ≻ r₀` -/

/-- An ordered weave: `true = +`, `false = -`. -/
abbrev Weave : Type := List Bool

/-- The ordered weave `W = (+,-,+,+,-,-,+)`. -/
def blackMirrorWeave : Weave := [true, false, true, true, false, false, true]

/-- `r₀` — the weak return: final intensity / total return. -/
def r0 (W : Weave) : ℤ := (W.count true : ℤ) - (W.count false : ℤ)

/-- `r₁` — the coarse class hair `(#+, #-)`. -/
def r1 (W : Weave) : ℕ × ℕ := (W.count true, W.count false)

/-- `r₂` — the enriched return: the ordered weave itself (with all its based partial returns). -/
def r2 (W : Weave) : Weave := W

/-- The based partial-return hair `H_k = M_k ⋯ M_1`, here the list of initial segments of the
weave: the ordered data that `r₀` and `r₁` discard. -/
def hairSegments (W : Weave) : List Weave := (List.range (W.length + 1)).map (fun k => W.take k)

/-- One reading refines another when it separates at least as much. -/
def Refines {X Y Z : Type*} (f : X → Y) (g : X → Z) : Prop := ∀ x y, f x = f y → g x = g y

theorem r1_refines_r0 : Refines r1 r0 := by
  intro W V h
  have h1 : W.count true = V.count true := congrArg Prod.fst h
  have h2 : W.count false = V.count false := congrArg Prod.snd h
  simp [r0, h1, h2]

theorem r2_refines_r1 : Refines r2 r1 := by
  intro W V h
  simpa [r1] using congrArg r1 (show W = V from h)

theorem r2_refines_hairSegments : Refines r2 hairSegments := by
  intro W V h
  exact congrArg hairSegments (show W = V from h)

/-- The reordered weave: the same partition, a different order. -/
def reorderedWeave : Weave := [true, false, false, true, true, false, true]

/-- One crossing changed: the last `+` becomes a `-`. -/
def changedWeave : Weave := [true, false, true, true, false, false, false]

theorem reordered_same_r0 : r0 blackMirrorWeave = r0 reorderedWeave := by decide

theorem reordered_same_r1 : r1 blackMirrorWeave = r1 reorderedWeave := by decide

theorem reordered_differs_r2 : r2 blackMirrorWeave ≠ r2 reorderedWeave := by decide

theorem changed_differs_r1 : r1 blackMirrorWeave ≠ r1 changedWeave := by decide

/-- `r₀` does not refine `r₁`: total return is strictly weaker than the class hair — a balanced
weave and the empty weave have the same total return but different class hair. -/
theorem r0_not_refines_r1 : ¬ Refines r0 r1 := by
  intro h
  have : r1 [true, false] = r1 [] := h [true, false] [] (by decide)
  exact absurd this (by decide)

/-- `r₁` does not refine `r₂`: the class hair is strictly weaker than the ordered return. -/
theorem r1_not_refines_r2 : ¬ Refines r1 r2 := by
  intro h
  exact reordered_differs_r2 (h blackMirrorWeave reorderedWeave reordered_same_r1)

/-- **`r₂ ≻ r₁ ≻ r₀`, strictly.** -/
theorem return_hierarchy_strict :
    Refines r2 r1 ∧ Refines r1 r0 ∧ ¬ Refines r1 r2 ∧ ¬ Refines r0 r1 :=
  ⟨r2_refines_r1, r1_refines_r0, r1_not_refines_r2, r0_not_refines_r1⟩

/-- **The relative ball encoding**: not the isolated final ball, but the final ball together with
its whole fibre and the enriched return sitting in that fibre. -/
def relBall (W : Weave) : ℤ × Set Weave × Weave := (r0 W, r0 ⁻¹' {r0 W}, r2 W)

/-- The hair evaluation is the enriched return. -/
def hairEval (W : Weave) : Weave := r2 W

/-- **The ball–hair equality** `HairEval(W) =_C relBall(W)`, in the exact NRRF709 sense: the two
readings induce one and the same partition of weaves. -/
theorem hairEval_eq_relBall : NRRF709.Harness hairEval relBall := by
  intro W V
  constructor
  · intro h
    have hWV : W = V := h
    rw [hWV]
  · intro h
    exact congrArg (fun p => p.2.2) h

/-- **Brightness is one probe-state evaluation, not the Closure verdict.**  Two weaves with the
same total return *and* the same coarse class hair whose enriched returns differ. -/
theorem brightness_does_not_determine_closure :
    ∃ W W' : Weave, r0 W = r0 W' ∧ r1 W = r1 W' ∧ r2 W ≠ r2 W' :=
  ⟨blackMirrorWeave, reorderedWeave, reordered_same_r0, reordered_same_r1, reordered_differs_r2⟩

/-! ## §3  The physical–digital commuting harness: stagewise conjugators telescope -/

section Holonomy

variable {G : Type*} [Group G]

/-- The based partial return `H_k = M_k ⋯ M_1`. -/
def partialHolonomy (M : ℕ → G) : ℕ → G
  | 0 => 1
  | k + 1 => M (k + 1) * partialHolonomy M k

@[simp] theorem partialHolonomy_zero (M : ℕ → G) : partialHolonomy M 0 = 1 := rfl

@[simp] theorem partialHolonomy_succ (M : ℕ → G) (k : ℕ) :
    partialHolonomy M (k + 1) = M (k + 1) * partialHolonomy M k := rfl

/-- **The partial returns telescope.**  If the admissible physical and digital local operations are
related stagewise by `M_i^D = K_i M_i^P K_{i-1}⁻¹`, then `H_k^D = K_k H_k^P K_0⁻¹`. -/
theorem partialHolonomy_telescope {MP MD K : ℕ → G}
    (hstep : ∀ i, MD (i + 1) = K (i + 1) * MP (i + 1) * (K i)⁻¹) (k : ℕ) :
    partialHolonomy MD k = K k * partialHolonomy MP k * (K 0)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [partialHolonomy_succ, ih, hstep k, partialHolonomy_succ]
      group

/-- **For a closed path** (`K_n = K_0`) the final ordered holonomies are conjugate. -/
theorem holonomy_isConj_of_closed_path {MP MD K : ℕ → G} {n : ℕ}
    (hstep : ∀ i, MD (i + 1) = K (i + 1) * MP (i + 1) * (K i)⁻¹) (hclosed : K n = K 0) :
    IsConj (partialHolonomy MP n) (partialHolonomy MD n) := by
  have h := partialHolonomy_telescope hstep n
  rw [hclosed] at h
  rw [isConj_iff]
  exact ⟨K 0, h.symm⟩

/-- Hence every gauge-invariant (conjugation-invariant) reading of the two returns agrees:
`[U_W^D]_C = [U_W^P]_C`. -/
theorem holonomy_class_eq_of_closed_path {Om : Type*} {MP MD K : ℕ → G} {n : ℕ}
    (q : G → Om) (hq : ∀ g u, q (g * u * g⁻¹) = q u)
    (hstep : ∀ i, MD (i + 1) = K (i + 1) * MP (i + 1) * (K i)⁻¹) (hclosed : K n = K 0) :
    q (partialHolonomy MD n) = q (partialHolonomy MP n) := by
  have h := partialHolonomy_telescope hstep n
  rw [hclosed] at h
  rw [h, hq]

/-- The harness statement in the `NatEq` language: with the enriched return `partialHolonomy · n`
and a gauge-invariant Closure map, the physical and digital chains are naturally translationally
equal, even though the matrices need not be literally identical. -/
theorem holonomy_natEq_of_closed_path {Om : Type*} {MP MD K : ℕ → G} {n : ℕ}
    (q : G → Om) (hq : ∀ g u, q (g * u * g⁻¹) = q u)
    (hstep : ∀ i, MD (i + 1) = K (i + 1) * MP (i + 1) * (K i)⁻¹) (hclosed : K n = K 0) :
    NatEq (fun _ : Unit => partialHolonomy MP n) q (fun _ : Unit => partialHolonomy MD n) q
      (id : Unit → Unit) :=
  fun _ => holonomy_class_eq_of_closed_path q hq hstep hclosed

/-- The physical and digital returns really may differ as elements while being naturally equal:
conjugation by a non-central element moves the holonomy but not its class. -/
theorem holonomy_need_not_be_literally_equal :
    ∃ (H : Type) (_ : Group H) (u k : H), k * u * k⁻¹ ≠ u := by
  refine ⟨Equiv.Perm (Fin 3), inferInstance, Equiv.swap 0 1, Equiv.swap 1 2, ?_⟩
  decide

end Holonomy

/-! ## §4  The Closure verdict: gauge distance and the five cases -/

/-- The Closure verdict. -/
inductive Verdict where
  | true_
  | approximate
  | false_
  deriving DecidableEq, Repr

/-- `d_C(X) = inf_{g ∈ G} d(τ_P, ρ_g τ_D)` over a finite admitted presentation group. -/
noncomputable def dC {R Gp : Type*} [Fintype Gp] [Nonempty Gp] (rho : Gp → R → R)
    (d : R → R → ℝ) (tP tD : R) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun g => d tP (rho g tD))

theorem dC_le {R Gp : Type*} [Fintype Gp] [Nonempty Gp] (rho : Gp → R → R) (d : R → R → ℝ)
    (tP tD : R) (g : Gp) : dC rho d tP tD ≤ d tP (rho g tD) :=
  Finset.inf'_le _ (Finset.mem_univ g)

theorem le_dC {R Gp : Type*} [Fintype Gp] [Nonempty Gp] {rho : Gp → R → R} {d : R → R → ℝ}
    {tP tD : R} {c : ℝ} (h : ∀ g, c ≤ d tP (rho g tD)) : c ≤ dC rho d tP tD :=
  Finset.le_inf' _ _ fun g _ => h g

theorem dC_eq {R Gp : Type*} [Fintype Gp] [Nonempty Gp] {rho : Gp → R → R} {d : R → R → ℝ}
    {tP tD : R} {c : ℝ} (g₀ : Gp) (hle : d tP (rho g₀ tD) ≤ c) (hge : ∀ g, c ≤ d tP (rho g tD)) :
    dC rho d tP tD = c :=
  le_antisymm (le_trans (dC_le rho d tP tD g₀) hle) (le_dC hge)

/-- **`d_C = 0` is exactly gauge equivalence of the enriched returns.** -/
theorem dC_eq_zero_iff {R Gp : Type*} [Fintype Gp] [Nonempty Gp] {rho : Gp → R → R}
    {d : R → R → ℝ} (hd : ∀ x y, d x y = 0 ↔ x = y) (hnn : ∀ x y, 0 ≤ d x y) (tP tD : R) :
    dC rho d tP tD = 0 ↔ ∃ g, rho g tD = tP := by
  constructor
  · intro h
    obtain ⟨g, -, hg⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Gp))
      (fun g => d tP (rho g tD))
    refine ⟨g, ?_⟩
    have : d tP (rho g tD) = 0 := by rw [← hg]; exact h
    exact ((hd _ _).1 this).symm
  · rintro ⟨g, hg⟩
    refine le_antisymm ?_ (le_dC fun g => hnn _ _)
    have := dC_le rho d tP tD g
    rwa [hg, (hd tP tP).2 rfl] at this

/-- The verdict function: `TRUE` at distance `0`, `APPROXIMATE` within tolerance, `FALSE` beyond. -/
noncomputable def verdict (eps d : ℝ) : Verdict :=
  if d = 0 then Verdict.true_ else if d ≤ eps then Verdict.approximate else Verdict.false_

theorem verdict_true {eps d : ℝ} (h : d = 0) : verdict eps d = Verdict.true_ := by
  simp [verdict, h]

theorem verdict_approximate {eps d : ℝ} (h0 : d ≠ 0) (h : d ≤ eps) :
    verdict eps d = Verdict.approximate := by simp [verdict, h0, h]

theorem verdict_false {eps d : ℝ} (heps : 0 ≤ eps) (h : eps < d) :
    verdict eps d = Verdict.false_ := by
  have hz : d ≠ 0 := by
    intro hz
    rw [hz] at h
    linarith
  simp [verdict, hz, not_le.mpr h]

section FiveCases

/-- The concrete enriched return: an ordered weave together with a relative phase. -/
abbrev Ret : Type := Weave × ℝ

/-- The admitted presentation group of the toy harness: the trivial re-presentation and the
admissible phase-conjugation (encoding change). -/
abbrev Gauge : Type := Bool

/-- The action of the admitted group on returns: it never touches the ordered topology. -/
def rho : Gauge → Ret → Ret
  | false, t => t
  | true, t => (t.1, -t.2)

/-- The return distance: ordered topologies must agree exactly; phases are compared metrically. -/
noncomputable def dRet (t s : Ret) : ℝ := if t.1 = s.1 then |t.2 - s.2| else 1

theorem dRet_nonneg (t s : Ret) : 0 ≤ dRet t s := by
  unfold dRet; split <;> positivity

theorem dRet_of_eq {t s : Ret} (h : t.1 = s.1) : dRet t s = |t.2 - s.2| := if_pos h

theorem dRet_of_ne {t s : Ret} (h : t.1 ≠ s.1) : dRet t s = 1 := if_neg h

theorem dRet_same_weave (W : Weave) (p q : ℝ) : dRet (W, p) (W, q) = |p - q| := if_pos rfl

theorem dRet_eq_zero_iff (t s : Ret) : dRet t s = 0 ↔ t = s := by
  by_cases h : t.1 = s.1
  · rw [dRet_of_eq h, abs_eq_zero, sub_eq_zero]
    exact ⟨fun h2 => Prod.ext h h2, fun h2 => congrArg Prod.snd h2⟩
  · rw [dRet_of_ne h]
    constructor
    · intro h1; norm_num at h1
    · intro h1; exact absurd (congrArg Prod.fst h1) h

theorem rho_fst (g : Gauge) (t : Ret) : (rho g t).1 = t.1 := by cases g <;> rfl

/-- The tolerance of the toy harness. -/
noncomputable def epsHarness : ℝ := 1 / 10

/-- **Case 1 — exact physical–digital translation:** `r₂^P = r₂^D`, verdict CLOSED. -/
theorem case1_exact (t : Ret) : verdict epsHarness (dC rho dRet t t) = Verdict.true_ :=
  verdict_true ((dC_eq_zero_iff dRet_eq_zero_iff dRet_nonneg t t).2 ⟨false, rfl⟩)

/-- **Case 2 — admissible basis change:** `r₂^D = ρ_g(r₂^P)`, verdict CLOSED. -/
theorem case2_admissible_gauge (W : Weave) (p : ℝ) :
    verdict epsHarness (dC rho dRet (W, p) (W, -p)) = Verdict.true_ := by
  refine verdict_true ((dC_eq_zero_iff dRet_eq_zero_iff dRet_nonneg _ _).2 ⟨true, ?_⟩)
  simp [rho]

/-- **Case 3 — same partition, reordered weave:** `r₁^P = r₁^D` but `r₂^P ≠ r₂^D`, NOT CLOSED. -/
theorem case3_reordered_weave (p : ℝ) :
    verdict epsHarness (dC rho dRet (blackMirrorWeave, p) (reorderedWeave, p))
      = Verdict.false_ := by
  have key : ∀ g : Gauge, dRet (blackMirrorWeave, p) (rho g (reorderedWeave, p)) = 1 := by
    intro g
    refine dRet_of_ne ?_
    rw [rho_fst]
    exact fun h => (by decide : blackMirrorWeave ≠ reorderedWeave) h
  have hd : dC rho dRet (blackMirrorWeave, p) (reorderedWeave, p) = 1 :=
    dC_eq false (le_of_eq (key false)) (fun g => le_of_eq (key g).symm)
  rw [hd]
  exact verdict_false (by norm_num [epsHarness]) (by norm_num [epsHarness])

/-- **Case 4 — one crossing changed:** `r₁^P ≠ r₁^D`, NOT CLOSED. -/
theorem case4_crossing_changed (p : ℝ) :
    verdict epsHarness (dC rho dRet (blackMirrorWeave, p) (changedWeave, p)) = Verdict.false_ := by
  have key : ∀ g : Gauge, dRet (blackMirrorWeave, p) (rho g (changedWeave, p)) = 1 := by
    intro g
    refine dRet_of_ne ?_
    rw [rho_fst]
    exact fun h => (by decide : blackMirrorWeave ≠ changedWeave) h
  have hd : dC rho dRet (blackMirrorWeave, p) (changedWeave, p) = 1 :=
    dC_eq false (le_of_eq (key false)) (fun g => le_of_eq (key g).symm)
  rw [hd]
  exact verdict_false (by norm_num [epsHarness]) (by norm_num [epsHarness])

/-- **Case 5 — small phase error:** the ordered topology agrees but the phases differ slightly,
verdict APPROXIMATE. -/
theorem case5_small_phase_error :
    verdict epsHarness (dC rho dRet (blackMirrorWeave, (1 : ℝ)) (blackMirrorWeave, 1 + 1 / 100))
      = Verdict.approximate := by
  have h0 : dRet (blackMirrorWeave, (1 : ℝ)) (rho false (blackMirrorWeave, 1 + 1 / 100))
      = 1 / 100 := by
    show dRet (blackMirrorWeave, (1 : ℝ)) (blackMirrorWeave, 1 + 1 / 100) = 1 / 100
    rw [dRet_same_weave, show (1 : ℝ) - (1 + 1 / 100) = -(1 / 100) by ring, abs_neg,
      abs_of_nonneg]
    norm_num
  have h1 : dRet (blackMirrorWeave, (1 : ℝ)) (rho true (blackMirrorWeave, 1 + 1 / 100))
      = 2 + 1 / 100 := by
    show dRet (blackMirrorWeave, (1 : ℝ)) (blackMirrorWeave, -(1 + 1 / 100)) = 2 + 1 / 100
    rw [dRet_same_weave, show (1 : ℝ) - -(1 + 1 / 100) = 2 + 1 / 100 by ring,
      abs_of_nonneg]
    norm_num
  have hd : dC rho dRet (blackMirrorWeave, (1 : ℝ)) (blackMirrorWeave, 1 + 1 / 100)
      = 1 / 100 := by
    refine dC_eq false (le_of_eq h0) ?_
    intro g
    cases g with
    | false => rw [h0]
    | true => rw [h1]; norm_num
  rw [hd]
  exact verdict_approximate (by norm_num) (by norm_num [epsHarness])

end FiveCases

/-! ## §5  Three levels: natural equality, dynamical conjugacy, universality -/

section Levels

variable {A B : Type*}

/-- The **dynamical return**: the whole orbit of a point. -/
def dynReturn (f : A → A) (x : A) : ℕ → A := fun n => f^[n] x

/-- **The orbit-valued return is natural exactly when the translation is a semiconjugacy.**
Dynamical conjugacy is therefore the level strictly above natural translational equality. -/
theorem dynReturn_natural_iff_semiconj {f : A → A} {g : B → B} (T : A → B) :
    (∀ x n, g^[n] (T x) = T (f^[n] x)) ↔ (∀ x, g (T x) = T (f x)) := by
  constructor
  · intro h x; simpa using h x 1
  · intro h x n
    induction n generalizing x with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ_apply, h x, ih (f x), Function.iterate_succ_apply]

/-- A conjugacy (indeed any semiconjugacy) yields a natural translational equality of the enriched
orbit returns. -/
theorem semiconj_implies_dynReturn_natEq {f : A → A} {g : B → B} {T : A → B}
    (h : ∀ x, g (T x) = T (f x)) :
    NatEq (dynReturn f) (fun o : ℕ → A => (fun n => T (o n))) (dynReturn g) id T := by
  intro x
  funext n
  exact ((dynReturn_natural_iff_semiconj T).2 h x n)

/-- **A return that forgets orbit structure identifies everything.**  Under a coarse return with a
one-point Closure target, *every* translation is a natural equality — so an admission may identify
a rigid rotation with a symbolic shift.  The formalism does not erase universality; a return
lacking orbit structure does. -/
theorem coarse_return_natEq_trivial (rA : A → A) (rB : B → B) (T : A → B) :
    NatEq rA (fun _ => ()) rB (fun _ => ()) T := fun _ => rfl

/-- **NRRF708 as a boundary theorem.**  A rigid rotation return admits no injective natural orbit
translation from the square-Cantor Baker shift: the enriched dynamical return separates them. -/
theorem rigid_rotation_no_natural_orbit_translation {G : Type*} [AddGroup G] (a : G)
    (h : NRRF708.CantorSquare → G) (hinj : Injective h)
    (hnat : ∀ s n, (fun x => x + a)^[n] (h s) = h (NRRF708.bakerShift^[n] s)) : False := by
  have hstep : ∀ s, h (NRRF708.bakerShift s) = h s + a := by
    intro s
    simpa using (hnat s 1).symm
  exact NRRF708.ellipse_rotation_not_conjugate_to_bakerShift a h hinj hstep

/-- **The three levels are strictly ordered.**  Semiconjugacy (the dynamical level) implies natural
equality of orbit returns; natural equality of *coarse* returns implies nothing dynamical — it holds
for every translation — and in the rigid-rotation/Baker-shift case the dynamical level is
genuinely unavailable. -/
theorem levels_strictly_ordered :
    (∀ {A B : Type} {f : A → A} {g : B → B} {T : A → B}, (∀ x, g (T x) = T (f x)) →
        NatEq (dynReturn f) (fun o : ℕ → A => (fun n => T (o n))) (dynReturn g) id T) ∧
    (∀ {A B : Type} (rA : A → A) (rB : B → B) (T : A → B),
        NatEq rA (fun _ => ()) rB (fun _ => ()) T) ∧
    (∀ {G : Type} [AddGroup G] (a : G) (h : NRRF708.CantorSquare → G), Injective h →
        (∀ s, h (NRRF708.bakerShift s) = h s + a) → False) :=
  ⟨fun h => semiconj_implies_dynReturn_natEq h,
   fun rA rB T => coarse_return_natEq_trivial rA rB T,
   fun a h hinj hstep => NRRF708.ellipse_rotation_not_conjugate_to_bakerShift a h hinj hstep⟩

end Levels

/-! ## §6  The `0 ↔ ∞` reciprocal chart: related by rescaling, not literally identical -/

section ZeroInf

/-- Inversion conjugates dilation by `a` into dilation by `a⁻¹`: a valid reciprocal chart
translation. -/
theorem inversion_conj_dilation (a x : ℝ) : (a * x)⁻¹ = a⁻¹ * x⁻¹ := mul_inv a x

/-- Stated as a natural translational equality: with `I(x) = x⁻¹` as the translation, dilation by
`a` and dilation by `a⁻¹` return the same relation. -/
theorem dilation_natEq_reciprocal (a : ℝ) :
    NatEq (fun x : ℝ => a * x) (id : ℝ → ℝ) (fun y : ℝ => a⁻¹ * y) (fun y : ℝ => y⁻¹)
      (fun x : ℝ => x⁻¹) := by
  intro x
  simp [mul_comm]

/-- The reciprocal relation on `ℝ≥0∞`: `x` and `y` are relatively distinct presentations of one
returned identity when `y = x` or `y = x⁻¹`. -/
def recipRel (x y : ENNReal) : Prop := y = x ∨ y = x⁻¹

theorem recipRel_refl (x : ENNReal) : recipRel x x := Or.inl rfl

theorem recipRel_symm {x y : ENNReal} (h : recipRel x y) : recipRel y x := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (by simp)

theorem recipRel_trans {x y z : ENNReal} (h₁ : recipRel x y) (h₂ : recipRel y z) : recipRel x z := by
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl (by simp)

/-- The reciprocal chart as an equivalence of presentations. -/
def recipSetoid : Setoid ENNReal where
  r := recipRel
  iseqv := ⟨recipRel_refl, recipRel_symm, recipRel_trans⟩

/-- The Closure class of a magnitude under the admitted reciprocal re-presentation. -/
def closureClassZeroInf (x : ENNReal) : Quotient recipSetoid := Quotient.mk recipSetoid x

/-- **`[0]_C = [∞]_C`** — zero and infinity are one returned identity under the admitted reciprocal
re-presentation. -/
theorem zero_closureClass_eq_top :
    closureClassZeroInf 0 = closureClassZeroInf ⊤ :=
  Quotient.sound (Or.inr (by simp))

/-- **`0 ≠ ∞`** — but they remain *relatively* distinct: the reciprocal chart does not make them
arithmetically identical. -/
theorem zero_ne_top_absolutely : (0 : ENNReal) ≠ ⊤ := by simp

/-- The precise statement: relative distinction without absolute separation. -/
theorem zero_inf_relative_not_absolute :
    (0 : ENNReal) ≠ ⊤ ∧ closureClassZeroInf 0 = closureClassZeroInf ⊤ :=
  ⟨zero_ne_top_absolutely, zero_closureClass_eq_top⟩

end ZeroInf

/-! ## §6b  Diósi–Penrose as a separation test: path dependence is the discriminator

NRRF708 already proves the power-law rigidity: two rates agreeing at every separation force equal
amplitude and exponent.  The remaining — and sharper — discriminator is *path dependence*, and it
has an exact logical form. -/

section PathDependence

variable {Proto Par : Type*}

/-- **A parameter-only rate cannot separate two protocols with identical parameters.**  If the
predicted rate factors through masses, separations, durations and environmental controls alone,
then two protocols agreeing on all of them are predicted to decohere identically — whatever their
ordered Closure hair. -/
theorem parameter_rate_cannot_separate (par : Proto → Par) (Gam : Par → ℝ)
    {sA sB : Proto} (h : par sA = par sB) : Gam (par sA) = Gam (par sB) := by
  rw [h]

/-- **Hence a Closure-specific rate that does separate them is necessarily path dependent**: it
cannot factor through the parameter return at all.  This is the precise bridge condition a physical
Closure collapse claim must meet. -/
theorem closure_rate_separating_is_path_dependent (par : Proto → Par) (GamC : Proto → ℝ)
    {sA sB : Proto} (hpar : par sA = par sB) (hsep : GamC sA ≠ GamC sB) :
    ¬ ∃ F : Par → ℝ, ∀ s, GamC s = F (par s) := by
  rintro ⟨F, hF⟩
  exact hsep ((hF sA).trans ((parameter_rate_cannot_separate par F hpar).trans (hF sB).symm))

/-- The two protocols required by such a test exist as soon as the enriched return separates them
while the parameter return does not: exactly the `r₁`-equal, `r₂`-different situation of §2. -/
theorem separating_protocol_pair_exists :
    ∃ sA sB : Weave, r1 sA = r1 sB ∧ r2 sA ≠ r2 sB :=
  ⟨blackMirrorWeave, reorderedWeave, reordered_same_r1, reordered_differs_r2⟩

end PathDependence

/-! ## §7  Admission factors through return; isolations are local admissions -/

section Admission

variable {X R : Type*}

/-- An admission factors through the return when it is the pullback of a relation on returns. -/
def FactorsThrough (r : X → R) (Adm : X → X → Prop) : Prop :=
  ∃ Ahat : R → R → Prop, ∀ x y, Adm x y ↔ Ahat (r x) (r y)

/-- **`A(x,y) ↔ Â(r x, r y)`** is exactly the statement that the admission cannot see anything the
return discards. -/
theorem admission_factorsThrough_iff (r : X → R) (Adm : X → X → Prop) :
    FactorsThrough r Adm ↔
      ∀ x y x' y', r x = r x' → r y = r y' → (Adm x y ↔ Adm x' y') := by
  classical
  constructor
  · rintro ⟨Ahat, hA⟩ x y x' y' hx hy
    rw [hA, hA, hx, hy]
  · intro h
    refine ⟨fun a b => ∃ x y, r x = a ∧ r y = b ∧ Adm x y, fun x y => ?_⟩
    constructor
    · intro hxy; exact ⟨x, y, rfl, rfl, hxy⟩
    · rintro ⟨x', y', hx, hy, hxy⟩
      exact (h x' y' x y hx hy).1 hxy

/-- Once two forms have the same return, no admissible judgment at that resolution distinguishes
them as separate relational identities. -/
theorem same_return_indistinguishable {r : X → R} {Adm : X → X → Prop}
    (hfac : FactorsThrough r Adm) {x y : X} (hxy : r x = r y) (z : X) :
    Adm x z ↔ Adm y z :=
  ((admission_factorsThrough_iff r Adm).1 hfac) x z y z hxy rfl

/-- **Isolations are local admissions of a prior translational Closure relation.**  Materially and
representationally different forms — a physical state and its digital encoding — can be relatively
distinct, `x_sil ≠ x_dig`, while belonging to one admitted relational identity, and then no
return-factoring admission separates them. -/
theorem isolations_are_local_admissions :
    ∃ (X : Type) (R : Type) (r : X → R) (xs xd : X),
      xs ≠ xd ∧ r xs = r xd ∧
        ∀ Adm : X → X → Prop, FactorsThrough r Adm → ∀ z, (Adm xs z ↔ Adm xd z) := by
  refine ⟨Bool, Unit, fun _ => (), false, true, by simp, rfl, ?_⟩
  intro Adm hfac z
  exact same_return_indistinguishable hfac rfl z

end Admission

/-! ## §8  The reunified statement -/

/-- **NRRF710.**  The reunified thesis, as one theorem.

1. Natural translational equality is reflexive, compositional and invertible — one returned
   identity through a translation, with no reduction of either presentation to the other; and the
   translation must be frozen, because a post-hoc translation always makes the square commute.
2. The Black Mirror return hierarchy is strict: `r₂ ≻ r₁ ≻ r₀`, so brightness (a single probe-state
   evaluation) does not determine Closure.
3. The physical–digital chains, related stagewise by conjugators along a closed path, return
   conjugate holonomies, hence equal Closure classes: the matrices need not be literally identical.
4. `d_C = 0` is exactly gauge equivalence of the enriched returns.
5. `[0]_C = [∞]_C` while `0 ≠ ∞`: relative distinction without absolute separation.
6. Admission factors through return, so apparent isolations are local admissions of the prior
   translational relation. -/
theorem nrrf710_natural_translational_equality :
    -- 1. natural equality composes, and a post-hoc translation is vacuous
    (∀ {A B C RA RB RC Om : Type} {rA : A → RA} {qA : RA → Om} {rB : B → RB} {qB : RB → Om}
        {rC : C → RC} {qC : RC → Om} {T : A → B} {S : B → C},
        NatEq rA qA rB qB T → NatEq rB qB rC qC S → NatEq rA qA rC qC (S ∘ T)) ∧
    (∀ {A B RA RB Om : Type} (rA : A → RA) (qA : RA → Om) (rB : B → RB) (qB : RB → Om),
        Surjective (qB ∘ rB) → ∃ T : A → B, NatEq rA qA rB qB T) ∧
    -- 2. the strict return hierarchy and the failure of brightness
    (Refines r2 r1 ∧ Refines r1 r0 ∧ ¬ Refines r1 r2 ∧ ¬ Refines r0 r1) ∧
    (∃ W W' : Weave, r0 W = r0 W' ∧ r1 W = r1 W' ∧ r2 W ≠ r2 W') ∧
    -- 3. the commuting physical–digital harness
    (∀ {G : Type} [Group G] {Om : Type} {MP MD K : ℕ → G} {n : ℕ} (q : G → Om),
        (∀ g u, q (g * u * g⁻¹) = q u) →
        (∀ i, MD (i + 1) = K (i + 1) * MP (i + 1) * (K i)⁻¹) → K n = K 0 →
        q (partialHolonomy MD n) = q (partialHolonomy MP n)) ∧
    -- 4. the Closure verdict
    (∀ {R Gp : Type} [Fintype Gp] [Nonempty Gp] {rho : Gp → R → R} {d : R → R → ℝ},
        (∀ x y, d x y = 0 ↔ x = y) → (∀ x y, 0 ≤ d x y) → ∀ tP tD : R,
          (dC rho d tP tD = 0 ↔ ∃ g, rho g tD = tP)) ∧
    -- 5. the prior `0 ↔ ∞` closure
    ((0 : ENNReal) ≠ ⊤ ∧ closureClassZeroInf 0 = closureClassZeroInf ⊤) ∧
    -- 6. admission factors through return
    (∃ (X : Type) (R : Type) (r : X → R) (xs xd : X),
        xs ≠ xd ∧ r xs = r xd ∧
          ∀ Adm : X → X → Prop, FactorsThrough r Adm → ∀ z, (Adm xs z ↔ Adm xd z)) :=
  ⟨fun h₁ h₂ => natEq_comp h₁ h₂,
   fun rA qA rB qB hs => posthoc_translation_of_surjective rA qA rB qB hs,
   return_hierarchy_strict,
   brightness_does_not_determine_closure,
   fun q hq hstep hclosed => holonomy_class_eq_of_closed_path q hq hstep hclosed,
   fun hd hnn tP tD => dC_eq_zero_iff hd hnn tP tD,
   zero_inf_relative_not_absolute,
   isolations_are_local_admissions⟩

/-! ## Axiom audit -/

#print axioms posthoc_translation_always_exists
#print axioms frozen_translation_can_fail
#print axioms return_hierarchy_strict
#print axioms hairEval_eq_relBall
#print axioms brightness_does_not_determine_closure
#print axioms partialHolonomy_telescope
#print axioms holonomy_isConj_of_closed_path
#print axioms holonomy_class_eq_of_closed_path
#print axioms dC_eq_zero_iff
#print axioms case1_exact
#print axioms case2_admissible_gauge
#print axioms case3_reordered_weave
#print axioms case4_crossing_changed
#print axioms case5_small_phase_error
#print axioms dynReturn_natural_iff_semiconj
#print axioms rigid_rotation_no_natural_orbit_translation
#print axioms levels_strictly_ordered
#print axioms zero_inf_relative_not_absolute
#print axioms closure_rate_separating_is_path_dependent
#print axioms separating_protocol_pair_exists
#print axioms admission_factorsThrough_iff
#print axioms isolations_are_local_admissions
#print axioms nrrf710_natural_translational_equality

end NRRF710
