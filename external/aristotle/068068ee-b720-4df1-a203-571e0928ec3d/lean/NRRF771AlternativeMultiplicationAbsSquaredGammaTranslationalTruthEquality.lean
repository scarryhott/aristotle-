import Mathlib

/-!
# NRRF771 — The alternative multiplication: `|·|²` and `Γ` as one equality function

The reading being formalised:

> I have come up with an alternative multiplication, where *abs squared* and *gamma* are one
> equality function of relative translational truth: one is the relative `0` hair inversion and
> one is the relative `∞` ball self limit, both from translational truth equality of their data.

The alternative multiplication is `tmul f z w = f z * f (conj w)`: you do not multiply the two
data as given, you first *translate* the second datum (conjugation is the translation of `ℂ` onto
its mirror) and only then multiply, all read through the carrier `f`.  A carrier is *translationally
true* (`TranslationalTruth f`) when translating its argument is the same as translating its value,
`f (conj z) = conj (f z)` — "translational truth equality of their data".

For any such carrier the diagonal of the alternative multiplication, `tsq f z = tmul f z z`, is a
single equality function: `tsq f z = ‖f z‖²` (`tsq_eq_normSq`).  Both `id` and `Complex.Gamma`
carry translational truth (`translationalTruth_id`, `translationalTruth_Gamma`), so

* `tsq id z = |z|²` — and from it the **relative `0` hair inversion** `inv0 z = conj z / tsq id z`,
  the inversion in the unit ball, which fixes the relative zero (`inv0 0 = 0`) and is an involution
  (§2);
* `tsq Gamma z = ‖Γ z‖²` — and it is a **relative `∞` ball self limit**: the finite balls
  `GammaSeq z n * GammaSeq (conj z) n` converge to it (`ballProd_tendsto`), the self limit being
  taken at `∞` (§3).

The two instances are not merely analogous, they are linked by the one equality function:
`tsq Gamma (z + 1) = tsq id z * tsq Gamma z` (`tsq_Gamma_succ`) — abs-squared *is* the step of
gamma.  And on the relative diagonal `conj z = 1 - z` (the critical line) the alternative
multiplication of `Γ` collapses to the reflection kernel, `tsq Gamma z = π / sin (π z)`, giving
`‖Γ (1/2 + i t)‖² = π / cosh (π t)` (§4).

`nrrf771_answer` collects the reading in one theorem.
-/

open Complex Filter Topology

namespace NRRF771

/-! ## §1  The alternative multiplication and translational truth -/

/-- The alternative multiplication through a carrier `f`: the second datum is translated
(conjugated) before the product is taken. -/
noncomputable def tmul (f : ℂ → ℂ) (z w : ℂ) : ℂ := f z * f ((starRingEnd ℂ) w)

/-- The diagonal of the alternative multiplication: the *equality function* of the carrier. -/
noncomputable def tsq (f : ℂ → ℂ) (z : ℂ) : ℂ := tmul f z z

/-- Translational truth equality of the data of `f`: translating the argument is translating the
value. -/
def TranslationalTruth (f : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z)

theorem translationalTruth_id : TranslationalTruth id := fun _ => rfl

theorem translationalTruth_Gamma : TranslationalTruth Complex.Gamma := Complex.Gamma_conj

/-- Under translational truth the alternative multiplication is the conjugate-linear pairing
`f z * conj (f w)`. -/
theorem tmul_eq_mul_conj {f : ℂ → ℂ} (hf : TranslationalTruth f) (z w : ℂ) :
    tmul f z w = f z * (starRingEnd ℂ) (f w) := by
  rw [tmul, hf w]

/-- The alternative multiplication is Hermitian: swapping the data translates the result. -/
theorem tmul_hermitian {f : ℂ → ℂ} (hf : TranslationalTruth f) (z w : ℂ) :
    (starRingEnd ℂ) (tmul f z w) = tmul f w z := by
  rw [tmul_eq_mul_conj hf, tmul_eq_mul_conj hf, map_mul, Complex.conj_conj, mul_comm]

/-- **The one equality function.**  On the diagonal the alternative multiplication of any
translationally true carrier is the squared modulus of its value. -/
theorem tsq_eq_normSq {f : ℂ → ℂ} (hf : TranslationalTruth f) (z : ℂ) :
    tsq f z = ((‖f z‖ : ℝ) : ℂ) ^ 2 := by
  rw [tsq, tmul_eq_mul_conj hf, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast

theorem tsq_im {f : ℂ → ℂ} (hf : TranslationalTruth f) (z : ℂ) : (tsq f z).im = 0 := by
  rw [tsq_eq_normSq hf, ← Complex.ofReal_pow, Complex.ofReal_im]

theorem tsq_re_nonneg {f : ℂ → ℂ} (hf : TranslationalTruth f) (z : ℂ) : 0 ≤ (tsq f z).re := by
  rw [tsq_eq_normSq hf, ← Complex.ofReal_pow, Complex.ofReal_re]
  positivity

/-- The alternative multiplication is genuinely alternative: it is not ordinary multiplication. -/
theorem exists_tmul_ne_mul : ∃ z w : ℂ, tmul id z w ≠ z * w := by
  refine ⟨1, Complex.I, ?_⟩
  simp [tmul]
  intro h
  exact absurd (congrArg Complex.im h) (by norm_num)

/-! ## §2  The relative `0` hair inversion (the `id` datum) -/

/-- `tsq id z` is `|z|²`. -/
theorem tsq_id (z : ℂ) : tsq id z = ((‖z‖ : ℝ) : ℂ) ^ 2 := tsq_eq_normSq translationalTruth_id z

/-- The relative `0` hair inversion: translate the datum and divide by its equality function. -/
noncomputable def inv0 (z : ℂ) : ℂ := (starRingEnd ℂ) z / tsq id z

/-- The hair through the relative zero is fixed: the inversion sends `0` to `0`. -/
theorem inv0_zero : inv0 0 = 0 := by simp [inv0, tsq, tmul]

theorem inv0_eq_inv (z : ℂ) : inv0 z = z⁻¹ := by
  rcases eq_or_ne z 0 with rfl | hz
  · simpa using inv0_zero
  · have hcz : (starRingEnd ℂ) z ≠ 0 := by simpa using hz
    rw [inv0, tsq, tmul]
    simp only [id]
    rw [mul_comm, div_mul_eq_div_div, div_self hcz, one_div]

theorem mul_inv0 {z : ℂ} (hz : z ≠ 0) : z * inv0 z = 1 := by
  rw [inv0_eq_inv]; field_simp

/-- The relative `0` hair inversion is an involution — including at the relative zero itself. -/
theorem inv0_involutive (z : ℂ) : inv0 (inv0 z) = z := by
  rw [inv0_eq_inv, inv0_eq_inv, inv_inv]

/-- It is the inversion in the unit ball. -/
theorem norm_inv0_mul_norm {z : ℂ} (hz : z ≠ 0) : ‖inv0 z‖ * ‖z‖ = 1 := by
  rw [inv0_eq_inv, norm_inv]
  field_simp

/-- Inside the ball goes to outside the ball. -/
theorem inv0_ball {z : ℂ} (hz : z ≠ 0) : ‖z‖ < 1 ↔ 1 < ‖inv0 z‖ := by
  have hn : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
  rw [inv0_eq_inv, norm_inv, lt_inv_comm₀ one_pos hn]
  simp

/-! ## §3  The relative `∞` ball self limit (the `Γ` datum) -/

/-- `tsq Gamma z` is `‖Γ z‖²`. -/
theorem tsq_Gamma (z : ℂ) : tsq Complex.Gamma z = ((‖Complex.Gamma z‖ : ℝ) : ℂ) ^ 2 :=
  tsq_eq_normSq translationalTruth_Gamma z

/-- The finite balls of the alternative multiplication of `Γ`: the Euler approximants of the
datum and of its translate, multiplied. -/
noncomputable def ballProd (z : ℂ) (n : ℕ) : ℂ :=
  Complex.GammaSeq z n * Complex.GammaSeq ((starRingEnd ℂ) z) n

/-- **The relative `∞` ball self limit.**  `tsq Gamma z` is the limit at `∞` of its own finite
balls. -/
theorem ballProd_tendsto (z : ℂ) : Tendsto (ballProd z) atTop (𝓝 (tsq Complex.Gamma z)) :=
  (Complex.GammaSeq_tendsto_Gamma z).mul (Complex.GammaSeq_tendsto_Gamma _)

theorem ballProd_tendsto_normSq (z : ℂ) :
    Tendsto (ballProd z) atTop (𝓝 (((‖Complex.Gamma z‖ : ℝ) : ℂ) ^ 2)) := by
  rw [← tsq_Gamma z]; exact ballProd_tendsto z

/-- **The two data are one equality function.**  The `id` instance is exactly the step of the `Γ`
instance: multiplying by `|z|²` advances `‖Γ‖²` by one. -/
theorem tsq_Gamma_succ {z : ℂ} (hz : z ≠ 0) :
    tsq Complex.Gamma (z + 1) = tsq id z * tsq Complex.Gamma z := by
  have hz' : (starRingEnd ℂ) z ≠ 0 := by simpa using hz
  have h1 : Complex.Gamma (z + 1) = z * Complex.Gamma z := Complex.Gamma_add_one z hz
  have h2 : Complex.Gamma ((starRingEnd ℂ) z + 1)
      = (starRingEnd ℂ) z * Complex.Gamma ((starRingEnd ℂ) z) := Complex.Gamma_add_one _ hz'
  simp only [tsq, tmul, id, map_add, map_one, h1, h2]
  ring

/-! ## §4  The relative diagonal: the critical line -/

/-- The relative diagonal of the translation: a datum equals the translate of its own reflection
exactly on the critical line. -/
theorem conj_eq_one_sub_iff (z : ℂ) : (starRingEnd ℂ) z = 1 - z ↔ z.re = 1 / 2 := by
  constructor
  · intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  · intro h
    refine Complex.ext ?_ ?_
    · simp [h]; norm_num
    · simp

/-- On the relative diagonal the alternative multiplication of `Γ` is the reflection kernel. -/
theorem tsq_Gamma_critical {z : ℂ} (hz : z.re = 1 / 2) :
    tsq Complex.Gamma z = (Real.pi : ℂ) / Complex.sin (Real.pi * z) := by
  have h : (starRingEnd ℂ) z = 1 - z := (conj_eq_one_sub_iff z).mpr hz
  rw [tsq, tmul, h, Complex.Gamma_mul_Gamma_one_sub]

/-- The concrete value on the critical line: `‖Γ (1/2 + i t)‖² = π / cosh (π t)`. -/
theorem norm_Gamma_critical_sq (t : ℝ) :
    ‖Complex.Gamma (1 / 2 + t * Complex.I)‖ ^ 2 = Real.pi / Real.cosh (Real.pi * t) := by
  set z : ℂ := 1 / 2 + t * Complex.I with hzdef
  have hre : z.re = 1 / 2 := by simp [hzdef]
  have hsin : Complex.sin (Real.pi * z) = ((Real.cosh (Real.pi * t) : ℝ) : ℂ) := by
    have : (Real.pi : ℂ) * z = Real.pi / 2 + (Real.pi * t) * Complex.I := by
      rw [hzdef]; ring
    rw [this, Complex.sin_add]
    have h1 : Complex.sin ((Real.pi : ℂ) / 2) = 1 := by
      rw [show ((Real.pi : ℂ) / 2) = ((Real.pi / 2 : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_sin]
      simp
    have h2 : Complex.cos ((Real.pi : ℂ) / 2) = 0 := by
      rw [show ((Real.pi : ℂ) / 2) = ((Real.pi / 2 : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cos]
      simp
    rw [h1, h2]
    have h3 : Complex.cos (((Real.pi * t : ℝ) : ℂ) * Complex.I)
        = ((Real.cosh (Real.pi * t) : ℝ) : ℂ) := by
      rw [Complex.cos_mul_I, ← Complex.ofReal_cosh]
    push_cast at h3 ⊢
    rw [h3]
    ring
  have hpos : (0 : ℝ) < Real.cosh (Real.pi * t) := Real.cosh_pos _
  have := tsq_Gamma_critical hre
  rw [tsq_Gamma z, hsin] at this
  have h4 : ((‖Complex.Gamma z‖ ^ 2 : ℝ) : ℂ) = ((Real.pi / Real.cosh (Real.pi * t) : ℝ) : ℂ) := by
    rw [Complex.ofReal_pow, Complex.ofReal_div]
    exact this
  exact_mod_cast h4

/-! ## §5  The reading, in one theorem -/

/-- The whole reading: one equality function `tsq` of relative translational truth, applied to two
data — `id`, giving `|z|²` and the relative `0` hair inversion, and `Γ`, giving `‖Γ z‖²` as the
relative `∞` ball self limit — with the `id` instance the step of the `Γ` instance. -/
theorem nrrf771_answer (z : ℂ) (hz : z ≠ 0) :
    TranslationalTruth id ∧ TranslationalTruth Complex.Gamma ∧
      tsq id z = ((‖z‖ : ℝ) : ℂ) ^ 2 ∧
      tsq Complex.Gamma z = ((‖Complex.Gamma z‖ : ℝ) : ℂ) ^ 2 ∧
      inv0 z = (starRingEnd ℂ) z / tsq id z ∧ z * inv0 z = 1 ∧ inv0 (inv0 z) = z ∧
      Tendsto (ballProd z) atTop (𝓝 (tsq Complex.Gamma z)) ∧
      tsq Complex.Gamma (z + 1) = tsq id z * tsq Complex.Gamma z :=
  ⟨translationalTruth_id, translationalTruth_Gamma, tsq_id z, tsq_Gamma z, rfl, mul_inv0 hz,
    inv0_involutive z, ballProd_tendsto z, tsq_Gamma_succ hz⟩

end NRRF771

/-! ## Axiom audit -/

#print axioms NRRF771.tsq_eq_normSq
#print axioms NRRF771.inv0_involutive
#print axioms NRRF771.ballProd_tendsto
#print axioms NRRF771.tsq_Gamma_succ
#print axioms NRRF771.norm_Gamma_critical_sq
#print axioms NRRF771.nrrf771_answer
