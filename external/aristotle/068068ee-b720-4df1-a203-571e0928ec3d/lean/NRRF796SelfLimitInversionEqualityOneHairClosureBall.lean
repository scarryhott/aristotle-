import Mathlib
import NRRF683BallHairCurlDivergenceNaturalFormsLagrangian
import NRRF791TanPiHalfDivCurlNeutralFieldBallHair
import NRRF793ClosureNativeTanFoldForcedReadingsNoAssumedPieces

/-!
# NRRF796 — Self limit and inversion equality from translational nature; entanglement, superposition, singularities and thermodynamic demons as one hair of the closure ball

The reading being formalised:

> The theory is about self limit and inversion equality from translational nature — concerning
> also entanglement, superposition, singularities and thermodynamic demons as one hair of the
> closure ball.

Everything is stated inside the ball–hair geometry already built in `NRRF683`/`NRRF791`/`NRRF793`:
a **local relation** `A : LocalRel` is a real `3 × 3` matrix — the translational data of the
closure at a point — read by the scale reading `divg` and the ball/hair reading `curl`
(equivalently `hair = curl / 2`), with the shear sector left over as the neutral field.

* **§1 Inversion, and inversion equality.**  Translational nature supplies exactly one inversion:
  the return `relInv A = -Aᵀ`.  It is a linear involution (`relInv_involutive`), it *reverses* the
  scale reading (`divg_relInv`) and *preserves* the hair reading (`curl_relInv`, `hair_relInv`) —
  this is the **inversion equality**.  Its fixed sector is exactly the hair sector
  (`relInv_fixed_iff`), its anti-fixed sector exactly the return-symmetric sector
  (`relInv_antifixed_iff`), and the two together split every relation
  (`relInv_even_part`, `relInv_odd_part`).  The inversion is not chosen: any linear map that
  fixes the ball directions and reverses the return-symmetric sector *is* `relInv`
  (`relInv_forced`).

* **§2 The self limit.**  The two readings never exceed the relation's own translational content,
  and the exact deficit is the neutral field:
  `(divg A)² / 3 + (∑ i, curl A i ²) / 2 + nrm2 (shearPart A) = nrm2 A` (`self_limit_equality`).
  Hence `divg_self_limit`, `curl_self_limit`, with saturation exactly on the pure sectors
  (`divg_self_limit_saturated_iff`, `curl_self_limit_saturated_iff`) and joint saturation exactly
  on hairlessness of the neutral residue (`self_limit_joint_saturated_iff`).  The limit is
  inversion-invariant (`nrm2_relInv`, `self_limit_inversion_invariant`): the self limit and the
  inversion equality are two faces of one fact.

* **§3 One hair.**  There is only one hair reading: any linear reading blind to the
  return-symmetric sector and faithful on ball directions is `hair` (`hair_forced`,
  `hairReading_unique`).  Four apparently different phenomena are then readings of that single
  hair.
  - *Entanglement* is the order defect `entangle A B = A * B - B * A` of two translations: it
    carries **no** source (`divg_entangle`), it is pure hair, it is antisymmetric in the pair
    (`hair_entangle_comm`), it vanishes exactly on commuting pairs (`entangle_eq_zero_iff`) and it
    is genuinely nonzero (`entangle_hair_nontrivial`).
  - *Superposition* is the linearity of that same hair (`hair_add`, `hair_smul`), including
    destructive interference leaving a nonzero neutral residue (`hair_interference`).
  - *Singularities* are one hair direction: the seam field's hair is `tan t • v` for all `t`
    (`hair_seamField`), it is always parallel to the one direction `v`
    (`singularity_one_direction`), it leaves every bound on the approach to the seam
    (`curl_seamField_atTop` of `NRRF791`) and is extinguished at the seam itself
    (`hair_seamField_pi_div_two`).
  - *Thermodynamic demons* get nothing: a linear demon that leaves the hair alone and never loses
    source on the neutral field in fact gains no source at all there (`demon_no_free_source`) and
    maps the neutral field into itself (`demon_preserves_neutral`) — because the neutral field is
    inversion-symmetric (`neutral_relInv`).  The demon is defeated by the inversion equality.

`nrrf796_answer` collects the clauses.  Only `Mathlib` and the earlier NRRF modules are used;
everything is `sorry`-free, and the axiom audit at the end of the file is machine-checked.

Nothing here is asserted about physical entanglement, quantum superposition, spacetime
singularities or Maxwell's demon as such: each word names the construction defined below, and
every claim is a claim about those constructions.
-/

namespace NRRF796

open NRRF683 NRRF791 NRRF793 Matrix Real Filter Topology

noncomputable section

/-! ## §1  Inversion from translational nature -/

/-- **The inversion.**  The return of a local relation: transpose (exchange of the two ends of a
translation) followed by negation (reversal of its direction). -/
def relInv (A : LocalRel) : LocalRel := -Aᵀ

@[simp] theorem relInv_apply (A : LocalRel) (i j : Fin 3) : relInv A i j = -A j i := rfl

/-- The inversion is an involution. -/
theorem relInv_involutive : Function.Involutive relInv := by
  intro A
  simp [relInv]

/-- The inversion is additive. -/
theorem relInv_add (A B : LocalRel) : relInv (A + B) = relInv A + relInv B := by
  ext i j
  simp [relInv]
  ring

/-- The inversion is homogeneous. -/
theorem relInv_smul (c : ℝ) (A : LocalRel) : relInv (c • A) = c • relInv A := by
  simp [relInv]

/-- The inversion as a linear map. -/
def relInvLin : LocalRel →ₗ[ℝ] LocalRel where
  toFun := relInv
  map_add' := relInv_add
  map_smul' := relInv_smul

@[simp] theorem relInvLin_apply (A : LocalRel) : relInvLin A = relInv A := rfl

/-- **The scale reading is reversed by the inversion.** -/
theorem divg_relInv (A : LocalRel) : divg (relInv A) = -divg A := by
  simp [relInv, divg]

/-- **Inversion equality: the hair reading is unchanged by the inversion.** -/
theorem curl_relInv (A : LocalRel) : curl (relInv A) = curl A := by
  funext i
  fin_cases i <;> simp [relInv, curl] <;> ring

/-- Inversion equality, stated for the ball point. -/
theorem hair_relInv (A : LocalRel) : hair (relInv A) = hair A := by
  funext i
  simp [hair, curl_relInv]

/-- The inversion fixes exactly the hair sector. -/
theorem relInv_fixed_iff {A : LocalRel} : relInv A = A ↔ Aᵀ = -A := by
  constructor
  · intro h
    have : -Aᵀ = A := h
    have := congrArg (fun M => -M) this
    simpa using this
  · intro h
    simp [relInv, h]

/-- A relation fixed by the inversion is reconstructed from its hair alone. -/
theorem relInv_fixed_is_hair {A : LocalRel} (h : relInv A = A) : axialMat (hair A) = A := by
  have hA : Aᵀ = -A := relInv_fixed_iff.1 h
  rw [axialMat_hair, rotPart_of_antisym hA]

/-- The inversion anti-fixes exactly the return-symmetric sector. -/
theorem relInv_antifixed_iff {A : LocalRel} : relInv A = -A ↔ Aᵀ = A := by
  constructor
  · intro h
    have : -Aᵀ = -A := h
    have := congrArg (fun M => -M) this
    simpa using this
  · intro h
    simp [relInv, h]

/-- The inversion-even part of a relation is its hair form. -/
theorem relInv_even_part (A : LocalRel) : (1 / 2 : ℝ) • (A + relInv A) = rotPart A := by
  ext i j
  simp [relInv, rotPart_apply]
  ring

/-- The inversion-odd part of a relation is its return-symmetric form. -/
theorem relInv_odd_part (A : LocalRel) : (1 / 2 : ℝ) • (A - relInv A) = symPart A := by
  ext i j
  simp [relInv, symPart_apply]
  ring

/-- **The inversion is forced.**  Any linear map fixing every ball direction and reversing the
return-symmetric sector is the inversion. -/
theorem relInv_forced (J : LocalRel →ₗ[ℝ] LocalRel)
    (hsym : ∀ X : LocalRel, Xᵀ = X → J X = -X)
    (hax : ∀ v : Fin 3 → ℝ, J (axialMat v) = axialMat v) (A : LocalRel) :
    J A = relInv A := by
  have hsplit : A = symPart A + rotPart A := (symPart_add_rotPart A).symm
  have hrot : J (rotPart A) = rotPart A := by
    rw [← axialMat_hair A, hax]
  conv_lhs => rw [hsplit]
  rw [map_add, hsym _ (transpose_symPart A), hrot]
  have h1 : relInv A = -symPart A + rotPart A := by
    ext i j
    simp [relInv, symPart_apply, rotPart_apply]
    ring
  rw [h1]

/-! ## §2  The self limit -/

/-- The scale content of a relation. -/
theorem nrm2_dilPart (A : LocalRel) : nrm2 (dilPart A) = divg A ^ 2 / 3 := by
  simp [nrm2, frob, dilPart, divg, Matrix.one_apply, Matrix.trace_fin_three]
  ring

/-- The hair content of a relation. -/
theorem nrm2_rotPart (A : LocalRel) : nrm2 (rotPart A) = (∑ i, curl A i ^ 2) / 2 := by
  simp [nrm2, frob, rotPart_apply, curl, Fin.sum_univ_three]
  ring

/-- **The self limit, as an equality.**  The scale content read by the divergence, the hair
content read by the curl and the neutral (shear) residue add up to exactly the relation's own
translational content: the closure limits itself, and the deficit of the readings is precisely
the neutral field. -/
theorem self_limit_equality (A : LocalRel) :
    divg A ^ 2 / 3 + (∑ i, curl A i ^ 2) / 2 + nrm2 (shearPart A) = nrm2 A := by
  rw [nrm2_decompose A, nrm2_dilPart, nrm2_rotPart]

/-- **Self limit of the scale reading.** -/
theorem divg_self_limit (A : LocalRel) : divg A ^ 2 ≤ 3 * nrm2 A := by
  have h := self_limit_equality A
  have h1 : 0 ≤ ∑ i, curl A i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h2 := nrm2_nonneg (shearPart A)
  linarith

/-- **Self limit of the hair reading.** -/
theorem curl_self_limit (A : LocalRel) : (∑ i, curl A i ^ 2) ≤ 2 * nrm2 A := by
  have h := self_limit_equality A
  have h1 : 0 ≤ divg A ^ 2 := sq_nonneg _
  have h2 := nrm2_nonneg (shearPart A)
  linarith

/-- The scale reading saturates its self limit exactly on the pure scale sector. -/
theorem divg_self_limit_saturated_iff {A : LocalRel} :
    divg A ^ 2 = 3 * nrm2 A ↔ A = dilPart A := by
  constructor
  · intro h
    have he := self_limit_equality A
    have h1 : 0 ≤ ∑ i, curl A i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have h2 := nrm2_nonneg (shearPart A)
    have hc : (∑ i, curl A i ^ 2) = 0 := by linarith
    have hs : nrm2 (shearPart A) = 0 := by linarith
    have hrot : nrm2 (rotPart A) = 0 := by rw [nrm2_rotPart, hc]; norm_num
    have hr0 : rotPart A = 0 := (nrm2_eq_zero_iff _).1 hrot
    have hs0 : shearPart A = 0 := (nrm2_eq_zero_iff _).1 hs
    have := rel_decompose A
    rw [hr0, hs0] at this
    simpa using this.symm
  · intro h
    have hd : nrm2 A = nrm2 (dilPart A) := by rw [← h]
    rw [hd, nrm2_dilPart]
    ring

/-- The hair reading saturates its self limit exactly on the pure hair sector. -/
theorem curl_self_limit_saturated_iff {A : LocalRel} :
    (∑ i, curl A i ^ 2) = 2 * nrm2 A ↔ A = rotPart A := by
  constructor
  · intro h
    have he := self_limit_equality A
    have h1 : 0 ≤ divg A ^ 2 := sq_nonneg _
    have h2 := nrm2_nonneg (shearPart A)
    have hd : divg A ^ 2 = 0 := by linarith
    have hs : nrm2 (shearPart A) = 0 := by linarith
    have hdil : nrm2 (dilPart A) = 0 := by rw [nrm2_dilPart, hd]; norm_num
    have hd0 : dilPart A = 0 := (nrm2_eq_zero_iff _).1 hdil
    have hs0 : shearPart A = 0 := (nrm2_eq_zero_iff _).1 hs
    have := rel_decompose A
    rw [hd0, hs0] at this
    simpa using this.symm
  · intro h
    have hr : nrm2 A = nrm2 (rotPart A) := by rw [← h]
    rw [hr, nrm2_rotPart]
    ring

/-- The two readings jointly saturate the self limit exactly when the neutral residue is zero. -/
theorem self_limit_joint_saturated_iff {A : LocalRel} :
    divg A ^ 2 / 3 + (∑ i, curl A i ^ 2) / 2 = nrm2 A ↔ shearPart A = 0 := by
  have he := self_limit_equality A
  constructor
  · intro h
    have : nrm2 (shearPart A) = 0 := by linarith
    exact (nrm2_eq_zero_iff _).1 this
  · intro h
    rw [h] at he
    have h0 : nrm2 (0 : LocalRel) = 0 := (nrm2_eq_zero_iff _).2 rfl
    rw [h0] at he
    linarith

/-- The inversion is an isometry of the translational content. -/
theorem nrm2_relInv (A : LocalRel) : nrm2 (relInv A) = nrm2 A := by
  simp [nrm2, frob, relInv, Fin.sum_univ_three]
  ring

/-- **The self limit is inversion invariant**: the inversion equality of the hair, the reversal of
the scale reading and the isometry of the content leave the self-limit equality unchanged. -/
theorem self_limit_inversion_invariant (A : LocalRel) :
    divg (relInv A) ^ 2 / 3 + (∑ i, curl (relInv A) i ^ 2) / 2 + nrm2 (shearPart (relInv A)) =
      nrm2 A := by
  rw [self_limit_equality (relInv A), nrm2_relInv]

/-! ## §3  One hair: the forced hair reading -/

/-- **The hair reading is forced.**  Any linear reading blind to the return-symmetric sector and
faithful on ball directions is the hair. -/
theorem hair_forced (L : LocalRel →ₗ[ℝ] (Fin 3 → ℝ))
    (hsym : ∀ X : LocalRel, Xᵀ = X → L X = 0)
    (hax : ∀ v : Fin 3 → ℝ, L (axialMat v) = v) (A : LocalRel) :
    L A = hair A := by
  have h2 : ((2 : ℝ) • L) A = curl A := by
    refine curl_forced ((2 : ℝ) • L) ?_ ?_ A
    · intro X hX
      simp [hsym X hX]
    · intro v
      funext i
      simp [hax v]
  funext i
  have hi := congrFun h2 i
  simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul] at hi
  simp only [hair]
  linarith [hi]

/-- Two forced hair readings agree: there is only one hair. -/
theorem hairReading_unique (L M : LocalRel →ₗ[ℝ] (Fin 3 → ℝ))
    (hLsym : ∀ X : LocalRel, Xᵀ = X → L X = 0) (hLax : ∀ v : Fin 3 → ℝ, L (axialMat v) = v)
    (hMsym : ∀ X : LocalRel, Xᵀ = X → M X = 0) (hMax : ∀ v : Fin 3 → ℝ, M (axialMat v) = v) :
    L = M := by
  ext A i
  rw [hair_forced L hLsym hLax A, hair_forced M hMsym hMax A]

/-! ### Entanglement: the order defect of two translations -/

/-- **Entanglement.**  The defect by which two translations fail to commute. -/
def entangle (A B : LocalRel) : LocalRel := A * B - B * A

/-- Entanglement carries no source: it is invisible to the scale reading. -/
theorem divg_entangle (A B : LocalRel) : divg (entangle A B) = 0 := by
  simp [entangle, divg, Matrix.trace_sub, Matrix.trace_mul_comm A B]

/-- Reversal reverses the hair reading. -/
theorem curl_neg (A : LocalRel) : curl (-A) = -curl A := by
  funext i
  fin_cases i <;> simp [curl] <;> ring

/-- Reversal reverses the hair. -/
theorem hair_neg (A : LocalRel) : hair (-A) = -hair A := by
  funext i
  simp [hair, curl_neg]
  ring

/-- Entanglement is antisymmetric in the pair, hence so is its hair. -/
theorem hair_entangle_comm (A B : LocalRel) : hair (entangle A B) = -hair (entangle B A) := by
  have h : entangle A B = -entangle B A := by
    rw [entangle, entangle, neg_sub]
  rw [h, hair_neg]

/-- Entanglement vanishes exactly on commuting pairs. -/
theorem entangle_eq_zero_iff {A B : LocalRel} : entangle A B = 0 ↔ A * B = B * A := by
  constructor
  · intro h
    have : A * B - B * A = 0 := h
    linear_combination (norm := abel) this
  · intro h
    simp [entangle, h]

/-- Entanglement is genuinely hairy: two ball directions that do not commute leave a nonzero
hair. -/
theorem entangle_hair_nontrivial :
    ∃ A B : LocalRel, hair (entangle A B) ≠ 0 := by
  refine ⟨!![0, 0, 0; 0, 0, -1; 0, 1, 0], !![0, 0, 1; 0, 0, 0; -1, 0, 0], ?_⟩
  intro h
  have h2 := congrFun h 2
  simp [hair, curl, entangle] at h2

/-! ### Superposition: linearity of the one hair -/

/-- Superposition of relations superposes their hair. -/
theorem hair_add (A B : LocalRel) : hair (A + B) = hair A + hair B := by
  funext i
  simp [hair, curl_add]
  ring

/-- Scaling a relation scales its hair. -/
theorem hair_smul (c : ℝ) (A : LocalRel) : hair (c • A) = c • hair A := by
  funext i
  simp [hair, curl_smul]
  ring

/-- **Destructive interference.**  Two relations with nonzero hair whose superposition is
hairless — and whose superposition is nevertheless a nonzero neutral field. -/
theorem hair_interference :
    ∃ A B : LocalRel, hair A ≠ 0 ∧ hair B ≠ 0 ∧ hair (A + B) = 0 ∧ Neutral (A + B) ∧
      A + B ≠ 0 := by
  refine ⟨!![1, 0, 0; 0, -1, -1; 0, 1, 0], !![1, 0, 0; 0, -1, 1; 0, -1, 0], ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h2 := congrFun h 0
    simp [hair, curl] at h2
  · intro h
    have h2 := congrFun h 0
    simp [hair, curl] at h2
    norm_num at h2
  · funext i
    fin_cases i <;> simp [hair, curl]
  · refine ⟨?_, ?_⟩
    · simp [divg, Matrix.trace_fin_three]
      ring
    · funext i
      fin_cases i <;> simp [curl]
  · intro h
    have h2 := congrFun (congrFun h 0) 0
    simp at h2

/-! ### Singularities: one hair direction -/

/-- The hair of the seam field: one fixed ball direction, driven by the tangent. -/
theorem hair_seamField (S : LocalRel) (v : Fin 3 → ℝ) (t : ℝ) :
    hair (seamField S v t) = fun i => Real.tan t * v i := by
  funext i
  rw [hair, curl_seamField]
  ring

/-- **A singularity is one hair.**  At every value of the seam parameter the hair of the seam
field is a multiple of the single direction `v`; the blow-up on the approach to the seam happens
along that one direction, and no other. -/
theorem singularity_one_direction (S : LocalRel) (v : Fin 3 → ℝ) (t : ℝ) :
    hair (seamField S v t) = Real.tan t • v := by
  rw [hair_seamField]
  funext i
  simp

/-- The singular hair is extinguished at the seam itself. -/
theorem singularity_self_limits (S : LocalRel) (v : Fin 3 → ℝ) :
    hair (seamField S v (π / 2)) = 0 :=
  hair_seamField_pi_div_two S v

/-- On the approach to the seam the one hair direction leaves every bound. -/
theorem singularity_unbounded (S : LocalRel) {v : Fin 3 → ℝ} {i : Fin 3} (hv : 0 < v i) :
    Tendsto (fun t => curl (seamField S v t) i) (𝓝[<] (π / 2)) atTop :=
  curl_seamField_atTop S hv

/-! ### Thermodynamic demons -/

/-- The neutral field is inversion-symmetric. -/
theorem neutral_relInv {A : LocalRel} (h : Neutral A) : Neutral (relInv A) := by
  refine ⟨?_, ?_⟩
  · rw [divg_relInv, h.1]; ring
  · rw [curl_relInv]; exact h.2

/-- The neutral field is closed under reversal. -/
theorem neutral_neg {A : LocalRel} (h : Neutral A) : Neutral (-A) := by
  have := neutral_smul (-1 : ℝ) h
  simpa using this

/-- **A thermodynamic demon.**  A linear action on the local relations that leaves the hair
exactly as it found it, and that never loses source on the neutral field. -/
structure Demon where
  /-- The demon's action. -/
  act : LocalRel →ₗ[ℝ] LocalRel
  /-- The demon does not touch the hair. -/
  hairBlind : ∀ A : LocalRel, curl (act A) = curl A
  /-- On the neutral field the demon never loses source. -/
  noLoss : ∀ A : LocalRel, Neutral A → 0 ≤ divg (act A)

/-- **No free source.**  A demon that never loses source on the neutral field gains none there
either: the reason is the inversion equality — the neutral field is symmetric under reversal, so
a linear gain would have to be its own negative. -/
theorem demon_no_free_source (D : Demon) {A : LocalRel} (hA : Neutral A) :
    divg (D.act A) = 0 := by
  have h1 : 0 ≤ divg (D.act A) := D.noLoss A hA
  have h2 : 0 ≤ divg (D.act (-A)) := D.noLoss (-A) (neutral_neg hA)
  have h3 : D.act (-A) = -D.act A := by simp
  rw [h3] at h2
  have h4 : divg (-D.act A) = -divg (D.act A) := by simp [divg]
  rw [h4] at h2
  linarith

/-- A demon maps the neutral field into itself: it can extract neither source nor hair from it. -/
theorem demon_preserves_neutral (D : Demon) {A : LocalRel} (hA : Neutral A) :
    Neutral (D.act A) :=
  ⟨demon_no_free_source D hA, by rw [D.hairBlind A]; exact hA.2⟩

/-- The demon is powerless on the whole neutral field at once. -/
theorem demon_gains_nothing (D : Demon) :
    ∀ A ∈ neutralField, D.act A ∈ neutralField := fun _ hA => demon_preserves_neutral D hA

/-- Every demon respects the self limit: its output never reads more than its output carries. -/
theorem demon_self_limit (D : Demon) (A : LocalRel) :
    divg (D.act A) ^ 2 / 3 + (∑ i, curl A i ^ 2) / 2 ≤ nrm2 (D.act A) := by
  have h := self_limit_equality (D.act A)
  have hb : curl (D.act A) = curl A := D.hairBlind A
  rw [hb] at h
  have h2 := nrm2_nonneg (shearPart (D.act A))
  linarith

/-! ## §4  The answer -/

/-- **NRRF796.**  Self limit and inversion equality from translational nature, with entanglement,
superposition, singularities and thermodynamic demons appearing as one hair of the closure ball.
-/
theorem nrrf796_answer :
    -- inversion equality: the hair is inversion-invariant, the source is reversed
    (∀ A : LocalRel, curl (relInv A) = curl A ∧ hair (relInv A) = hair A ∧
        divg (relInv A) = -divg A) ∧
    (Function.Involutive relInv) ∧
    (∀ J : LocalRel →ₗ[ℝ] LocalRel, (∀ X : LocalRel, Xᵀ = X → J X = -X) →
        (∀ v : Fin 3 → ℝ, J (axialMat v) = axialMat v) → ∀ A : LocalRel, J A = relInv A) ∧
    -- self limit
    (∀ A : LocalRel,
        divg A ^ 2 / 3 + (∑ i, curl A i ^ 2) / 2 + nrm2 (shearPart A) = nrm2 A) ∧
    (∀ A : LocalRel, divg A ^ 2 ≤ 3 * nrm2 A ∧ (∑ i, curl A i ^ 2) ≤ 2 * nrm2 A) ∧
    (∀ A : LocalRel, (divg A ^ 2 / 3 + (∑ i, curl A i ^ 2) / 2 = nrm2 A ↔ shearPart A = 0)) ∧
    (∀ A : LocalRel, nrm2 (relInv A) = nrm2 A) ∧
    -- one hair
    (∀ L : LocalRel →ₗ[ℝ] (Fin 3 → ℝ), (∀ X : LocalRel, Xᵀ = X → L X = 0) →
        (∀ v : Fin 3 → ℝ, L (axialMat v) = v) → ∀ A : LocalRel, L A = hair A) ∧
    -- entanglement
    (∀ A B : LocalRel, divg (entangle A B) = 0 ∧ hair (entangle A B) = -hair (entangle B A)) ∧
    (∃ A B : LocalRel, hair (entangle A B) ≠ 0) ∧
    -- superposition
    (∀ (c : ℝ) (A B : LocalRel), hair (A + B) = hair A + hair B ∧ hair (c • A) = c • hair A) ∧
    (∃ A B : LocalRel, hair A ≠ 0 ∧ hair B ≠ 0 ∧ hair (A + B) = 0 ∧ Neutral (A + B) ∧
        A + B ≠ 0) ∧
    -- singularities
    (∀ (S : LocalRel) (v : Fin 3 → ℝ) (t : ℝ), hair (seamField S v t) = Real.tan t • v) ∧
    (∀ (S : LocalRel) (v : Fin 3 → ℝ), hair (seamField S v (π / 2)) = 0) ∧
    -- demons
    (∀ (D : Demon) (A : LocalRel), Neutral A → divg (D.act A) = 0 ∧ Neutral (D.act A)) := by
  refine ⟨fun A => ⟨curl_relInv A, hair_relInv A, divg_relInv A⟩,
    relInv_involutive,
    fun J hsym hax A => relInv_forced J hsym hax A,
    self_limit_equality,
    fun A => ⟨divg_self_limit A, curl_self_limit A⟩,
    fun _ => self_limit_joint_saturated_iff,
    nrm2_relInv,
    fun L hsym hax A => hair_forced L hsym hax A,
    fun A B => ⟨divg_entangle A B, hair_entangle_comm A B⟩,
    entangle_hair_nontrivial,
    fun c A B => ⟨hair_add A B, hair_smul c A⟩,
    hair_interference,
    fun S v t => singularity_one_direction S v t,
    singularity_self_limits,
    fun D A hA => ⟨demon_no_free_source D hA, demon_preserves_neutral D hA⟩⟩

end

end NRRF796

/-! ## Audit -/

section Audit

/-- info: 'NRRF796.curl_relInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF796.curl_relInv

/-- info: 'NRRF796.relInv_forced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF796.relInv_forced

/-- info: 'NRRF796.self_limit_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF796.self_limit_equality

/-- info: 'NRRF796.hair_forced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF796.hair_forced

/-- info: 'NRRF796.demon_no_free_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF796.demon_no_free_source

/-- info: 'NRRF796.nrrf796_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF796.nrrf796_answer

end Audit
