import Mathlib
import NRRF771AlternativeMultiplicationAbsSquaredGammaTranslationalTruthEquality

/-!
# NRRF772 — Relative equality functions, layout equivalence over `𝔽₂`, and completeness

The reading being formalised:

> Gluon's Linear Layouts give a computational analogue of relative translational truth: two layout
> *descriptions* `L_A ≠ L_B` can denote the same mapping `⟦L_A⟧ = ⟦L_B⟧` of logical tensor data onto
> hardware; there is no canonical representation.  My organisation of translational truth into
> *relative equality functions* (the `|·|²` reading and the `Γ` reading of the self tensor being one
> equality function) asks the same question one level up: not "do two layouts encode the same
> mapping?" but "do two readings of the same datum carry the same information?".  How might that
> organisation approach a *complete* theory?

This file answers with a precise criterion, and tests it on both sides.

* **§1 Layouts.**  Layout *presentations* (`Pres`) are syntax: identity, bit permutations,
  composites, and explicit `𝔽₂` matrices.  `Pres.eval` is the denotation `⟦·⟧`, a linear map on
  bits.  `noCanonicalRepresentation` exhibits three pairwise distinct presentations of the Gluon
  tutorial's `7 × 7` identity (five lane bits, two warp bits) with equal denotation — presentation
  inequality with denotational equality.  `TrivialConv` is Gluon's *zero-cost* conversion (a
  permutation of the register bits only); it is a groupoid (`TrivialConv.refl/symm/trans`) and it
  preserves the logical data (`TrivialConv.range_eq`).

* **§2 Relative equality functions.**  A reading `r : D → V` of data `D` is a relative equality
  function: it declares `d` and `d'` equal when `r d = r d'`.  `Refines r s` says `s` is a
  translation of `r` (`∃ t, t ∘ r = s`), and `TransEq r s` that each is a translation of the other.
  The central lemma `transEq_iff_kernel` says: **two relative equality functions are translationally
  equal exactly when they induce the same equality on the data.**  So "relative equality function",
  taken up to translation, *is* an equivalence relation on the data, nothing more and nothing less.

* **§3 Completeness.**  A family `r : ∀ i, D → V i` is `Complete` when its joint reading is
  injective.  Then:
  `complete_iff_refines_id` — complete ⟺ the identity reading is a translation of the family;
  `complete_iff_all_readings` — complete ⟺ *every* further relative equality function on the data is
  already a translation of the family (nothing new can ever be read off);
  `complete_of_subfamily`, and `quotient_complete` — **every** family is complete about the quotient
  it determines.  Completeness is therefore never absolute: it is the statement that the family's
  joint kernel has been driven down to equality at the level of data one intends.

* **§4 The two tests.**  Over `𝔽₂` the coordinate readings *are* complete (`bits_complete`), and
  dropping a single bit destroys completeness (`bits_drop_one_not_complete`); the basis readings of
  a layout are complete (`layout_basis_complete`) — this is why Gluon's linear-layout algebra can
  decide layout equality at all.  On the other side, no family of `tsq` readings (NRRF771: `|z|²`
  and `‖Γ z‖²` are instances) can be complete on `ℂ`, because every such reading is blind to the
  mirror: `tsq_conj` and `tsq_family_not_complete`.  They are exactly complete one level up, on the
  quotient they determine (`tsq_quotient_complete`, `conj_in_tsq_kernel`).

`nrrf772_answer` collects the answer in one theorem.
-/

open Complex

universe u v w

namespace NRRF772

/-! ## §1  Layout presentations over `𝔽₂` and their denotation -/

/-- The bits of an index: the `𝔽₂`-vector space Gluon's linear layouts act on. -/
abbrev Bits (n : ℕ) := Fin n → ZMod 2

/-- A *linear layout*: an `𝔽₂`-linear map from input bits (register, lane, warp, block) to the bits
of a logical tensor coordinate. -/
abbrev LinLayout (n m : ℕ) := Bits n →ₗ[ZMod 2] Bits m

/-- Layout *descriptions* (syntax).  Distinct descriptions may denote the same layout. -/
inductive Pres : ℕ → ℕ → Type
  | protected id (n : ℕ) : Pres n n
  | perm {n : ℕ} (e : Equiv.Perm (Fin n)) : Pres n n
  | comp {n m k : ℕ} (p : Pres m k) (q : Pres n m) : Pres n k
  | mat {n m : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2)) : Pres n m

/-- The denotation `⟦·⟧` of a layout description: the mapping it actually performs. -/
noncomputable def Pres.eval : {n m : ℕ} → Pres n m → LinLayout n m
  | _, _, .id _ => LinearMap.id
  | _, _, .perm e => LinearMap.funLeft (ZMod 2) (ZMod 2) e
  | _, _, .comp p q => p.eval.comp q.eval
  | _, _, .mat M => Matrix.mulVecLin M

/-- Denotational equivalence of layout descriptions: `⟦p⟧ = ⟦q⟧`. -/
def LayoutEquiv {n m : ℕ} (p q : Pres n m) : Prop := p.eval = q.eval

theorem layoutEquiv_refl {n m : ℕ} (p : Pres n m) : LayoutEquiv p p := rfl

theorem layoutEquiv_symm {n m : ℕ} {p q : Pres n m} (h : LayoutEquiv p q) : LayoutEquiv q p :=
  Eq.symm h

theorem layoutEquiv_trans {n m : ℕ} {p q r : Pres n m} (h : LayoutEquiv p q)
    (h' : LayoutEquiv q r) : LayoutEquiv p r := Eq.trans h h'

/-- The Gluon tutorial's example: the `7 × 7` identity on the bits of a 1-D tensor index. -/
noncomputable def gluonBlocked : Pres 7 7 := Pres.mat 1

/-- The same mapping, described by a round trip through a bit permutation (a "slice"-style
description: relabel the bits and relabel them back). -/
noncomputable def gluonSliced (e : Equiv.Perm (Fin 7)) : Pres 7 7 :=
  Pres.comp (Pres.perm e) (Pres.perm e.symm)

/-- The five lane bits of the example. -/
def laneBit (i : Fin 5) : Fin 7 := ⟨i.val, by omega⟩

/-- The two warp bits of the example. -/
def warpBit (i : Fin 2) : Fin 7 := ⟨i.val + 5, by omega⟩

/-- Five lane bits and two warp bits exhaust the seven input bits. -/
theorem lane_warp_cover (j : Fin 7) : (∃ i, laneBit i = j) ∨ ∃ i, warpBit i = j := by
  rcases j with ⟨v, hv⟩
  by_cases h : v < 5
  · exact Or.inl ⟨⟨v, h⟩, rfl⟩
  · refine Or.inr ⟨⟨v - 5, by omega⟩, ?_⟩
    apply Fin.ext
    simp [warpBit]
    omega

theorem lane_ne_warp (i : Fin 5) (k : Fin 2) : laneBit i ≠ warpBit k := by
  intro h
  have hv := congrArg Fin.val h
  simp [laneBit, warpBit] at hv
  omega

/-- The denotation of the example is the identity on bits: input bit `j` is output bit `j`. -/
theorem gluonBlocked_apply (v : Bits 7) (j : Fin 7) : gluonBlocked.eval v j = v j := by
  simp [gluonBlocked, Pres.eval]

theorem gluonSliced_apply (e : Equiv.Perm (Fin 7)) (v : Bits 7) (j : Fin 7) :
    (gluonSliced e).eval v j = v j := by
  simp [gluonSliced, Pres.eval, LinearMap.funLeft_apply]

/-- **No canonical layout representation.**  Three pairwise distinct descriptions of the Gluon
example denote one and the same mapping. -/
theorem noCanonicalRepresentation (e : Equiv.Perm (Fin 7)) :
    gluonBlocked ≠ Pres.id 7 ∧ gluonBlocked ≠ gluonSliced e ∧ Pres.id 7 ≠ gluonSliced e ∧
      LayoutEquiv gluonBlocked (Pres.id 7) ∧ LayoutEquiv gluonBlocked (gluonSliced e) := by
  refine ⟨by simp [gluonBlocked], by simp [gluonBlocked, gluonSliced], by simp [gluonSliced],
    ?_, ?_⟩
  · exact LinearMap.ext fun v => funext fun j => by
      simpa [Pres.eval] using gluonBlocked_apply v j
  · exact LinearMap.ext fun v => funext fun j => by
      rw [gluonBlocked_apply, gluonSliced_apply]

/-! ### Zero-cost conversions -/

/-- A conversion `p → q` is *trivial* (zero cost, at most a reordering of registers inside a
thread) when it is a permutation of the input bits designated as register bits. -/
def TrivialConv {n m : ℕ} (regs : Finset (Fin n)) (p q : Pres n m) : Prop :=
  ∃ e : Equiv.Perm (Fin n), (∀ i, i ∉ regs → e i = i) ∧
    ∀ v : Bits n, p.eval (fun i => v (e i)) = q.eval v

theorem trivialConv_refl {n m : ℕ} (regs : Finset (Fin n)) (p : Pres n m) :
    TrivialConv regs p p :=
  ⟨Equiv.refl _, fun _ _ => rfl, fun _ => rfl⟩

theorem trivialConv_symm {n m : ℕ} {regs : Finset (Fin n)} {p q : Pres n m}
    (h : TrivialConv regs p q) : TrivialConv regs q p := by
  obtain ⟨e, hfix, heq⟩ := h
  refine ⟨e.symm, fun i hi => e.symm_apply_eq.mpr (hfix i hi).symm, fun v => ?_⟩
  have := heq (fun i => v (e.symm i))
  simpa using this.symm

theorem trivialConv_trans {n m : ℕ} {regs : Finset (Fin n)} {p q r : Pres n m}
    (h : TrivialConv regs p q) (h' : TrivialConv regs q r) : TrivialConv regs p r := by
  obtain ⟨e, hfix, heq⟩ := h
  obtain ⟨e', hfix', heq'⟩ := h'
  refine ⟨e.trans e', fun i hi => by simp [Equiv.trans_apply, hfix i hi, hfix' i hi], fun v => ?_⟩
  have h1 := heq (fun i => v (e' i))
  have h2 := heq' v
  simpa [Equiv.trans_apply] using h1.trans h2

/-- A trivial conversion preserves the logical data: the set of tensor coordinates reached is
unchanged. -/
theorem trivialConv_range_eq {n m : ℕ} {regs : Finset (Fin n)} {p q : Pres n m}
    (h : TrivialConv regs p q) : Set.range q.eval = Set.range p.eval := by
  obtain ⟨e, -, heq⟩ := h
  ext y
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨_, heq v⟩
  · rintro ⟨v, rfl⟩
    refine ⟨fun i => v (e.symm i), ?_⟩
    have := heq (fun i => v (e.symm i))
    simpa using this.symm

/-! ## §2  Relative equality functions and translation between them -/

variable {D : Type u}

/-- `s` is a *translation* of `r`: everything `s` reads is already determined by what `r` reads. -/
def Refines {V : Type v} {W : Type w} (r : D → V) (s : D → W) : Prop :=
  ∃ t : V → W, ∀ d, t (r d) = s d

/-- Two relative equality functions carry the same translational data: each is a translation of the
other. -/
def TransEq {V : Type v} {W : Type w} (r : D → V) (s : D → W) : Prop :=
  Refines r s ∧ Refines s r

theorem Refines.refl {V : Type v} (r : D → V) : Refines r r := ⟨id, fun _ => rfl⟩

theorem Refines.trans {V : Type v} {W : Type w} {X : Type*} {r : D → V} {s : D → W} {u : D → X}
    (h : Refines r s) (h' : Refines s u) : Refines r u := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨t', ht'⟩ := h'
  exact ⟨t' ∘ t, fun d => by simp [ht d, ht' d]⟩

/-- A translation can only coarsen equality: it never distinguishes data its source identifies. -/
theorem Refines.kernel_le {V : Type v} {W : Type w} {r : D → V} {s : D → W} (h : Refines r s)
    {d d' : D} (hd : r d = r d') : s d = s d' := by
  obtain ⟨t, ht⟩ := h
  rw [← ht d, ← ht d', hd]

/-- **Relative equality functions are exactly their induced equalities.**  Given some datum, `s` is
a translation of `r` precisely when `r`'s equality implies `s`'s. -/
theorem refines_iff_kernel {V : Type v} {W : Type w} (r : D → V) (s : D → W) (d₀ : D) :
    Refines r s ↔ ∀ d d', r d = r d' → s d = s d' := by
  classical
  refine ⟨fun h _ _ hd => h.kernel_le hd, fun h => ?_⟩
  refine ⟨fun v => if hv : ∃ d, r d = v then s hv.choose else s d₀, fun d => ?_⟩
  have hv : ∃ d', r d' = r d := ⟨d, rfl⟩
  show (if hv : ∃ d', r d' = r d then s hv.choose else s d₀) = s d
  rw [dif_pos hv]
  exact h _ _ hv.choose_spec

/-- Two relative equality functions are translationally equal exactly when they declare the same
data equal. -/
theorem transEq_iff_kernel {V : Type v} {W : Type w} (r : D → V) (s : D → W) (d₀ : D) :
    TransEq r s ↔ ∀ d d', (r d = r d' ↔ s d = s d') := by
  rw [TransEq, refines_iff_kernel r s d₀, refines_iff_kernel s r d₀]
  constructor
  · rintro ⟨h₁, h₂⟩ d d'
    exact ⟨h₁ d d', h₂ d d'⟩
  · intro h
    exact ⟨fun d d' hd => (h d d').1 hd, fun d d' hd => (h d d').2 hd⟩

theorem TransEq.refl {V : Type v} (r : D → V) : TransEq r r := ⟨Refines.refl r, Refines.refl r⟩

theorem TransEq.symm {V : Type v} {W : Type w} {r : D → V} {s : D → W} (h : TransEq r s) :
    TransEq s r := ⟨h.2, h.1⟩

theorem TransEq.trans {V : Type v} {W : Type w} {X : Type*} {r : D → V} {s : D → W} {u : D → X}
    (h : TransEq r s) (h' : TransEq s u) : TransEq r u :=
  ⟨h.1.trans h'.1, h'.2.trans h.2⟩

/-! ## §3  Completeness of a family of relative equality functions -/

/-- The joint reading of a family of relative equality functions. -/
def joint {ι : Type*} {V : ι → Type v} (r : ∀ i, D → V i) : D → ∀ i, V i := fun d i => r i d

/-- A family of relative equality functions is *complete* for `D` when its joint reading separates
the data: agreement in every relative reading is identity of the datum. -/
def Complete {ι : Type*} {V : ι → Type v} (r : ∀ i, D → V i) : Prop :=
  Function.Injective (joint r)

theorem complete_iff {ι : Type*} {V : ι → Type v} (r : ∀ i, D → V i) :
    Complete r ↔ ∀ d d', (∀ i, r i d = r i d') → d = d' := by
  constructor
  · intro h d d' hd
    exact h (funext hd)
  · intro h d d' hd
    exact h d d' fun i => congrFun hd i

/-- Enlarging a family cannot destroy completeness. -/
theorem complete_of_subfamily {ι κ : Type*} {V : ι → Type v} (r : ∀ i, D → V i) (f : κ → ι)
    (h : Complete fun k => r (f k)) : Complete r := by
  rw [complete_iff] at h ⊢
  exact fun d d' hd => h d d' fun k => hd (f k)

/-- **Completeness is the identity reading being a translation.** -/
theorem complete_iff_refines_id {ι : Type*} {V : ι → Type v} (r : ∀ i, D → V i) (d₀ : D) :
    Complete r ↔ Refines (joint r) (id : D → D) := by
  rw [refines_iff_kernel _ _ d₀]
  constructor
  · intro h d d' hd
    exact h hd
  · intro h d d' hd
    exact h d d' hd

/-- **The completeness criterion.**  A family of relative equality functions is complete exactly
when every further relative equality function on the same data is already a translation of it:
nothing that could ever be read off the data is outside the family's translational reach. -/
theorem complete_iff_all_readings {ι : Type*} {V : ι → Type v} (r : ∀ i, D → V i) (d₀ : D) :
    Complete r ↔ ∀ (W : Type u) (s : D → W), Refines (joint r) s := by
  constructor
  · intro h W s
    rw [refines_iff_kernel _ _ d₀]
    intro d d' hd
    rw [h hd]
  · intro h
    obtain ⟨t, ht⟩ := h D id
    intro d d' hd
    have e1 : t (joint r d) = d := ht d
    have e2 : t (joint r d') = d' := ht d'
    rw [← e1, ← e2, hd]

/-- The equality on data that a family of relative equality functions actually determines. -/
def kerSetoid {ι : Type*} {V : ι → Type v} (r : ∀ i, D → V i) : Setoid D :=
  Setoid.ker (joint r)

theorem kerSetoid_iff {ι : Type*} {V : ι → Type v} (r : ∀ i, D → V i) (d d' : D) :
    (kerSetoid r).r d d' ↔ ∀ i, r i d = r i d' := by
  constructor
  · intro h i; exact congrFun h i
  · intro h; exact funext h

/-- The readings, transported to the level of data they actually determine. -/
def qread {ι : Type*} {V : ι → Type v} (r : ∀ i, D → V i) (i : ι) :
    Quotient (kerSetoid r) → V i :=
  Quotient.lift (r i) fun _ _ h => congrFun h i

/-- **Every family of relative equality functions is complete — about the level of data it
determines.**  Completeness is thus never absolute: it is reached by driving the family's joint
kernel down to the equality one intends. -/
theorem quotient_complete {ι : Type*} {V : ι → Type v} (r : ∀ i, D → V i) :
    Complete (qread r) := by
  rw [complete_iff]
  intro d d' hd
  induction d using Quotient.inductionOn with
  | h a =>
    induction d' using Quotient.inductionOn with
    | h b =>
      exact Quotient.sound (funext fun i => hd i)

/-- The quotient level is the *finest* level at which the family is complete: two data identified by
the family are indistinguishable by any translation of it. -/
theorem indistinguishable_of_kernel {ι : Type*} {V : ι → Type v} {r : ∀ i, D → V i} {W : Type w}
    {s : D → W} (h : Refines (joint r) s) {d d' : D} (hd : ∀ i, r i d = r i d') : s d = s d' :=
  h.kernel_le (funext hd)

/-! ## §4  The two tests: bits over `𝔽₂`, and the `|·|²` / `Γ` readings -/

/-- Over `𝔽₂` the coordinate readings are a complete family of relative equality functions: this is
why layout equality is decidable in the linear-layout algebra. -/
theorem bits_complete (n : ℕ) : Complete (fun (i : Fin n) (v : Bits n) => v i) := by
  rw [complete_iff]
  exact fun _ _ h => funext h

/-- Drop a single bit and completeness fails: a family of relative equality functions is complete
only when it exhausts the data. -/
theorem bits_drop_one_not_complete {n : ℕ} (i₀ : Fin n) :
    ¬ Complete (fun (i : {i : Fin n // i ≠ i₀}) (v : Bits n) => v i.1) := by
  rw [complete_iff]
  intro h
  have := h (fun _ => 0) (Pi.single i₀ 1) (by
    rintro ⟨i, hi⟩
    simp [hi])
  have h0 := congrFun this i₀
  simp at h0

/-- Reading a linear layout on the basis bits is a complete family: layouts are determined by where
each input bit goes. -/
theorem layout_basis_complete (n m : ℕ) :
    Complete (fun (i : Fin n) (L : LinLayout n m) => L (Pi.single i 1)) := by
  rw [complete_iff]
  intro L L' h
  apply (Pi.basisFun (ZMod 2) (Fin n)).ext
  intro i
  simpa using h i

/-- Every `tsq` reading of NRRF771 — in particular `|z|²` and `‖Γ z‖²` — is blind to the mirror. -/
theorem tsq_conj (f : ℂ → ℂ) (z : ℂ) :
    NRRF771.tsq f ((starRingEnd ℂ) z) = NRRF771.tsq f z := by
  simp [NRRF771.tsq, NRRF771.tmul, mul_comm]

/-- The mirror is inside the joint kernel of any family of `tsq` readings. -/
theorem conj_in_tsq_kernel {ι : Type*} (f : ι → ℂ → ℂ) (z : ℂ) (i : ι) :
    (fun i z => NRRF771.tsq (f i) z) i ((starRingEnd ℂ) z) = (fun i z => NRRF771.tsq (f i) z) i z :=
  tsq_conj (f i) z

/-- **No family of `tsq` relative equality functions is complete on `ℂ`.**  The `|·|²` reading and
the `Γ` reading — and any other reading of the self tensor `z ⊗ z` through a carrier — identify a
datum with its mirror, so completeness at the level of `ℂ` is unreachable in principle, not merely
unproved. -/
theorem tsq_family_not_complete {ι : Type*} (f : ι → ℂ → ℂ) :
    ¬ Complete (fun (i : ι) (z : ℂ) => NRRF771.tsq (f i) z) := by
  rw [complete_iff]
  intro h
  have := h ((starRingEnd ℂ) Complex.I) Complex.I fun i => tsq_conj (f i) Complex.I
  rw [Complex.conj_I] at this
  have him := congrArg Complex.im this
  simp at him
  norm_num at him

/-- …but they are complete one level up, about the data they do determine. -/
theorem tsq_quotient_complete {ι : Type*} (f : ι → ℂ → ℂ) :
    Complete (qread fun (i : ι) (z : ℂ) => NRRF771.tsq (f i) z) :=
  quotient_complete _

/-- The pair actually at issue: the `0`-hair reading `|z|²` and the `∞`-ball reading `‖Γ z‖²`, as a
two-element family of relative equality functions. -/
noncomputable def hairBallCarrier : Bool → (ℂ → ℂ)
  | false => id
  | true => Complex.Gamma

@[inherit_doc hairBallCarrier]
noncomputable def hairBallFamily (b : Bool) (z : ℂ) : ℂ := NRRF771.tsq (hairBallCarrier b) z

theorem hairBallFamily_false (z : ℂ) : hairBallFamily false z = ((‖z‖ : ℝ) : ℂ) ^ 2 :=
  NRRF771.tsq_id z

theorem hairBallFamily_true (z : ℂ) :
    hairBallFamily true z = ((‖Complex.Gamma z‖ : ℝ) : ℂ) ^ 2 := NRRF771.tsq_Gamma z

/-- The hair reading and the ball reading are linked by one step of the equality function. -/
theorem hairBall_step {z : ℂ} (hz : z ≠ 0) :
    hairBallFamily true (z + 1) = hairBallFamily false z * hairBallFamily true z :=
  NRRF771.tsq_Gamma_succ hz

/-- The concrete instance of the scope theorem: the hair/ball family is incomplete on `ℂ`, complete
on the level of data it determines. -/
theorem hairBall_scope :
    ¬ Complete hairBallFamily ∧ Complete (qread hairBallFamily) := by
  exact ⟨tsq_family_not_complete hairBallCarrier, quotient_complete _⟩

/-- The ball reading is not a translation of the hair reading: `|1|² = |-1|²` while
`‖Γ 1‖² = 1 ≠ 0 = ‖Γ (-1)‖²`. -/
theorem ball_not_refined_by_hair : ¬ Refines (hairBallFamily false) (hairBallFamily true) := by
  intro h
  have hk : hairBallFamily false (1 : ℂ) = hairBallFamily false (-1 : ℂ) := by
    simp [hairBallFamily, hairBallCarrier, NRRF771.tsq, NRRF771.tmul]
  have hb := h.kernel_le hk
  rw [hairBallFamily, hairBallFamily, NRRF771.tsq, NRRF771.tsq, NRRF771.tmul, NRRF771.tmul] at hb
  have hg1 : Complex.Gamma 1 = 1 := Complex.Gamma_one
  have hgm1 : Complex.Gamma (-1) = 0 := by simpa using Complex.Gamma_neg_nat_eq_zero 1
  simp [hairBallCarrier, hg1, hgm1] at hb

/-- The hair reading is not a translation of the ball reading: `‖Γ (-1)‖² = ‖Γ (-2)‖² = 0` while
`|-1|² = 1 ≠ 4 = |-2|²`. -/
theorem hair_not_refined_by_ball : ¬ Refines (hairBallFamily true) (hairBallFamily false) := by
  intro h
  have hgm1 : Complex.Gamma (-1) = 0 := by simpa using Complex.Gamma_neg_nat_eq_zero 1
  have hgm2 : Complex.Gamma (-2) = 0 := by
    have := Complex.Gamma_neg_nat_eq_zero 2
    norm_num at this
    exact this
  have hk : hairBallFamily true (-1 : ℂ) = hairBallFamily true (-2 : ℂ) := by
    simp [hairBallFamily, hairBallCarrier, NRRF771.tsq, NRRF771.tmul, hgm1, hgm2]
  have hb := h.kernel_le hk
  simp [hairBallFamily, hairBallCarrier, NRRF771.tsq, NRRF771.tmul] at hb
  have := congrArg Complex.re hb
  norm_num at this

/-- **The two readings are genuinely two.**  Neither the `0`-hair reading nor the `∞`-ball reading
is a translation of the other, so the joint reading is strictly finer than either: the organisation
of translational truth into a *family* of relative equality functions gains information that no
single one of them carries. -/
theorem hairBall_independent :
    ¬ Refines (hairBallFamily false) (hairBallFamily true) ∧
      ¬ Refines (hairBallFamily true) (hairBallFamily false) ∧
      ¬ TransEq (hairBallFamily false) (hairBallFamily true) :=
  ⟨ball_not_refined_by_hair, hair_not_refined_by_ball,
    fun h => ball_not_refined_by_hair h.1⟩

/-! ## §5  The answer, in one theorem -/

/-- **How the organisation of translational truth into relative equality functions approaches a
complete theory.**

1. *Representation is not identity* (the Gluon side): distinct descriptions can denote one mapping,
   and the zero-cost conversions between them form a groupoid preserving the logical data.
2. *A relative equality function is exactly the equality it induces*: two readings are
   translationally equal iff they declare the same data equal.
3. *Completeness criterion*: a family is complete iff the identity reading is a translation of it,
   iff no further reading of the data can escape the family's translational reach.
4. *Completeness is always relative to a level*: every family is complete about the quotient it
   determines, so a "complete theory" is reached exactly by driving the joint kernel down to the
   intended equality — over `𝔽₂` the coordinate readings do reach it, while the `|·|²` and `Γ`
   readings provably cannot reach `ℂ`, only its mirror quotient. -/
theorem nrrf772_answer (e : Equiv.Perm (Fin 7)) (regs : Finset (Fin 7)) :
    (gluonBlocked ≠ gluonSliced e ∧ LayoutEquiv gluonBlocked (gluonSliced e)) ∧
    (∀ p q : Pres 7 7, TrivialConv regs p q → Set.range q.eval = Set.range p.eval) ∧
    (∀ {V W : Type} (r : ℂ → V) (s : ℂ → W),
        TransEq r s ↔ ∀ d d', (r d = r d' ↔ s d = s d')) ∧
    (∀ {ι : Type} {V : ι → Type} (r : ∀ i, ℂ → V i),
        Complete r ↔ ∀ (W : Type) (s : ℂ → W), Refines (joint r) s) ∧
    (∀ {ι : Type} {V : ι → Type} (r : ∀ i, ℂ → V i), Complete (qread r)) ∧
    Complete (fun (i : Fin 7) (v : Bits 7) => v i) ∧
    (¬ Complete hairBallFamily ∧ Complete (qread hairBallFamily)) ∧
    (¬ Refines (hairBallFamily false) (hairBallFamily true) ∧
      ¬ Refines (hairBallFamily true) (hairBallFamily false)) := by
  refine ⟨⟨(noCanonicalRepresentation e).2.1, (noCanonicalRepresentation e).2.2.2.2⟩,
    fun _ _ h => trivialConv_range_eq h, fun r s => transEq_iff_kernel r s 0,
    fun r => complete_iff_all_readings r 0, fun r => quotient_complete r, bits_complete 7,
    hairBall_scope, hairBall_independent.1, hairBall_independent.2.1⟩

end NRRF772

/-! ## Axiom audit -/

#print axioms NRRF772.noCanonicalRepresentation
#print axioms NRRF772.trivialConv_range_eq
#print axioms NRRF772.transEq_iff_kernel
#print axioms NRRF772.complete_iff_all_readings
#print axioms NRRF772.quotient_complete
#print axioms NRRF772.tsq_family_not_complete
#print axioms NRRF772.nrrf772_answer
