import Mathlib

/-!
# NRRF708 — The path-ellipse return map, the square Cantor shift, and the Diósi–Penrose comparison

## The request

The user asks how the "path-ellipse closure" topology of the twin-silica / silica-weave /
elliptical-micropillar picture relates to (i) the Miranda–Cardona–Peralta-Salas–Presas chain
*square Cantor set `C × C` → generalized shift → area-preserving disk map → contact geometry →
steady Euler flow*, (ii) Penrose's conformal `0 ∼ ∞` rescaling, and (iii) the Diósi–Penrose
objective-collapse test on levitated silica.

The honest answer is a *test*, not an analogy, and this file states and proves that test.  Three
things are formalised.

## §1–§2  The square Cantor shift and what a return map must look like

`Addr := ℕ → Bool`, `CantorSquare := Addr × Addr` is the symbolic square Cantor set already used in
NRRF418.  Its canonical dynamics is the **baker shift** `bakerShift (x, y) = (tail x, cons (x 0) y)`
— exactly the two-sided shift read through the past/future splitting that Moore's coding uses.
`bakerShift_bijective` gives its explicit inverse; `bakerShift_fixed` and `bakerShift_period_two`
exhibit a fixed point and a genuine period-`2` point.

**The obstruction (`ellipse_rotation_not_conjugate_to_bakerShift`).**  If the path-ellipse return
map is a *rigid rotation* — a translation `x ↦ x + a` on any additive group, which is what a
closed elliptical path with a fixed return angle gives — then it is **never** conjugate to the
square Cantor shift, for any coding whatsoever.  So the ellipse-closure return map as currently
specified carries no computational content: the missing ingredient is not a metaphor but a
non-equicontinuous (hyperbolic / horseshoe-type) return map.

## §3  What a conjugacy *would* buy: undecidability transfer, unconditionally

`Reach f a b := ∃ n, f^[n] a = b`.  `reach_conj_iff` transports reachability along any bijective
semiconjugacy.  `haltStep` is an explicit **computable** self-map of `ℕ` built from Mathlib's
step-bounded evaluator `Nat.Partrec.Code.evaln`, and

* `haltStep_reach_iff` : `Reach (haltStep n) (haltStart c) none ↔ (c.eval n).Dom`;
* `haltStep_reachability_undecidable` : `¬ ComputablePred fun s => Reach (haltStep n) s none`.

So a Turing-complete discrete dynamical system with provably undecidable orbit-reachability exists
in the formal environment, unconditionally.  The master theorem

* `return_map_inherits_undecidability`

then says: *any* return map `g` that admits a computable conjugacy to such a system inherits the
undecidability.  This is precisely the Moore-style lemma the user was told they would need: exhibit
the conjugacy and Turing completeness follows rigorously; without it nothing transfers, and
`ellipse_rotation_not_conjugate_to_bakerShift` shows the naive ellipse return map cannot supply it.

## §4  Diósi–Penrose: when is an excess-decoherence claim distinguishable?

Modelling the two predicted rates as power laws in the superposition separation,
`Γ_excess(Δ) = lam · Δ ^ p` and `Γ_DP(Δ) = kap · Δ ^ q`, `powerlaw_rigidity` shows that agreement of
the two functions on all positive separations forces `lam = kap` **and** `p = q`; contrapositively
`powerlaw_distinguishable` produces an explicit separation `Δ` at which the two differ.  So an
excess-decoherence coupling is distinguishable from Diósi–Penrose exactly when its exponent (or its
amplitude, at equal exponent) differs — otherwise it is absorbed into DP.  `dpLifetime_antitone`
records the DP lifetime `τ = ħ / E_G` decreasing in the gravitational self-energy.

## §5  Penrose `0 ∼ ∞`: the rescaling map, explicitly

The CCC-style closure needs an actual rescaling map, not a slogan.  On `(0, ∞)` the inversion
`x ↦ x⁻¹` is an involution (`ccc_rescale_involutive`) which conjugates dilation by `a` to dilation
by `a⁻¹` (`ccc_rescale_conj_dilation`) and carries the `∞` end to the `0` end and back
(`ccc_rescale_tendsto_atTop`, `ccc_rescale_tendsto_zero`) — the minimal explicit witness of
"`∞` = new `0`" in one dimension.
-/

namespace NRRF708

open Function

/-! ## §1  The symbolic square Cantor set and its shift -/

/-- A Cantor address: an infinite binary string (a ternary expansion with digits `{0,2}`). -/
abbrev Addr : Type := ℕ → Bool

/-- The square Cantor set `C × C` in its symbolic form. -/
abbrev CantorSquare : Type := Addr × Addr

/-- Drop the first symbol. -/
def tail (x : Addr) : Addr := fun n => x (n + 1)

/-- Prepend a symbol. -/
def cons (b : Bool) (x : Addr) : Addr := fun n => Nat.casesOn n b x

@[simp] theorem cons_zero (b : Bool) (x : Addr) : cons b x 0 = b := rfl

@[simp] theorem cons_succ (b : Bool) (x : Addr) (n : ℕ) : cons b x (n + 1) = x n := rfl

@[simp] theorem tail_apply (x : Addr) (n : ℕ) : tail x n = x (n + 1) := rfl

theorem cons_tail (x : Addr) : cons (x 0) (tail x) = x := by
  funext n; cases n <;> rfl

/-- **The square Cantor shift** (baker map): the two-sided shift read through the
`future × past` splitting `C × C`. -/
def bakerShift (s : CantorSquare) : CantorSquare := (tail s.1, cons (s.1 0) s.2)

/-- Its inverse. -/
def bakerShiftInv (s : CantorSquare) : CantorSquare := (cons (s.2 0) s.1, tail s.2)

theorem bakerShiftInv_bakerShift : LeftInverse bakerShiftInv bakerShift := by
  intro s
  simp only [bakerShift, bakerShiftInv, cons_zero]
  ext n
  · exact congrFun (cons_tail s.1) n
  · rfl

theorem bakerShift_bakerShiftInv : RightInverse bakerShiftInv bakerShift := by
  intro s
  simp only [bakerShift, bakerShiftInv, cons_zero]
  ext n
  · rfl
  · exact congrFun (cons_tail s.2) n

theorem bakerShift_bijective : Bijective bakerShift :=
  ⟨bakerShiftInv_bakerShift.injective, bakerShift_bakerShiftInv.surjective⟩

/-- The all-`0` address, the "originless origin" of the coding. -/
def zeroAddr : Addr := fun _ => false

/-- `bakerShift` has a fixed point. -/
theorem bakerShift_fixed : bakerShift (zeroAddr, zeroAddr) = (zeroAddr, zeroAddr) := by
  simp only [bakerShift, zeroAddr]
  ext n
  · rfl
  · cases n <;> rfl

/-- The alternating address `t, f, t, f, …`. -/
def altEven : Addr := fun n => decide (n % 2 = 0)

/-- The alternating address `f, t, f, t, …`. -/
def altOdd : Addr := fun n => decide (n % 2 = 1)

/-- `bakerShift` has a point of exact period `2`: it is not a rigid rotation in disguise. -/
theorem bakerShift_period_two :
    bakerShift (bakerShift (altEven, altOdd)) = (altEven, altOdd) ∧
      bakerShift (altEven, altOdd) ≠ (altEven, altOdd) := by
  constructor
  · simp only [bakerShift, tail_apply]
    ext n
    · show altEven (n + 1 + 1) = altEven n
      simp only [altEven, decide_eq_decide]; omega
    · match n with
      | 0 => rfl
      | 1 => rfl
      | (k + 2) =>
        show altOdd k = altOdd (k + 2)
        simp only [altOdd, decide_eq_decide]; omega
  · intro h
    have h1 : tail altEven 0 = altEven 0 := by
      have := congrArg (fun s => s.1 0) h
      simpa [bakerShift] using this
    simp [tail, altEven] at h1

/-! ## §2  The rotation obstruction

A *rigid* return map — the return map of a closed elliptical path with a fixed return angle — is a
translation on an additive group.  No such map is conjugate to the square Cantor shift, under any
coding at all. -/

/-- **Obstruction.**  If a bijective coding `h` conjugates the square Cantor shift to a rigid
rotation `x ↦ x + a` on an additive group, we get a contradiction.  Hence a path-ellipse return
map that is a rigid rotation can never realise the Moore/Miranda symbolic dynamics, and inherits
no computational content from it. -/
theorem ellipse_rotation_not_conjugate_to_bakerShift {G : Type*} [AddGroup G] (a : G)
    (h : CantorSquare → G) (hinj : Injective h)
    (hconj : ∀ s, h (bakerShift s) = h s + a) : False := by
  have ha : a = 0 := by
    have := hconj (zeroAddr, zeroAddr)
    rw [bakerShift_fixed] at this
    exact (add_eq_left.mp this.symm)
  have hfix : ∀ s, bakerShift s = s := by
    intro s
    apply hinj
    rw [hconj s, ha, add_zero]
  exact bakerShift_period_two.2 (hfix (altEven, altOdd))

/-- The same obstruction stated for the return map itself: a rotation return map `R` on a group,
bijectively coded by the square Cantor set so that the coding intertwines `R` with the shift,
cannot exist. -/
theorem rotation_return_map_not_shift_conjugate {G : Type*} [AddGroup G] (a : G)
    (R : G → G) (hR : ∀ x, R x = x + a)
    (h : CantorSquare → G) (hinj : Injective h)
    (hconj : ∀ s, h (bakerShift s) = R (h s)) : False :=
  ellipse_rotation_not_conjugate_to_bakerShift a h hinj (fun s => by rw [hconj s, hR])

/-! ## §3  Reachability, conjugacy transfer, and an explicit Turing-complete return map -/

open Nat.Partrec.Code (evaln evaln_complete evaln_mono)

/-- Partial-recursive machine codes. -/
abbrev PCode : Type := Nat.Partrec.Code

/-- Orbit reachability of a discrete return map. -/
def Reach {α : Type*} (f : α → α) (a b : α) : Prop := ∃ n, f^[n] a = b

/-- Reachability transports along an injective semiconjugacy: this is the transfer principle a
"path-ellipse ↔ symbolic shift" conjugacy would activate. -/
theorem reach_conj_iff {α β : Type*} {f : α → α} {g : β → β} {h : β → α}
    (hinj : Injective h) (hsemi : ∀ x, h (g x) = f (h x)) (a b : β) :
    Reach g a b ↔ Reach f (h a) (h b) := by
  have hs : Semiconj h g f := hsemi
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [← (hs.iterate_right n) a, hn]⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, hinj (by rw [(hs.iterate_right n) a, hn])⟩

/-- Computable predicates are closed under precomposition with a computable map. -/
theorem computablePred_comp {α β : Type*} [Primcodable α] [Primcodable β] {p : β → Prop}
    (hp : ComputablePred p) {r : α → β} (hr : Computable r) :
    ComputablePred (fun a => p (r a)) := by
  obtain ⟨D, hD⟩ := hp
  exact ⟨fun a => D (r a), hD.comp hr⟩

/-- **The universal halting-search return map.**  A state is either the target `none` or a pair
`(c, k)` meaning "machine code `c`, already simulated for `k` steps on the fixed input `n`".  One
step runs one more step of the step-bounded evaluator `evaln` and lands on the target exactly when
the machine has halted. -/
def haltStep (n : ℕ) (s : Option (PCode × ℕ)) : Option (PCode × ℕ) :=
  s.bind (fun p => Option.casesOn (motive := fun _ => Option (PCode × ℕ))
    (evaln (p.2 + 1) p.1 n) (some (p.1, p.2 + 1)) (fun _ => none))

/-- The initial state for code `c`. -/
def haltStart (c : PCode) : Option (PCode × ℕ) := some (c, 0)

@[simp] theorem haltStep_none (n : ℕ) : haltStep n none = none := rfl

theorem haltStep_some (n : ℕ) (c : PCode) (k : ℕ) :
    haltStep n (some (c, k)) =
      if (evaln (k + 1) c n).isSome then none else some (c, k + 1) := by
  cases h : evaln (k + 1) c n <;> simp [haltStep, h]

/-- Along the orbit of a start state the system is either already at the target or at the state
recording exactly the number of simulated steps. -/
theorem haltStep_iterate_dichotomy (n : ℕ) (c : PCode) (j : ℕ) :
    (haltStep n)^[j] (haltStart c) = none ∨ (haltStep n)^[j] (haltStart c) = some (c, j) := by
  induction j with
  | zero => right; rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with h | h
      · left; rw [h, haltStep_none]
      · rw [h, haltStep_some]
        by_cases hs : (evaln (j + 1) c n).isSome
        · left; simp [hs]
        · right; simp [hs]

theorem haltStep_reach_of_evaln (n : ℕ) (c : PCode) (m : ℕ)
    (hm : (evaln (m + 1) c n).isSome) : Reach (haltStep n) (haltStart c) none := by
  rcases haltStep_iterate_dichotomy n c m with h | h
  · exact ⟨m, h⟩
  · refine ⟨m + 1, ?_⟩
    rw [Function.iterate_succ_apply', h, haltStep_some, if_pos hm]

theorem evaln_of_haltStep_reach (n : ℕ) (c : PCode) (j : ℕ)
    (h : (haltStep n)^[j] (haltStart c) = none) : ∃ m, (evaln (m + 1) c n).isSome := by
  induction j with
  | zero => simp [haltStart] at h
  | succ j ih =>
      rw [Function.iterate_succ_apply'] at h
      rcases haltStep_iterate_dichotomy n c j with h0 | h0
      · exact ih h0
      · rw [h0, haltStep_some] at h
        by_cases hs : (evaln (j + 1) c n).isSome
        · exact ⟨j, hs⟩
        · rw [if_neg hs] at h; simp at h

/-- **Reachability of the target is halting.**  The orbit of `haltStart c` reaches the target state
if and only if machine `c` halts on input `n`. -/
theorem haltStep_reach_iff (n : ℕ) (c : PCode) :
    Reach (haltStep n) (haltStart c) none ↔ (c.eval n).Dom := by
  constructor
  · rintro ⟨j, hj⟩
    obtain ⟨m, hm⟩ := evaln_of_haltStep_reach n c j hj
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hm
    exact (Part.dom_iff_mem).2 ⟨x, evaln_complete.2 ⟨m + 1, hx⟩⟩
  · intro hd
    obtain ⟨x, hx⟩ := Part.dom_iff_mem.1 hd
    obtain ⟨k, hk⟩ := evaln_complete.1 hx
    exact haltStep_reach_of_evaln n c k
      (Option.isSome_iff_exists.2 ⟨x, evaln_mono (Nat.le_succ k) hk⟩)

/-- The return map is genuinely computable: the dynamics is effective, only its orbit structure is
not. -/
theorem haltStep_computable (n : ℕ) : Computable (haltStep n) := by
  have hev : Computable (fun p : PCode × ℕ => evaln (p.2 + 1) p.1 n) :=
    (Nat.Partrec.Code.primrec_evaln.to_comp).comp
      (((Computable.succ.comp Computable.snd).pair Computable.fst).pair (Computable.const n))
  have hinner : Computable (fun p : PCode × ℕ =>
      Option.casesOn (motive := fun _ => Option (PCode × ℕ))
        (evaln (p.2 + 1) p.1 n) (some (p.1, p.2 + 1)) (fun _ => none)) :=
    Computable.option_casesOn hev
      (Computable.option_some.comp (Computable.fst.pair (Computable.succ.comp Computable.snd)))
      (Computable.const none).to₂
  exact Computable.option_bind Computable.id (hinner.comp Computable.snd)

theorem haltStart_computable : Computable haltStart :=
  Computable.option_some.comp (Computable.id.pair (Computable.const 0))

/-- **A Turing-complete return map.**  Orbit reachability of the explicit computable map
`haltStep n` is undecidable.  This is the formal content of "the symbolic side carries
undecidable dynamics", with no hypotheses. -/
theorem haltStep_reachability_undecidable (n : ℕ) :
    ¬ ComputablePred (fun s => Reach (haltStep n) s none) := by
  intro hC
  refine ComputablePred.halting_problem n
    ((computablePred_comp hC haltStart_computable).of_eq fun c => ?_)
  exact haltStep_reach_iff n c

/-- **Master transfer theorem.**  If a return map `g` on a computably presented state space admits
a computable conjugacy `h` (with computable inverse `hinv`) to a system `f` whose reachability
encodes the halting problem, then reachability for `g` is itself undecidable.  This is the exact
shape of the Moore-style lemma the ellipse-closure programme needs: *produce the conjugacy and
Turing completeness is inherited; without it, nothing transfers.* -/
theorem return_map_inherits_undecidability {α β : Type*} [Primcodable α] [Primcodable β]
    (f : α → α) (g : β → β) (h : β → α) (hinv : α → β)
    (hleft : ∀ x, hinv (h x) = x) (hright : ∀ x, h (hinv x) = x)
    (hsemi : ∀ x, h (g x) = f (h x)) (hinv_comp : Computable hinv)
    (n : ℕ) (t : α) (r : PCode → α) (hr : Computable r)
    (hred : ∀ c : PCode, (c.eval n).Dom ↔ Reach f (r c) t) :
    ¬ ComputablePred (fun b => Reach g b (hinv t)) := by
  intro hC
  have hinj : Injective h := Function.LeftInverse.injective hleft
  have hcomp : ComputablePred (fun c : PCode => Reach g (hinv (r c)) (hinv t)) :=
    computablePred_comp hC (hinv_comp.comp hr)
  refine ComputablePred.halting_problem n (hcomp.of_eq fun c => ?_)
  rw [reach_conj_iff hinj hsemi, hright, hright, ← hred c]

/-- The transfer theorem is not vacuous: its hypotheses are satisfied by `haltStep n` with the
identity conjugacy, and the conclusion is then the unconditional undecidability above. -/
theorem return_map_inherits_undecidability_witness (n : ℕ) :
    ¬ ComputablePred (fun s => Reach (haltStep n) s (id none)) :=
  return_map_inherits_undecidability (haltStep n) (haltStep n) id id (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) Computable.id n none haltStart haltStart_computable
    (fun c => (haltStep_reach_iff n c).symm)

/-! ## §4  Diósi–Penrose comparison: distinguishability of an excess-decoherence law -/

/-- The Diósi–Penrose superposition lifetime `τ = ħ / E_G`. -/
noncomputable def dpLifetime (hbar E : ℝ) : ℝ := hbar / E

/-- Larger gravitational self-energy of the mass-distribution difference ⇒ shorter DP lifetime. -/
theorem dpLifetime_antitone {hbar E₁ E₂ : ℝ} (hh : 0 < hbar) (h1 : 0 < E₁) (h12 : E₁ < E₂) :
    dpLifetime hbar E₂ < dpLifetime hbar E₁ := by
  unfold dpLifetime
  exact div_lt_div_of_pos_left hh h1 h12

/-- **Rigidity of power-law rates.**  If an excess-decoherence rate `lam · Δ ^ p` agrees with the
Diósi–Penrose rate `kap · Δ ^ q` at every positive separation, then the amplitudes and the
exponents coincide: the claim is then not a new prediction but DP itself. -/
theorem powerlaw_rigidity {lam kap p q : ℝ} (hl : lam ≠ 0)
    (h : ∀ x : ℝ, 0 < x → lam * x ^ p = kap * x ^ q) : lam = kap ∧ p = q := by
  have h1 : lam = kap := by
    have := h 1 one_pos
    simpa using this
  refine ⟨h1, ?_⟩
  have he := h (Real.exp 1) (Real.exp_pos 1)
  rw [Real.exp_one_rpow, Real.exp_one_rpow, ← h1] at he
  have : Real.exp p = Real.exp q := by
    exact mul_left_cancel₀ hl he
  exact Real.exp_injective this

/-- **Distinguishability.**  Different exponents (or different amplitudes) give an explicit
separation at which the two predicted rates differ — i.e. a falsifiable difference from DP. -/
theorem powerlaw_distinguishable {lam kap p q : ℝ} (hl : lam ≠ 0)
    (hne : ¬ (lam = kap ∧ p = q)) :
    ∃ x : ℝ, 0 < x ∧ lam * x ^ p ≠ kap * x ^ q := by
  by_contra hc
  push_neg at hc
  exact hne (powerlaw_rigidity hl fun x hx => hc x hx)

/-! ## §5  The Penrose-style `0 ∼ ∞` rescaling map, explicitly -/

/-- The one-dimensional conformal rescaling witnessing `0 ∼ ∞`. -/
noncomputable def cccRescale (x : ℝ) : ℝ := x⁻¹

theorem ccc_rescale_involutive (x : ℝ) : cccRescale (cccRescale x) = x := by
  simp [cccRescale]

/-- The rescaling conjugates dilation by `a` to dilation by `a⁻¹`: the scale-inversion law. -/
theorem ccc_rescale_conj_dilation (a x : ℝ) : cccRescale (a * x) = a⁻¹ * cccRescale x := by
  simp [cccRescale, mul_comm]

/-- The `0` end is carried to the `∞` end. -/
theorem ccc_rescale_tendsto_atTop :
    Filter.Tendsto cccRescale (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
  tendsto_inv_nhdsGT_zero

/-- …and the `∞` end back to the `0` end. -/
theorem ccc_rescale_tendsto_zero :
    Filter.Tendsto cccRescale Filter.atTop (nhds 0) :=
  tendsto_inv_atTop_zero

end NRRF708
