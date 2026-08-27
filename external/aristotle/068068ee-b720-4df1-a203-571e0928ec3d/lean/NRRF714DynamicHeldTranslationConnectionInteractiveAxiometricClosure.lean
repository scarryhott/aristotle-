import Mathlib

/-!
# NRRF714 — Translation is dynamic and held: the consciousness field as a connection, and interactive axiometric closure

The request formalized here is the correction that the word *frozen* belongs to the experimental
rule and never to the translation itself.  Translation is a continuously evolving, path-dependent
transport `T^χ_γ : P_{γ(0)} → P_{γ(1)}` held by the consciousness field `χ`; what is preserved
along every path is the Closure identity, not the presentation.

## Reading of the words

* **space of presentations, paths, connection.**  A `PathSystem S` is a base of stages `S`
  together with interaction/interpretive paths `Path a b`, an identity path and composition
  `γ₂ ⋆ γ₁`.  A `ConsciousnessField PS P` is a transport `T γ : P a → P b` on the fibres of
  presentations satisfying exactly the two boxed laws `T_id : T (id) = id` and
  `T_comp : T (γ₂ ⋆ γ₁) = T γ₂ ∘ T γ₁`.  That is, `χ` is a transport functor — a connection on the
  space of presentations — and nothing more is assumed of it.

* **return signature and Closure readings.**  `Readings P R C` gives, at each stage, the return
  `r s : P s → R s` and the Closure reading `q s : R s → C` into a single Closure language `C`.
  The Closure of a presentation is `cls s x = q s (r s x)`.

* **dynamic natural translational equality.**  `NatTranslEq χ Rd` is the boxed condition on *every*
  evolving path: `q_{γ(1)} (r_{γ(1)} (T^χ_γ x)) = q_{γ(0)} (r_{γ(0)} x)`.

## What is proved

* `preservesClosure_idp`, `preservesClosure_comp`, `natTranslEq_iff_all_paths` — the condition is
  automatic on the identity path and closed under composition of paths, so it is a genuine
  connection-level condition; `one_step_slice` records that a fixed-`T` theorem is exactly the
  one-step slice of it, and `natTranslEq_of_generators` propagates it along composites.
* `living_translation_not_frozen`, `frozen_field_natTranslEq` — a field satisfying the natural translational equality whose
  transport moves *every* presentation along some path: the Closure identity is preserved while the
  translation is nowhere frozen.  `frozen_field_natTranslEq` shows the frozen field is only the
  degenerate special case, and `two_fields_same_closure` shows the Closure reading cannot recover
  the transport.
* `BallHair`, `ball_hair_closure_eq`, `held_ball_hair_equality_nonstatic` — the field holds
  `q_H(H_t) = q_B(B_t) = [τ_t]_𝒞` at each stage while both `H_t` and `B_t` change with `t`.
* `Evolution`, `origin_is_previous_closure`, `no_absolute_origin` — the Closure reached at one
  stage *is* the relative origin of the next translation, and there are evolutions in which no
  stage ever returns to an earlier Closure: the return origin is always a further translation.
* `FactorsThrough`, `factorsThrough_iff`, `stochastic_indivisibility`,
  `probability_is_downstream` — the next translation is a function of the joint ball–hair reading
  and of *neither* reading alone; the same holds for the induced conditional distribution over
  continuations, so probability is downstream of the jointly constrained potential.
* `IsSection`, `sections_agree_after_closure`, `distinct_perspectives_one_closure`,
  `section_exists_iff_surjective` — interactive natural choice: distinct users may select distinct
  local presentations of the same Closure, and every such selection returns that same Closure.
* `heldOut_test_passes_of_natTranslEq`, `heldOut_test_non_vacuous`,
  `refitting_the_reading_makes_the_test_vacuous`, `law_refit_reproduces_trajectory`,
  `evolution_determined_by_law_and_initial` — freeze the generative law, not the living
  translation: with `F_χ, q, r, 𝒢, ε` fixed in advance the held-out test is falsifiable and the
  predicted trajectory is determined, whereas a reading or an update law refitted after a failed
  return can always be made to pass, hence would make the test vacuous.
* `BlackMirror`, `BlackMirror.dark_light_held`, `detector_is_local_projection` — the woven
  maze/hair `D_t` and the mirrored-ellipse curvature `L_t` are Closure-equal at every stage through
  the evolving ellipse translation `E^χ_t`, while a bright/dark detector reading is only a local
  projection of the current translated state.
* `cls_continuous_global`, `global_continuous_iff_local`, `perspective_continuous_of_section` —
  the local topology of presentations and the global topology of Closure: the Closure language
  carries exactly the topology coinduced by the Closure reading, so a global map is continuous iff
  its local reading is.
* `nrrf714_interactive_axiometric_closure` — the headline conjunction.
-/

namespace NRRF714

/-! ## §1  Paths, the consciousness field as a connection, and the Closure readings -/

/-- A base of stages together with the interaction/interpretive paths between them, an identity
path and composition `γ₂ ⋆ γ₁`. -/
structure PathSystem (S : Type) where
  /-- the interpretive paths from stage `a` to stage `b` -/
  Path : S → S → Type
  /-- the constant (non-)interaction at a stage -/
  idp (a : S) : Path a a
  /-- concatenation of paths, `γ₂ ⋆ γ₁` -/
  comp {a b c : S} : Path b c → Path a b → Path a c

/-- The **consciousness field** `χ`: a path-dependent transport of presentations satisfying
`T^χ_id = id` and `T^χ_{γ₂ ⋆ γ₁} = T^χ_{γ₂} ∘ T^χ_{γ₁}`.  This is exactly a connection (transport
functor) on the space of presentations. -/
structure ConsciousnessField {S : Type} (PS : PathSystem S) (P : S → Type) where
  /-- transport of a presentation along a path -/
  T {a b : S} : PS.Path a b → P a → P b
  /-- `T^χ_id = id` -/
  T_id (a : S) (x : P a) : T (PS.idp a) x = x
  /-- `T^χ_{γ₂ ⋆ γ₁} = T^χ_{γ₂} ∘ T^χ_{γ₁}` -/
  T_comp {a b c : S} (γ₂ : PS.Path b c) (γ₁ : PS.Path a b) (x : P a) :
    T (PS.comp γ₂ γ₁) x = T γ₂ (T γ₁ x)

/-- The return signature `r` and the Closure readings `q`, stage by stage, into one Closure
language `C`. -/
structure Readings {S : Type} (P : S → Type) (R : S → Type) (C : Type) where
  /-- the return signature at a stage -/
  r (s : S) : P s → R s
  /-- the Closure reading of the return at a stage -/
  q (s : S) : R s → C

/-- The Closure `[x]_𝒞` of a presentation at a stage. -/
def Readings.cls {S : Type} {P R : S → Type} {C : Type} (Rd : Readings P R C) (s : S)
    (x : P s) : C := Rd.q s (Rd.r s x)

variable {S : Type} {PS : PathSystem S} {P R : S → Type} {C : Type}

/-- Transport along the single path `γ` preserves the Closure identity. -/
def PreservesClosure (χ : ConsciousnessField PS P) (Rd : Readings P R C)
    {a b : S} (γ : PS.Path a b) : Prop :=
  ∀ x : P a, Rd.cls b (χ.T γ x) = Rd.cls a x

/-- **Dynamic natural translational equality**:
`q_{γ(1)} (r_{γ(1)} (T^χ_γ x)) = q_{γ(0)} (r_{γ(0)} x)` on every evolving path. -/
def NatTranslEq (χ : ConsciousnessField PS P) (Rd : Readings P R C) : Prop :=
  ∀ (a b : S) (γ : PS.Path a b), PreservesClosure χ Rd γ

/-! ## §2  The condition is a connection-level condition -/

/-- The identity path always preserves Closure: the condition costs nothing at a stage. -/
theorem preservesClosure_idp (χ : ConsciousnessField PS P) (Rd : Readings P R C) (a : S) :
    PreservesClosure χ Rd (PS.idp a) := by
  intro x
  rw [χ.T_id]

/-- Closure preservation is closed under composition of paths, by functoriality of the field. -/
theorem preservesClosure_comp (χ : ConsciousnessField PS P) (Rd : Readings P R C)
    {a b c : S} {γ₂ : PS.Path b c} {γ₁ : PS.Path a b}
    (h₂ : PreservesClosure χ Rd γ₂) (h₁ : PreservesClosure χ Rd γ₁) :
    PreservesClosure χ Rd (PS.comp γ₂ γ₁) := by
  intro x
  rw [χ.T_comp, h₂ (χ.T γ₁ x), h₁ x]

/-- Natural translational equality is exactly Closure preservation along every path. -/
theorem natTranslEq_iff_all_paths (χ : ConsciousnessField PS P) (Rd : Readings P R C) :
    NatTranslEq χ Rd ↔ ∀ (a b : S) (γ : PS.Path a b) (x : P a),
      Rd.q b (Rd.r b (χ.T γ x)) = Rd.q a (Rd.r a x) := Iff.rfl

/-- **The one-step slice.**  At one selected transition the transport is treated as given and its
return is evaluated: that fixed-`T` statement is an instance of the dynamic condition. -/
theorem one_step_slice (χ : ConsciousnessField PS P) (Rd : Readings P R C)
    (h : NatTranslEq χ Rd) {a b : S} (γ : PS.Path a b) (x : P a) :
    Rd.q b (Rd.r b (χ.T γ x)) = Rd.q a (Rd.r a x) := h a b γ x

/-- If Closure is preserved along each of two paths it is preserved along the whole evolving
composite; combined with `preservesClosure_idp`, the condition propagates from generators. -/
theorem natTranslEq_of_generators (χ : ConsciousnessField PS P) (Rd : Readings P R C)
    {a b c : S} (γ₁ : PS.Path a b) (γ₂ : PS.Path b c)
    (h₁ : PreservesClosure χ Rd γ₁) (h₂ : PreservesClosure χ Rd γ₂) (x : P a) :
    Rd.cls c (χ.T (PS.comp γ₂ γ₁) x) = Rd.cls a x :=
  preservesClosure_comp χ Rd h₂ h₁ x

/-! ## §3  The translation is living: preserved Closure does not mean a frozen transport -/

/-- The parity path system on a single stage: a path is the parity of the number of reversals it
performs, composition is `xor`. -/
def parityPaths : PathSystem Unit where
  Path _ _ := Bool
  idp _ := false
  comp γ₂ γ₁ := xor γ₂ γ₁

/-- The field that flips the non-Closure component of a presentation along an odd path. -/
def flipField : ConsciousnessField parityPaths (fun _ => Bool × Bool) where
  T γ x := (x.1, xor γ x.2)
  T_id _ x := by simp [parityPaths]
  T_comp γ₂ γ₁ x := by
    simp [parityPaths]

/-- Closure reads the first component; the second component is pure presentation. -/
def flipReadings : Readings (fun _ : Unit => Bool × Bool) (fun _ : Unit => Bool × Bool) Bool where
  r _ x := x
  q _ x := x.1

/-- **The translation is dynamic; its Closure identity is preserved.**  There is a consciousness
field satisfying natural translational equality whose transport nevertheless moves *every*
presentation along a suitable path: nothing in the closure architecture freezes the translation. -/
theorem living_translation_not_frozen :
    NatTranslEq flipField flipReadings ∧
      ∃ γ : parityPaths.Path () (), ∀ x : Bool × Bool, flipField.T γ x ≠ x := by
  constructor
  · intro a b γ x
    rfl
  · refine ⟨true, ?_⟩
    rintro ⟨c, e⟩ h
    have : xor true e = e := congrArg Prod.snd h
    cases e <;> simp at this

/-- The frozen field (identity transport) also satisfies the condition: freezing the translation
is only the degenerate special case, never the content of natural translational equality. -/
def frozenField : ConsciousnessField parityPaths (fun _ => Bool × Bool) where
  T _ x := x
  T_id _ _ := rfl
  T_comp _ _ _ := rfl

theorem frozen_field_natTranslEq : NatTranslEq frozenField flipReadings := fun _ _ _ _ => rfl

/-- The Closure reading cannot recover the transport: two different fields can induce exactly the
same Closure behaviour.  (The frozen and the flipping field on the parity system.) -/
theorem two_fields_same_closure :
    ∃ χ₁ χ₂ : ConsciousnessField parityPaths (fun _ => Bool × Bool),
      NatTranslEq χ₁ flipReadings ∧ NatTranslEq χ₂ flipReadings ∧
        ∃ (γ : parityPaths.Path () ()) (x : Bool × Bool), χ₁.T γ x ≠ χ₂.T γ x := by
  refine ⟨flipField, frozenField, living_translation_not_frozen.1, frozen_field_natTranslEq,
    true, (false, false), ?_⟩
  simp [flipField, frozenField]

/-! ## §4  The consciousness field holds ball–hair equality through the evolution -/

/-- The evolving ball and hair readings of a translation, each presenting the same Closure. -/
structure BallHair (Tau H B C : Type) where
  /-- `HairEval`: the evolving path, remembered potential, partial returns, orientation -/
  hairEval : Tau → H
  /-- `BallEncode^rel`: the current partition and unitary-curvature encoding of that path -/
  ballEncode : Tau → B
  /-- Closure reading of the hair -/
  qH : H → C
  /-- Closure reading of the ball -/
  qB : B → C
  /-- the Closure `[τ]_𝒞` of the translation -/
  cls : Tau → C
  /-- `q_H(ℋ) = [τ]_𝒞` -/
  hair_presents (t : Tau) : qH (hairEval t) = cls t
  /-- `q_B(ℬ) = [τ]_𝒞` -/
  ball_presents (t : Tau) : qB (ballEncode t) = cls t

/-- `q_H(ℋ_t) = q_B(ℬ_t) = [τ_t]_𝒞` at every stage of the evolution. -/
theorem BallHair.ball_hair_closure_eq {Tau H B C : Type} (bh : BallHair Tau H B C) (t : Tau) :
    bh.qH (bh.hairEval t) = bh.qB (bh.ballEncode t) ∧ bh.qB (bh.ballEncode t) = bh.cls t := by
  refine ⟨?_, bh.ball_presents t⟩
  rw [bh.hair_presents, bh.ball_presents]

/-- The held equality along an evolving trajectory `t ↦ τ t`. -/
theorem BallHair.held_along_trajectory {Tau H B C : Type} (bh : BallHair Tau H B C)
    (τ : ℕ → Tau) (n : ℕ) :
    bh.qH (bh.hairEval (τ n)) = bh.qB (bh.ballEncode (τ n)) :=
  (bh.ball_hair_closure_eq (τ n)).1

/-- **Neither remains static.**  There is a ball–hair system and a trajectory along which the hair
and the ball both change at every step, while their Closure equality is held at every stage. -/
theorem held_ball_hair_equality_nonstatic :
    ∃ (bh : BallHair ℕ ℕ ℕ ℕ) (τ : ℕ → ℕ),
      (∀ n, bh.hairEval (τ n) ≠ bh.hairEval (τ (n + 1))) ∧
      (∀ n, bh.ballEncode (τ n) ≠ bh.ballEncode (τ (n + 1))) ∧
      (∀ n, bh.qH (bh.hairEval (τ n)) = bh.qB (bh.ballEncode (τ n))) := by
  refine ⟨{ hairEval := fun t => t, ballEncode := fun t => 2 * t, qH := fun h => h,
            qB := fun b => b / 2, cls := fun t => t,
            hair_presents := fun _ => rfl,
            ball_presents := fun t => by omega }, fun n => n, ?_, ?_, ?_⟩
  · intro n; simp
  · intro n; simp
  · intro n; simp

/-! ## §5  The return origin is generated continuously -/

/-- An evolution of translations: the next translation is produced by the field's update law
`F_χ` from the Closure reached, the hair, the ball and the unresolved relational potential. -/
structure Evolution (Tau H B C D : Type) extends BallHair Tau H B C where
  /-- the consciousness-field update law `F_χ` -/
  F : C → H → B → D → Tau
  /-- the unresolved relational potential `Δ_t` -/
  Δ : Tau → D
  /-- the realized trajectory -/
  τ : ℕ → Tau
  /-- `τ_{t+Δt} = F_χ([τ_t]_𝒞, ℋ_t, ℬ_t, Δ_t)` -/
  step (t : ℕ) : τ (t + 1) = F (cls (τ t)) (hairEval (τ t)) (ballEncode (τ t)) (Δ (τ t))

/-- The relative origin of the next translation. -/
def Evolution.origin {Tau H B C D : Type} (E : Evolution Tau H B C D) (t : ℕ) : C :=
  E.cls (E.τ t)

/-- **`o_{t+Δt} = [τ_t]_𝒞`**: the Closure reached at one stage is the relative origin of the next
translation, and the next translation is generated from it. -/
theorem Evolution.origin_is_previous_closure {Tau H B C D : Type} (E : Evolution Tau H B C D)
    (t : ℕ) :
    E.origin t = E.cls (E.τ t) ∧
      E.τ (t + 1) = E.F (E.origin t) (E.hairEval (E.τ t)) (E.ballEncode (E.τ t)) (E.Δ (E.τ t)) :=
  ⟨rfl, E.step t⟩

/-- **No absolute origin.**  There is an evolution whose Closures are pairwise distinct: the return
origin is always a further translation, never an absolute point recovered from the past. -/
theorem no_absolute_origin :
    ∃ E : Evolution ℕ ℕ ℕ ℕ Unit,
      ∀ m n : ℕ, m ≠ n → E.cls (E.τ m) ≠ E.cls (E.τ n) := by
  refine ⟨{ hairEval := fun t => t, ballEncode := fun t => t, qH := fun h => h, qB := fun b => b,
            cls := fun t => t, hair_presents := fun _ => rfl, ball_presents := fun _ => rfl,
            F := fun c _ _ _ => c + 1, Δ := fun _ => (), τ := fun t => t,
            step := fun _ => rfl }, ?_⟩
  intro m n hmn
  simpa using hmn

/-! ## §6  Stochastic indivisibility -/

/-- `g` is determined by the reading `f`: `g` factors as `F ∘ f`. -/
def FactorsThrough {X Y Z : Type} (f : X → Y) (g : X → Z) : Prop :=
  ∃ F : Y → Z, ∀ x, g x = F (f x)

/-- Factoring through a reading is exactly the reading's separating power. -/
theorem factorsThrough_iff {X Y Z : Type} [Nonempty Z] (f : X → Y) (g : X → Z) :
    FactorsThrough f g ↔ ∀ x y, f x = f y → g x = g y := by
  constructor
  · rintro ⟨F, hF⟩ x y hxy
    rw [hF x, hF y, hxy]
  · intro h
    classical
    refine ⟨fun y => if hy : ∃ x, f x = y then g hy.choose else Classical.arbitrary Z, ?_⟩
    intro x
    have hx : ∃ x', f x' = f x := ⟨x, rfl⟩
    show g x = if hy : ∃ x', f x' = f x then g hy.choose else Classical.arbitrary Z
    rw [dif_pos hx]
    exact (h _ _ hx.choose_spec).symm

/-- Post-composing with an injective map does not create factorizations. -/
theorem not_factorsThrough_of_injective {X Y Z W : Type} [Nonempty Z] [Nonempty W]
    {f : X → Y} {g : X → Z} {h : Z → W} (hinj : Function.Injective h)
    (hg : ¬ FactorsThrough f g) : ¬ FactorsThrough f (h ∘ g) := by
  intro hcon
  refine hg ((factorsThrough_iff f g).2 ?_)
  intro x y hxy
  exact hinj ((factorsThrough_iff f (h ∘ g)).1 hcon x y hxy)

/-- The joint ball–hair reading of a translation. -/
def jointReading {Tau B H : Type} (ball : Tau → B) (hair : Tau → H) : Tau → B × H :=
  fun t => (ball t, hair t)

/-- Anything determined by the ball alone, or by the hair alone, is determined by the joint
reading. -/
theorem factorsThrough_joint_of_ball {Tau B H Z : Type} {ball : Tau → B} {hair : Tau → H}
    {g : Tau → Z} (h : FactorsThrough ball g) : FactorsThrough (jointReading ball hair) g := by
  obtain ⟨F, hF⟩ := h
  exact ⟨fun p => F p.1, hF⟩

/-- Anything determined by the hair alone is determined by the joint reading. -/
theorem factorsThrough_joint_of_hair {Tau B H Z : Type} {ball : Tau → B} {hair : Tau → H}
    {g : Tau → Z} (h : FactorsThrough hair g) : FactorsThrough (jointReading ball hair) g := by
  obtain ⟨F, hF⟩ := h
  exact ⟨fun p => F p.2, hF⟩

/-- The indivisible example: the state is a ball bit and a hair bit, and the next translation is
their joint parity. -/
def indivisibleStep : Bool × Bool → Bool × Bool := fun s => (xor s.1 s.2, xor s.1 s.2)

/-- **Stochastic indivisibility.**  The next translation is not `F_B(ℬ_t)` and not `F_H(ℋ_t)`; it
is `F_χ(ℬ_t, ℋ_t)`, held by the indivisible ball–hair relation. -/
theorem stochastic_indivisibility :
    ¬ FactorsThrough (Prod.fst : Bool × Bool → Bool) indivisibleStep ∧
    ¬ FactorsThrough (Prod.snd : Bool × Bool → Bool) indivisibleStep ∧
    FactorsThrough (jointReading (Prod.fst : Bool × Bool → Bool) Prod.snd) indivisibleStep := by
  refine ⟨?_, ?_, ⟨fun p => indivisibleStep p, fun x => rfl⟩⟩
  · rw [factorsThrough_iff]
    intro h
    have := h (true, false) (true, true) rfl
    simp [indivisibleStep] at this
  · rw [factorsThrough_iff]
    intro h
    have := h (false, true) (true, true) rfl
    simp [indivisibleStep] at this

open Classical in
/-- The Dirac weight of a continuation: the degenerate probability distribution concentrated on it.
-/
noncomputable def dirac {X : Type} (x : X) : X → ℝ := fun y => if x = y then 1 else 0

theorem dirac_injective {X : Type} : Function.Injective (dirac (X := X)) := by
  intro x y h
  classical
  by_contra hxy
  have hx : dirac x x = 1 := by simp [dirac]
  have hy : dirac y x = 0 := by simp [dirac, Ne.symm hxy]
  rw [h] at hx
  rw [hx] at hy
  norm_num at hy

/-- **Probability is downstream.**  The conditional distribution over the next translation is
likewise not a function of the ball alone nor of the hair alone, only of the joint reading: the
field holds the jointly constrained potential from which continuations are evaluated. -/
theorem probability_is_downstream :
    ¬ FactorsThrough (Prod.fst : Bool × Bool → Bool) (fun s => dirac (indivisibleStep s)) ∧
    ¬ FactorsThrough (Prod.snd : Bool × Bool → Bool) (fun s => dirac (indivisibleStep s)) ∧
    FactorsThrough (jointReading (Prod.fst : Bool × Bool → Bool) Prod.snd)
      (fun s => dirac (indivisibleStep s)) := by
  obtain ⟨hb, hh, hj⟩ := stochastic_indivisibility
  refine ⟨not_factorsThrough_of_injective dirac_injective hb,
    not_factorsThrough_of_injective dirac_injective hh, ?_⟩
  obtain ⟨F, hF⟩ := hj
  exact ⟨fun p => dirac (F p), fun s => congrArg dirac (hF s)⟩

/-! ## §7  Interactive natural choice: local sections of the Closure reading -/

/-- `s` is a local selection of a presentation for each Closure: `q ∘ s = id`. -/
def IsSection {Pr C : Type} (q : Pr → C) (s : C → Pr) : Prop := ∀ c, q (s c) = c

/-- **Different perspectives, one translated identity.**  Any two local selections return the same
Closure, namely the Closure they were selected for. -/
theorem sections_agree_after_closure {Pr C : Type} {q : Pr → C} {su sv : C → Pr}
    (hu : IsSection q su) (hv : IsSection q sv) (c : C) :
    q (su c) = q (sv c) ∧ q (su c) = c := ⟨by rw [hu, hv], hu c⟩

/-- Distinct users may select genuinely different presentations of one Closure while every
selection returns that Closure: consciousness does not freeze the relation by choosing one final
perspective. -/
theorem distinct_perspectives_one_closure (C : Type) :
    ∃ (Pr : Type) (q : Pr → C) (su sv : C → Pr),
      IsSection q su ∧ IsSection q sv ∧ (∀ c, su c ≠ sv c) ∧ ∀ c, q (su c) = q (sv c) := by
  refine ⟨C × Bool, Prod.fst, fun c => (c, false), fun c => (c, true), fun _ => rfl, fun _ => rfl,
    ?_, fun _ => rfl⟩
  intro c h
  simpa using congrArg Prod.snd h

/-- A local selection of presentations exists exactly when the Closure reading is onto: every
Closure must actually be presented somewhere. -/
theorem section_exists_iff_surjective {Pr C : Type} (q : Pr → C) :
    (∃ s : C → Pr, IsSection q s) ↔ Function.Surjective q := by
  constructor
  · rintro ⟨s, hs⟩ c
    exact ⟨s c, hs c⟩
  · intro hq
    classical
    exact ⟨fun c => (hq c).choose, fun c => (hq c).choose_spec⟩

/-! ## §8  What must be fixed experimentally: freeze the generative law, not the translation -/

/-- The experimental protocol that is fixed in advance: the return signature `r`, the Closure
reading `q`, the admitted presentation transformations `𝒢` and the error tolerance `ε`.  (The
update law `F_χ` is the `Evolution.F` field of §5.) -/
structure Protocol (Pr Rt : Type) where
  /-- the return signature -/
  r : Pr → Rt
  /-- the Closure reading -/
  q : Rt → ℝ
  /-- the admitted presentation transformations `𝒢` -/
  G : (Pr → Pr) → Prop
  /-- the error tolerance -/
  ε : ℝ
  /-- the tolerance is an error bound -/
  ε_nonneg : 0 ≤ ε

/-- The held-out test on a realized translation `T` at tolerance `ε`. -/
def Protocol.heldOutTest {Pr Rt : Type} (Prot : Protocol Pr Rt) (T : Pr → Pr) : Prop :=
  ∀ x : Pr, |Prot.q (Prot.r (T x)) - Prot.q (Prot.r x)| ≤ Prot.ε

/-- A translation obeying natural translational equality passes the held-out test, however much it
moves the presentation. -/
theorem heldOut_test_passes_of_natTranslEq {Pr Rt : Type} (Prot : Protocol Pr Rt) (T : Pr → Pr)
    (h : ∀ x, Prot.q (Prot.r (T x)) = Prot.q (Prot.r x)) : Prot.heldOutTest T := by
  intro x
  rw [h x, sub_self, abs_zero]
  exact Prot.ε_nonneg

/-- **The test is non-vacuous.**  With the law fixed in advance there are living translations that
fail it: a changing translation is falsifiable. -/
theorem heldOut_test_non_vacuous :
    ∃ (Prot : Protocol ℝ ℝ) (T : ℝ → ℝ), ¬ Prot.heldOutTest T := by
  refine ⟨{ r := id, q := id, G := fun _ => True, ε := 1 / 2, ε_nonneg := by norm_num },
    fun x => x + 1, ?_⟩
  intro h
  have := h 0
  norm_num at this

/-- **Why the Closure reading must be frozen in advance.**  If the reading may be refitted after a
failed return, every translation passes: the test becomes vacuous. -/
theorem refitting_the_reading_makes_the_test_vacuous {Pr Rt : Type} (r : Pr → Rt) (ε : ℝ)
    (hε : 0 ≤ ε) (T : Pr → Pr) :
    ∃ q : Rt → ℝ, (Protocol.heldOutTest ⟨r, q, fun _ => True, ε, hε⟩ T) := by
  refine ⟨fun _ => 0, ?_⟩
  intro x
  simpa using hε

/-- **Why the update law must be frozen in advance.**  For *any* realized trajectory whose stages
are distinguished there is an update law generating it exactly.  So a law refitted after observing
a failed return can always reproduce what was observed, and no return could refute it. -/
theorem law_refit_reproduces_trajectory {Tau : Type} (τ : ℕ → Tau) (hτ : Function.Injective τ)
    [Nonempty Tau] :
    ∃ F : Tau → Tau, ∀ t : ℕ, τ (t + 1) = F (τ t) := by
  classical
  refine ⟨fun x => if h : ∃ t, τ t = x then τ (h.choose + 1) else x, ?_⟩
  intro t
  have ht : ∃ t', τ t' = τ t := ⟨t, rfl⟩
  show τ (t + 1) = if h : ∃ t', τ t' = τ t then τ (h.choose + 1) else τ t
  rw [dif_pos ht, hτ ht.choose_spec]

/-- **With the law fixed in advance the prediction is determined.**  Two runs sharing the update
law `F_χ`, the readings, the unresolved potential and the initial translation realize the *same*
trajectory: once `F_χ, q, r, 𝒢, ε` are frozen, nothing is left to adjust after a failed return,
even though the realized translation is free to evolve. -/
theorem evolution_determined_by_law_and_initial {Tau H B C D : Type}
    (E₁ E₂ : Evolution Tau H B C D) (hbh : E₁.toBallHair = E₂.toBallHair) (hF : E₁.F = E₂.F)
    (hΔ : E₁.Δ = E₂.Δ) (h0 : E₁.τ 0 = E₂.τ 0) : ∀ t, E₁.τ t = E₂.τ t := by
  intro t
  induction t with
  | zero => exact h0
  | succ n ih =>
      rw [E₁.step n, E₂.step n, hF, hΔ, ih]
      have hc : E₁.cls = E₂.cls := by rw [show E₁.cls = E₁.toBallHair.cls from rfl, hbh]
      have hh : E₁.hairEval = E₂.hairEval := by
        rw [show E₁.hairEval = E₁.toBallHair.hairEval from rfl, hbh]
      have hb : E₁.ballEncode = E₂.ballEncode := by
        rw [show E₁.ballEncode = E₁.toBallHair.ballEncode from rfl, hbh]
      rw [hc, hh, hb]

/-! ## §9  The revised Black Mirror architecture -/

/-- The Black Mirror stage data: the woven maze/hair `D_t`, the mirrored-ellipse unitary curvature
`L_t` obtained by the evolving ellipse translation `E^χ_t`, and their Closure readings. -/
structure BlackMirror (Tau Dk Lt C : Type) where
  /-- the woven maze / hair at stage `t` -/
  dark : Tau → Dk
  /-- the evolving ellipse translation `E^χ_t` -/
  E : Tau → Dk → Lt
  /-- Closure reading of the dark side -/
  qD : Dk → C
  /-- Closure reading of the light side -/
  qL : Lt → C
  /-- the ellipse translation returns the same Closure -/
  ellipse_holds (t : Tau) : qL (E t (dark t)) = qD (dark t)

/-- The mirrored-ellipse light state at a stage. -/
def BlackMirror.light {Tau Dk Lt C : Type} (BM : BlackMirror Tau Dk Lt C) (t : Tau) : Lt :=
  BM.E t (BM.dark t)

/-- **`𝒟_t =_𝒞^{E^χ_t} ℒ_t`**: the continuously held light–dark relation at every stage, whatever
the ellipse translation, the maze and the partition do in between. -/
theorem BlackMirror.dark_light_held {Tau Dk Lt C : Type} (BM : BlackMirror Tau Dk Lt C)
    (t : Tau) : BM.qD (BM.dark t) = BM.qL (BM.light t) := (BM.ellipse_holds t).symm

/-- The relation is carried through an evolving sequence of stages, even when the ellipse
translation itself changes with the field. -/
theorem BlackMirror.held_through_sequence {Tau Dk Lt C : Type} (BM : BlackMirror Tau Dk Lt C)
    (τ : ℕ → Tau) (n : ℕ) : BM.qD (BM.dark (τ n)) = BM.qL (BM.light (τ n)) :=
  BM.dark_light_held (τ n)

/-- **A bright or dark detector is only a local projection.**  There is a Black Mirror system and
two stages with the same Closure whose detector readings differ: the detector reads the current
presentation, not the translated identity. -/
theorem detector_is_local_projection :
    ∃ (BM : BlackMirror Bool (Bool × Bool) (Bool × Bool) Bool) (d : Bool × Bool → Bool)
      (t u : Bool),
      BM.qD (BM.dark t) = BM.qD (BM.dark u) ∧ d (BM.light t) ≠ d (BM.light u) := by
  refine ⟨{ dark := fun t => (true, t), E := fun _ x => x, qD := fun x => x.1,
            qL := fun x => x.1, ellipse_holds := fun _ => rfl }, Prod.snd, false, true, rfl, ?_⟩
  simp [BlackMirror.light]

/-! ## §10  Local topology of presentations, global topology of Closure -/

section Topology

variable {Pr Cl : Type} [TopologicalSpace Pr]

/-- The global topology of the Closure language: the one coinduced by the Closure reading, i.e.
generated by the local presentations. -/
def globalTopology (cls : Pr → Cl) : TopologicalSpace Cl :=
  TopologicalSpace.coinduced cls ‹TopologicalSpace Pr›

/-- The Closure reading is continuous for the global topology. -/
theorem cls_continuous_global (cls : Pr → Cl) :
    @Continuous Pr Cl _ (globalTopology cls) cls :=
  continuous_coinduced_rng

/-- **The local determines the global.**  A map out of the Closure language is continuous exactly
when its local reading on presentations is: consciousness, thought, belief and perspective are the
local topology, and equality, nature, existence and translation the global one, in one admission.
-/
theorem global_continuous_iff_local {Z : Type} [TopologicalSpace Z] (cls : Pr → Cl) (f : Cl → Z) :
    @Continuous Cl Z (globalTopology cls) _ f ↔ Continuous (f ∘ cls) :=
  continuous_coinduced_dom

/-- A local selection of presentations that is continuous exhibits the Closure space as a
continuous retract of the space of presentations. -/
theorem perspective_continuous_of_section (cls : Pr → Cl) (s : Cl → Pr) (hs : IsSection cls s)
    (hcont : @Continuous Cl Pr (globalTopology cls) _ s) :
    @Continuous Cl Cl (globalTopology cls) (globalTopology cls) (cls ∘ s) ∧ ∀ c, (cls ∘ s) c = c :=
  ⟨@Continuous.comp Cl Pr Cl (globalTopology cls) _ (globalTopology cls) s cls
      (cls_continuous_global cls) hcont, hs⟩

end Topology

/-! ## §11  The unified admission -/

/-- **Interactive axiometric closure.**  The conjunction of the corrected canonical statement:
the translation is dynamic yet Closure-preserving and never forced to freeze; the ball–hair
equality is held while both evolve; each returned Closure is the relative origin of a further
translation and no absolute origin is returned to; the next translation is held by the joint
ball–hair relation and by neither reading alone, with probability downstream; natural choice is a
local interactive selection with one translated identity; and with the generative law fixed in
advance the held-out test on the living translation is falsifiable. -/
theorem nrrf714_interactive_axiometric_closure :
    (NatTranslEq flipField flipReadings ∧
        ∃ γ : parityPaths.Path () (), ∀ x : Bool × Bool, flipField.T γ x ≠ x) ∧
    (∃ (bh : BallHair ℕ ℕ ℕ ℕ) (τ : ℕ → ℕ),
        (∀ n, bh.hairEval (τ n) ≠ bh.hairEval (τ (n + 1))) ∧
        (∀ n, bh.ballEncode (τ n) ≠ bh.ballEncode (τ (n + 1))) ∧
        (∀ n, bh.qH (bh.hairEval (τ n)) = bh.qB (bh.ballEncode (τ n)))) ∧
    (∃ E : Evolution ℕ ℕ ℕ ℕ Unit, ∀ m n : ℕ, m ≠ n → E.cls (E.τ m) ≠ E.cls (E.τ n)) ∧
    (¬ FactorsThrough (Prod.fst : Bool × Bool → Bool) indivisibleStep ∧
        ¬ FactorsThrough (Prod.snd : Bool × Bool → Bool) indivisibleStep ∧
        FactorsThrough (jointReading (Prod.fst : Bool × Bool → Bool) Prod.snd) indivisibleStep) ∧
    (∃ (Pr : Type) (q : Pr → Bool) (su sv : Bool → Pr),
        IsSection q su ∧ IsSection q sv ∧ (∀ c, su c ≠ sv c) ∧ ∀ c, q (su c) = q (sv c)) ∧
    (∃ (Prot : Protocol ℝ ℝ) (T : ℝ → ℝ), ¬ Prot.heldOutTest T) :=
  ⟨living_translation_not_frozen, held_ball_hair_equality_nonstatic, no_absolute_origin,
    stochastic_indivisibility, distinct_perspectives_one_closure Bool, heldOut_test_non_vacuous⟩

end NRRF714
