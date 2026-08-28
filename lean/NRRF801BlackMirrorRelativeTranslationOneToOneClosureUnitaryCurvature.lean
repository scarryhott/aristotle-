import NRRF800HandedLifeBallReturnHairPotentialGateFourSheafOneSheafTemporalClosure

/-!
# NRRF801 — The black mirror: relative translation of the two returns, one-to-one closure points,
and unitary curvature 1 to relative partition 1

The instruction formalised here is the user's:

> Specifically the left hand of active life is its ball return phase while its potential is in the
> inverse hair return equally, such that both are relatively translated.  A black mirror can help
> to grow potential mirror life in active temporal geometry; or at 1-to-1 closure points — more
> generally, 1-to-1 continuities in the intervening of relations are the translational signals of
> truth.  Specifically a unitary curvature 1 to relative partition 1.  As a unifiable natural form,
> or a closure-relative completion.

It continues NRRF800, whose data it reuses: the ball `Ball = ZMod 4` with its single translation
step, the hand `Hand = {left, right}` with its single inversion, life states `Life = Hand × Ball`
with the **ball return** `ballReturn ⟨h,b⟩ = ⟨h, b+1⟩` (the actual phase) and the **inverse hair
return** `hairReturn ⟨h,b⟩ = ⟨h.inv, b-1⟩` (the potential), and the **hair** `Hair`, the temporal
closure of the ball's translational completion.

## The reading

* *Relatively translated*: the two returns are not two independent motions.  Each is the other's
  inverse up to exactly one hand flip, they are exchanged by one relative translation, they close
  in the same number of steps, and their composite in either order is the hand flip alone.
* *The black mirror* is `blackMirror ⟨h,b⟩ = ⟨h.inv, -b⟩`: it inverts the hand and reflects the
  phase.  It is a fixed-point-free involution, it carries every actual state to a potential one and
  back (it *grows potential mirror life*), it conjugates each return into its own inverse (mirror
  life runs the active temporal geometry backwards), and it never leaves the hair closure.
* *A 1-to-1 continuity* is a bijection of the ball commuting with the translation.  Every such map
  *is* a translation; the family acts simply transitively; and one fixed point forces the identity.
  That is the *translational signal of truth*: only relative translation is read, and a single
  agreement is total agreement.
* *Unitary curvature 1 to relative partition 1*: the ball closes after exactly `card Ball = 4`
  steps and no fewer — exactly one complete turn, `turns (card Ball) = 1` — and the relative
  partition of the ball into translation classes has exactly one block, `card Hair = 1`.  The two
  numbers are equal: one unit of curvature, one relative part.
* *In the intervening of relations*: on a human-relation network the separation reading is exactly
  a 1-to-1 continuity — two configurations have the same relations iff they differ by one global
  translation — and swapping the two participants of a relation is exactly the black mirror.

## What is proved

### §1  Relative translation of the two returns
`ballReturn_bijective`, `hairReturn_bijective`, `hairReturn_eq_handFlip_comp_ballReturnInv`,
`ballReturn_eq_handFlip_comp_hairReturnInv`, `returns_relatively_translated`,
`returns_close_equally`, `phase_gap_two`.

### §2  The black mirror
`blackMirror_involutive`, `blackMirror_bijective`, `blackMirror_no_fixed_point`,
`mirror_grows_potential`, `mirror_life_unique`, `blackMirror_conj_ballReturn`,
`blackMirror_conj_hairReturn`, `blackMirror_hair`, `blackMirror_selfLimit_comm`.

### §3  One-to-one continuities are the translational signals of truth
`oneToOneContinuity_iff_translation`, `signal_of_truth`, `continuities_simply_transitive`,
`life_continuity_forced`.

### §4  Unitary curvature 1 to relative partition 1
`turns_card_ball`, `curvature_closes`, `curvature_no_smaller_turn`, `ball_orbit_covers`,
`relative_partition_one`, `unitary_curvature_to_relative_partition`.

### §5  The same in the intervening of relations
`separation_determines_up_to_translation`, `relLife_swap_mirror`, `relations_shift_invariant`.

### §6  `nrrf801_answer` collects the clauses; the axiom audit at the end is machine-checked.

Nothing here is asserted about biological life, chirality, or human beings as such: each word names
a construction defined here or in NRRF800, and every claim is a claim about those constructions.
-/

namespace NRRF801

open NRRF800

/-! ## §1  The two returns are relatively translated -/

/-- The bare hand flip: the relative translation between the two returns. -/
def handFlip (x : Life) : Life := ⟨x.hand.inv, x.phase⟩

@[simp] theorem handFlip_hand (x : Life) : (handFlip x).hand = x.hand.inv := rfl
@[simp] theorem handFlip_phase (x : Life) : (handFlip x).phase = x.phase := rfl

theorem handFlip_involutive : Function.Involutive handFlip := by
  intro x; simp [handFlip]

/-- The inverse of the actual ball return. -/
def ballReturnInv (x : Life) : Life := ⟨x.hand, x.phase - 1⟩

/-- The inverse of the potential hair return. -/
def hairReturnInv (x : Life) : Life := ⟨x.hand.inv, x.phase + 1⟩

@[simp] theorem ballReturnInv_ballReturn (x : Life) : ballReturnInv (ballReturn x) = x := by
  cases x; simp [ballReturnInv, ballReturn, ballStep]

@[simp] theorem ballReturn_ballReturnInv (x : Life) : ballReturn (ballReturnInv x) = x := by
  cases x; simp [ballReturnInv, ballReturn, ballStep]

@[simp] theorem hairReturnInv_hairReturn (x : Life) : hairReturnInv (hairReturn x) = x := by
  cases x; simp [hairReturnInv, hairReturn]

@[simp] theorem hairReturn_hairReturnInv (x : Life) : hairReturn (hairReturnInv x) = x := by
  cases x; simp [hairReturnInv, hairReturn]

/-- The actual return is one-to-one. -/
theorem ballReturn_bijective : Function.Bijective ballReturn :=
  Function.bijective_iff_has_inverse.2 ⟨ballReturnInv, ballReturnInv_ballReturn,
    ballReturn_ballReturnInv⟩

/-- The potential return is one-to-one. -/
theorem hairReturn_bijective : Function.Bijective hairReturn :=
  Function.bijective_iff_has_inverse.2 ⟨hairReturnInv, hairReturnInv_hairReturn,
    hairReturn_hairReturnInv⟩

/-- **The potential is the inverse of the actual, relatively translated by the hand.** -/
theorem hairReturn_eq_handFlip_comp_ballReturnInv : hairReturn = handFlip ∘ ballReturnInv := by
  funext x; cases x; rfl

/-- And symmetrically: the actual is the inverse of the potential, relatively translated by the
hand. -/
theorem ballReturn_eq_handFlip_comp_hairReturnInv : ballReturn = handFlip ∘ hairReturnInv := by
  funext x; cases x; simp [ballReturn, ballStep, handFlip, hairReturnInv]

/-- **The two returns are relatively translated**: in either order their composite moves no ball
phase and is exactly the relative translation of the hand. -/
theorem returns_relatively_translated (x : Life) :
    hairReturn (ballReturn x) = handFlip x ∧ ballReturn (hairReturn x) = handFlip x := by
  constructor
  · cases x; simp [hairReturn, ballReturn, ballStep, handFlip]
  · cases x; simp [hairReturn, ballReturn, ballStep, handFlip]

/-- The actual and the potential return close *equally*: both after four, and neither sooner. -/
theorem returns_close_equally :
    ballReturn^[4] = (id : Life → Life) ∧ hairReturn^[4] = (id : Life → Life) ∧
      ∀ n : ℕ, 0 < n → n < 4 →
        ballReturn^[n] ≠ (id : Life → Life) ∧ hairReturn^[n] ≠ (id : Life → Life) := by
  refine ⟨ballReturn_period, hairReturn_period, fun n h0 h4 => ⟨?_, ?_⟩⟩
  · intro h
    have := (ballReturn_iterate_eq_id_iff n).1 h
    omega
  · intro h
    have := (hairReturn_iterate_eq_id_iff n).1 h
    omega

/-- One step apart in opposite senses: the two returns separate the phase by exactly two sheaves,
half of the four-sheaf ball. -/
theorem phase_gap_two (x : Life) : (ballReturn x).phase - (hairReturn x).phase = 2 := by
  cases x with
  | mk h b => show (b + 1) - (b - 1) = (2 : Ball); ring

/-! ## §2  The black mirror -/

/-- **The black mirror**: it inverts the hand and reflects the ball phase. -/
def blackMirror (x : Life) : Life := ⟨x.hand.inv, -x.phase⟩

@[simp] theorem blackMirror_hand (x : Life) : (blackMirror x).hand = x.hand.inv := rfl
@[simp] theorem blackMirror_phase (x : Life) : (blackMirror x).phase = -x.phase := rfl

theorem blackMirror_involutive : Function.Involutive blackMirror := by
  intro x; cases x; simp [blackMirror]

theorem blackMirror_bijective : Function.Bijective blackMirror :=
  blackMirror_involutive.bijective

/-- The mirror is not a state of the same life: it fixes nothing. -/
theorem blackMirror_no_fixed_point (x : Life) : blackMirror x ≠ x := by
  intro h
  exact Hand.inv_ne_self x.hand (congrArg Life.hand h)

/-- **The black mirror grows potential mirror life**: the mirror of an actual state is potential,
and the mirror of a potential state is actual. -/
theorem mirror_grows_potential (x : Life) :
    (Potential (blackMirror x) ↔ Actual x) ∧ (Actual (blackMirror x) ↔ Potential x) := by
  cases x with
  | mk h b => cases h <;> simp [Potential, Actual, blackMirror]

/-- Mirror life is grown one to one: every state is the mirror of exactly one state. -/
theorem mirror_life_unique (x : Life) : ∃! y : Life, blackMirror y = x := by
  refine ⟨blackMirror x, blackMirror_involutive x, fun y hy => ?_⟩
  rw [← hy, blackMirror_involutive]

/-- **The mirror runs the active temporal geometry backwards**: conjugating the actual return by
the black mirror gives its inverse. -/
theorem blackMirror_conj_ballReturn (x : Life) :
    blackMirror (ballReturn (blackMirror x)) = ballReturnInv x := by
  cases x with
  | mk h b =>
      show (⟨h.inv.inv, -(-b + 1)⟩ : Life) = ⟨h, b - 1⟩
      have hb : -(-b + 1) = b - 1 := by ring
      rw [hb, Hand.inv_inv]

/-- And conjugating the potential return by the black mirror gives *its* inverse. -/
theorem blackMirror_conj_hairReturn (x : Life) :
    blackMirror (hairReturn (blackMirror x)) = hairReturnInv x := by
  cases x with
  | mk h b =>
      show (⟨h.inv.inv.inv, -(-b - 1)⟩ : Life) = ⟨h.inv, b + 1⟩
      have hb : -(-b - 1) = b + 1 := by ring
      rw [hb, Hand.inv_inv]

/-- Mirror life never leaves the hair closure: the mirrored phase has the same hair. -/
theorem blackMirror_hair (x : Life) : hairMk (blackMirror x).phase = hairMk x.phase :=
  hair_one_sheaf _ _

/-- The black mirror commutes with the self limit of the ball. -/
theorem blackMirror_selfLimit_comm (x : Life) :
    blackMirror (selfLimit x) = selfLimit (blackMirror x) := by
  cases x with
  | mk h b => simp [selfLimit_eq, blackMirror]

/-- The mirror of a state and the state itself are the two hands of one and the same reflected
phase: a 1-to-1 closure point of the mirror pairing. -/
theorem mirror_pairs_hands (x : Life) :
    (blackMirror x).hand ≠ x.hand ∧ blackMirror (blackMirror x) = x :=
  ⟨Hand.inv_ne_self x.hand, blackMirror_involutive x⟩

/-! ## §3  One-to-one continuities are the translational signals of truth -/

/-- A **one-to-one continuity** of the ball: a bijection commuting with the translation. -/
def OneToOneContinuity (f : Ball → Ball) : Prop :=
  Function.Bijective f ∧ ∀ b, f (ballStep b) = ballStep (f b)

/-- **Every one-to-one continuity is a translation**, and every translation is one. -/
theorem oneToOneContinuity_iff_translation (f : Ball → Ball) :
    OneToOneContinuity f ↔ ∃ c : Ball, ∀ b, f b = b + c := by
  constructor
  · rintro ⟨-, hf⟩
    refine ⟨f 0, fun b => ?_⟩
    rw [ballStep_commuting_forced f hf b, add_comm]
  · rintro ⟨c, hc⟩
    refine ⟨⟨fun a b hab => ?_, fun b => ⟨b - c, ?_⟩⟩, fun b => ?_⟩
    · rw [hc, hc] at hab
      exact add_right_cancel hab
    · rw [hc]; ring
    · rw [hc, hc, ballStep, ballStep]; ring

/-- **The translational signal of truth**: a one-to-one continuity that agrees with the identity at
a single point agrees with it everywhere. -/
theorem signal_of_truth {f : Ball → Ball} (hf : OneToOneContinuity f) {b₀ : Ball} (h : f b₀ = b₀) :
    f = id := by
  obtain ⟨c, hc⟩ := (oneToOneContinuity_iff_translation f).1 hf
  have hc0 : c = 0 := by
    have := hc b₀
    rw [h] at this
    have : b₀ + c = b₀ + 0 := by rw [← this, add_zero]
    exact add_left_cancel this
  funext b
  rw [hc, hc0, add_zero]
  rfl

/-- The one-to-one continuities act simply transitively on the ball: between any two readings there
is exactly one translational signal. -/
theorem continuities_simply_transitive (a b : Ball) : ∃! c : Ball, a + c = b := by
  refine ⟨b - a, by ring, fun c hc => ?_⟩
  rw [← hc]; ring

/-- The same rigidity at life states: a hand-preserving map commuting with the actual return is a
translation of the phase, one translation for each hand. -/
theorem life_continuity_forced (f : Life → Life) (hcomm : ∀ x, f (ballReturn x) = ballReturn (f x))
    (hhand : ∀ x, (f x).hand = x.hand) (x : Life) :
    f x = ⟨x.hand, x.phase + (f ⟨x.hand, 0⟩).phase⟩ := by
  have key : ∀ b : Ball, (f ⟨x.hand, ballStep b⟩).phase = ballStep (f ⟨x.hand, b⟩).phase := by
    intro b
    have h1 : f ⟨x.hand, ballStep b⟩ = ballReturn (f ⟨x.hand, b⟩) := hcomm ⟨x.hand, b⟩
    rw [h1, ballReturn_phase, ballStep]
  have hforced := ballStep_commuting_forced (fun b => (f ⟨x.hand, b⟩).phase) key x.phase
  have hx : (⟨x.hand, x.phase⟩ : Life) = x := rfl
  simp only [hx] at hforced
  have heta : f x = ⟨(f x).hand, (f x).phase⟩ := rfl
  rw [heta, hhand x, hforced]
  congr 1
  ring

/-! ## §4  Unitary curvature 1 to relative partition 1 -/

/-- The number of complete turns made by `n` translation steps of the ball. -/
def turns (n : ℕ) : ℕ := n / Fintype.card Ball

/-- **Unitary curvature 1**: a full closure of the ball is exactly one turn. -/
theorem turns_card_ball : turns (Fintype.card Ball) = 1 := by
  rw [turns, ball_card]

/-- The turn does close. -/
theorem curvature_closes : ballStep^[Fintype.card Ball] = (id : Ball → Ball) := by
  rw [ball_card]
  exact ballStep_period

/-- And no part of a turn closes: the curvature is a genuine unit. -/
theorem curvature_no_smaller_turn (n : ℕ) (h0 : 0 < n) (hn : n < Fintype.card Ball) :
    ballStep^[n] ≠ (id : Ball → Ball) := by
  rw [ball_card] at hn
  exact ballStep_ne_id_of_lt_four h0 hn

/-- One turn sweeps the whole ball: the orbit of any reading is everything. -/
theorem ball_orbit_covers (b : Ball) :
    (Finset.univ.image fun n : Fin 4 => ballStep^[(n : ℕ)] b) = Finset.univ := by
  refine Finset.eq_univ_iff_forall.2 (fun a => ?_)
  obtain ⟨n, hn, hna⟩ := ballStep_transitive b a
  exact Finset.mem_image.2 ⟨⟨n, hn⟩, Finset.mem_univ _, hna⟩

/-- **Relative partition 1**: the ball's translation classes form exactly one block, the hair. -/
theorem relative_partition_one : Fintype.card Hair = 1 := hair_card

/-- **Unitary curvature 1 to relative partition 1**: the one complete turn of the ball and the one
block of its relative partition are the same number. -/
theorem unitary_curvature_to_relative_partition :
    turns (Fintype.card Ball) = Fintype.card Hair := by
  rw [turns_card_ball, relative_partition_one]

/-- The closure-relative completion in one line: the curvature unit is the number of steps of the
ball, the partition unit is the hair, and every translation-invariant reading factors uniquely
through that one block. -/
theorem unifiable_natural_form {X : Type} (f : Ball → X) (hf : ∀ b, f (ballStep b) = f b) :
    (∀ b, hairLift f hf (hairMk b) = f b) ∧
      ∀ g : Hair → X, (∀ b, g (hairMk b) = f b) → g = hairLift f hf :=
  ⟨hairLift_mk f hf, fun g hg => hairLift_unique f hf g hg⟩

/-! ## §5  The intervening of relations -/

section Relations

variable {V : Type*}

/-- **The translational signal of truth at relations**: two configurations of a relation network
carry the same relations exactly when they differ by one global translation.  The separation
reading is a 1-to-1 continuity of the configuration modulo translation. -/
theorem separation_determines_up_to_translation [Nonempty V] (s t : Config V) :
    (∀ u v, separation s u v = separation t u v) ↔ ∃ c : ℤ, ∀ w, t w = s w + c := by
  constructor
  · intro h
    obtain ⟨v₀⟩ := ‹Nonempty V›
    refine ⟨t v₀ - s v₀, fun w => ?_⟩
    have hw := h w v₀
    unfold separation at hw
    omega
  · rintro ⟨c, hc⟩ u v
    unfold separation
    rw [hc u, hc v]
    ring

/-- Reading a relation the other way round is exactly the black mirror of it. -/
theorem relLife_swap_mirror (s : Config V) (u v : V) (h : s u ≠ s v) :
    relLife s v u = blackMirror (relLife s u v) := by
  have hhand : relHand s v u = (relHand s u v).inv := by
    rw [relHand_antisymm s u v h, Hand.inv_inv]
  have hball : relBall s v u = -relBall s u v := relBall_swap s u v
  show (⟨relHand s v u, relBall s v u⟩ : Life) = ⟨(relHand s u v).inv, -relBall s u v⟩
  rw [hhand, hball]

/-- Nothing absolute is read in the intervening of relations: a global translation moves no
relation at all. -/
theorem relations_shift_invariant (c : ℤ) (s : Config V) (u v : V) :
    relLife (shift c s) u v = relLife s u v ∧ relHair (shift c s) u v = relHair s u v :=
  ⟨relLife_shift c s u v, hair_one_sheaf _ _⟩

end Relations

/-! ## §6  The answer -/

/-- **NRRF801 in one statement.**

1. Both returns are one-to-one, and they are relatively translated: each is the inverse of the
   other up to exactly one hand flip, and in either order their composite is that flip alone.
2. They close equally: both after four steps, neither sooner.
3. The black mirror is a fixed-point-free involution that grows potential mirror life from actual
   life and back, one to one.
4. It conjugates each return into its own inverse — mirror life is the active temporal geometry run
   backwards — and it never leaves the hair closure.
5. Every one-to-one continuity of the ball is a translation, and one point of agreement forces
   total agreement: that is the translational signal of truth.
6. Unitary curvature 1 to relative partition 1: one full turn of the ball, one block of its
   relative partition, and these are the same number.
7. In the intervening of relations, the separation reading is exactly such a signal: the same
   relations everywhere iff one global translation apart. -/
theorem nrrf801_answer :
    (Function.Bijective ballReturn ∧ Function.Bijective hairReturn) ∧
    (∀ x : Life, hairReturn (ballReturn x) = handFlip x ∧
      ballReturn (hairReturn x) = handFlip x) ∧
    (ballReturn^[4] = (id : Life → Life) ∧ hairReturn^[4] = (id : Life → Life) ∧
      ∀ n : ℕ, 0 < n → n < 4 →
        ballReturn^[n] ≠ (id : Life → Life) ∧ hairReturn^[n] ≠ (id : Life → Life)) ∧
    (Function.Involutive blackMirror ∧ ∀ x : Life, blackMirror x ≠ x) ∧
    (∀ x : Life, (Potential (blackMirror x) ↔ Actual x) ∧ ∃! y : Life, blackMirror y = x) ∧
    (∀ x : Life, blackMirror (ballReturn (blackMirror x)) = ballReturnInv x ∧
      blackMirror (hairReturn (blackMirror x)) = hairReturnInv x ∧
      hairMk (blackMirror x).phase = hairMk x.phase) ∧
    (∀ f : Ball → Ball, OneToOneContinuity f ↔ ∃ c : Ball, ∀ b, f b = b + c) ∧
    (∀ f : Ball → Ball, OneToOneContinuity f → ∀ b₀ : Ball, f b₀ = b₀ → f = id) ∧
    (turns (Fintype.card Ball) = 1 ∧ Fintype.card Hair = 1 ∧
      turns (Fintype.card Ball) = Fintype.card Hair) ∧
    (∀ {V : Type} [Nonempty V] (s t : Config V),
      (∀ u v, separation s u v = separation t u v) ↔ ∃ c : ℤ, ∀ w, t w = s w + c) := by
  refine ⟨⟨ballReturn_bijective, hairReturn_bijective⟩, returns_relatively_translated,
    returns_close_equally, ⟨blackMirror_involutive, blackMirror_no_fixed_point⟩,
    fun x => ⟨(mirror_grows_potential x).1, mirror_life_unique x⟩,
    fun x => ⟨blackMirror_conj_ballReturn x, blackMirror_conj_hairReturn x, blackMirror_hair x⟩,
    oneToOneContinuity_iff_translation,
    fun f hf b₀ h => signal_of_truth hf h,
    ⟨turns_card_ball, relative_partition_one, unitary_curvature_to_relative_partition⟩,
    fun {V} _ s t => separation_determines_up_to_translation s t⟩

end NRRF801

/-! ## Axiom audit -/

#print axioms NRRF801.nrrf801_answer
#print axioms NRRF801.signal_of_truth
#print axioms NRRF801.separation_determines_up_to_translation
#print axioms NRRF801.life_continuity_forced
