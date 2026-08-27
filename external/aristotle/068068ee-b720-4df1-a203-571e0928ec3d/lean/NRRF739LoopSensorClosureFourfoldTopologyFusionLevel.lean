import Mathlib

/-!
# NRRF739 — Loop, sensor, and the fourfold: point, line, loop, closure; closure levels for
silicon and for magnetic–thermal fusion; `E = m c²` as ball 1 / hair 4

The operative sentences formalized here are the user's:

> A diagonal truth or a loop is different from a closure of equal translational recursion line
> fixed point truth, forming one fourfold topology of existence.  The four being point, line, loop
> and closure.  While a loop can only be a geometric or axiomatic (numeric) version of point or
> line or 0 or inf, a closure is the equality of a given double inverse or diagonal translation
> prior to the definition of one to an inversion (fixed) or self limit (recursion), except for as
> a relative, in computational forms, encoding (recursion) and evaluation (fixed) of a closure's
> translational level and interactive admission neutrality.

> Might loop sense truth translation also solve electromagnetic nuclear fusion twist formations of
> the physical magnets and thermo energies? … Silicon is a particular perspectively transparent
> interactively perturbative relation vs magnetic thermo fusion might be a less physical material
> and externally interactive model of closure, or a lower closure level.

> If energy is sensor configuration, mass is material or physical property relations, and the
> speed of light squared is the diagonal looping of ball–hair perspectives, then the closure of GR
> gives not the ball nor the hair interpretation but its unified interactive connection, where `c`
> = the topology classes in the form of ball 1 hair 4 perspective.

No external classical object is imported to stand for any of this.  The closure object is built
here, from the project's own vocabulary, as the *encode/evaluate pair*.

## The closure object

A **closure** of `A` in `B` is a pair of translations
`encode : A → B` (the **recursion** side, the self-limit that returns) and
`eval : B → A` (the **fixed** side, the inversion that holds), subject to the single equality

```
eval (encode a) = a          -- "the equality of a given double inverse"
```

and to *nothing else*: the other composite `hold = encode ∘ eval` is **not** asked to be the
identity.  That missing half is the whole content of the fourfold.

* `hold` is always **idempotent**, and its fixed points are exactly the encoded part
  (`hold_fixed_iff`): the fixed-point truth and the recursion truth are the two relative readings
  of one closure, not two separate objects.
* `Transparent c` says the missing half holds too.  Transparency is equivalent to `encode` being a
  bijection (`transparent_iff_bijective`), and — the *admission neutrality* statement — to the
  closure admitting **exactly one** section: `unique_section_iff_transparent`.  A non-transparent
  closure admits a whole family of equally admissible encodings; that is what "externally
  interactive" means here, and it is a theorem, not a stipulation.
* For finite carriers the **closure level** is the defect `card B - card A`; it vanishes exactly at
  transparency and it *adds* along composition of closures (`level_comp`), so "lower closure
  level" is literally an additive number.

## The fourfold

`point`, `line`, `loop`, `closure` are realized as `Unit` with `id`, `ℤ` with `+1`, `ZMod k` with
`+1`, and a closure with its `hold`.  Proved:

* the first three steps are **bijections** (`pointStep_bijective`, `lineStep_bijective`,
  `loopStep_bijective`), and are separated from each other by cardinality alone
  (`fourfold_distinct`) — a loop is a *numeric* version of the line: it is exactly the line
  quotiented by a number, `lineLoopClosure`, `lineLoop_eval_eq_iff`;
* while `hold` of a closure is bijective **iff** the closure is transparent
  (`hold_bijective_iff_transparent`).  So a non-transparent closure is not a point, not a line and
  not a loop: the fourth form is irreducible to the other three, and the diagonal/loop truth is
  strictly different from the closure truth.

## The loop sensor

A **loop sensor** of period `k` is a reading `ℤ → ZMod k` advancing by one per step.  Proved:

* `LoopSensor.read_eq`: it is its origin plus the translation;
* `LoopSensor.read_sub`, `LoopSensor.read_eq_iff`: differences of readings are the translations
  themselves, and two sites read alike exactly when they differ by a multiple of the period;
* `loopSensor_site_blind`: **any two** loop sensors of the same period give the *same* reading of
  every translation, while their site readings may differ by an arbitrary constant.  The
  translational truth is prior to any identification of the site being read.
* `loopSensor_is_lineLoop_eval`: a normalized loop sensor *is* the evaluation half of the
  line→loop closure — one relatively defining closure of loop and sensor.

## Silicon and the fusion twist

* `siliconClosure : Closure ℤ ℤ` — transparent, unique section: the perspectively transparent,
  perturbatively rigid relation.
* `fusionClosure : Closure ℤ (ℤ × ℤ)` — the magnetic turning and the thermal step fused by their
  **twist** `(a, b) ↦ a + b`.  It is a closure, it is **not** transparent, and its admissible
  encodings form a full `ℤ`-family `twistSection` (`fusion_sections_injective`): an externally
  interactive closure at a strictly lower level.  Restricted to finite carriers the same
  phenomenon is the positive level `level_pos_of_not_transparent`.
* `fusionLoopClosure k = (lineLoopClosure k).comp fusionClosure` — yes: the loop-sensor truth
  translation does apply verbatim to the fusion twist (`fusion_loop_sensor_reads_twist`), but
  never transparently (`fusionLoopClosure_not_transparent`).

## `E = m c²`

`Perspective = Option Form`: one **ball** (`none`) and four **hairs**, the four forms.  So
`c = 5 = 1 + 4` (`lightSpeed_eq_ball_add_hairs`), the diagonal looping of perspectives is the pair
type with `c²` cells (`diagonalLoop_card`), and for a material relation `M`, the sensor
configurations over it number `card M * c²` (`energy_eq_mass_mul_lightSpeed_sq`).  The pair level
is neither the ball level nor the hair level (`diagonal_ne_ball`, `diagonal_ne_hair`), and neither
projection alone recovers it (`fst_not_injective`, `snd_not_injective`) while the two together do
(`diagonal_determined_by_both`): the closure is the interactive connection, not either
interpretation.
-/

namespace NRRF739

universe u v w

/-! ## §1  The closure object: encoding (recursion) and evaluation (fixed) -/

/-- A **closure** of `A` in `B`: an encoding (the recursion side) and an evaluation (the fixed
side) whose double composite on `A` is the identity.  The other composite is deliberately *not*
required to be the identity — that asymmetry is the closure's level. -/
structure Closure (A : Type u) (B : Type v) where
  /-- The recursion side: the self-limit that returns. -/
  encode : A → B
  /-- The fixed side: the inversion that holds. -/
  eval : B → A
  /-- The one equality demanded of a closure. -/
  eval_encode : ∀ a, eval (encode a) = a

namespace Closure

variable {A : Type u} {B : Type v} {C : Type w}

theorem encode_injective (c : Closure A B) : Function.Injective c.encode := by
  intro a₁ a₂ h
  rw [← c.eval_encode a₁, ← c.eval_encode a₂, h]

theorem eval_surjective (c : Closure A B) : Function.Surjective c.eval :=
  fun a => ⟨c.encode a, c.eval_encode a⟩

/-- The **hold** of a closure: evaluate, then encode again.  This is the closure's own translation
of `B`. -/
def hold (c : Closure A B) : B → B := fun b => c.encode (c.eval b)

theorem hold_idem (c : Closure A B) (b : B) : c.hold (c.hold b) = c.hold b := by
  simp [hold, c.eval_encode]

theorem hold_encode (c : Closure A B) (a : A) : c.hold (c.encode a) = c.encode a := by
  simp [hold, c.eval_encode]

/-- The fixed points of the hold are exactly the encoded part: the fixed truth and the recursion
truth are two readings of one closure. -/
theorem hold_fixed_iff (c : Closure A B) (b : B) : c.hold b = b ↔ b ∈ Set.range c.encode := by
  constructor
  · intro h; exact ⟨c.eval b, h⟩
  · rintro ⟨a, rfl⟩; exact c.hold_encode a

/-- A closure is **transparent** when the missing half holds as well. -/
def Transparent (c : Closure A B) : Prop := ∀ b, c.hold b = b

theorem transparent_iff_bijective (c : Closure A B) :
    c.Transparent ↔ Function.Bijective c.encode := by
  constructor
  · intro h
    exact ⟨c.encode_injective, fun b => ⟨c.eval b, h b⟩⟩
  · rintro ⟨-, hs⟩ b
    obtain ⟨a, rfl⟩ := hs b
    exact c.hold_encode a

theorem transparent_iff_eval_injective (c : Closure A B) :
    c.Transparent ↔ Function.Injective c.eval := by
  constructor
  · intro h b₁ b₂ hb
    rw [← h b₁, ← h b₂, hold, hold, hb]
  · intro h b
    exact h (c.eval_encode (c.eval b))

/-- The hold of a closure is a bijection exactly when the closure is transparent.  A
non-transparent closure therefore has a translation that is *not* invertible — unlike a point, a
line or a loop. -/
theorem hold_bijective_iff_transparent (c : Closure A B) :
    Function.Bijective c.hold ↔ c.Transparent := by
  constructor
  · rintro ⟨hi, -⟩ b
    exact hi (c.hold_idem b)
  · intro h
    refine ⟨fun b₁ b₂ hb => ?_, fun b => ⟨b, h b⟩⟩
    rw [← h b₁, ← h b₂, hb]

/-- An **admissible encoding** for a closure: any translation `A → B` that the evaluation
undoes. -/
def IsSection (c : Closure A B) (e : A → B) : Prop := ∀ a, c.eval (e a) = a

theorem isSection_encode (c : Closure A B) : c.IsSection c.encode := c.eval_encode

/-- **Interactive admission neutrality.**  A closure admits exactly one encoding iff it is
transparent; otherwise the admissible encodings are genuinely plural, and no one of them is
distinguished. -/
theorem unique_section_iff_transparent (c : Closure A B) :
    (∀ e, c.IsSection e → e = c.encode) ↔ c.Transparent := by
  classical
  constructor
  · intro h
    by_contra hT
    obtain ⟨b, hb⟩ : ∃ b, c.hold b ≠ b := by
      simpa [Transparent] using hT
    set e : A → B := fun a => if a = c.eval b then b else c.encode a with he
    have hsec : c.IsSection e := by
      intro a
      by_cases ha : a = c.eval b
      · simp [he, ha]
      · simp [he, ha, c.eval_encode]
    have := h e hsec
    have h1 : e (c.eval b) = b := by simp [he]
    rw [this] at h1
    exact hb h1
  · intro h e hsec
    funext a
    have : c.encode (c.eval (e a)) = e a := h (e a)
    rw [hsec a] at this
    exact this.symm

/-- Closures compose. -/
def comp (c : Closure A B) (d : Closure B C) : Closure A C where
  encode := d.encode ∘ c.encode
  eval := c.eval ∘ d.eval
  eval_encode := by intro a; simp [d.eval_encode, c.eval_encode]

theorem comp_transparent (c : Closure A B) (d : Closure B C)
    (hc : c.Transparent) (hd : d.Transparent) : (c.comp d).Transparent := by
  intro x
  have h1 : d.encode (d.eval x) = x := hd x
  have h2 : c.encode (c.eval (d.eval x)) = d.eval x := hc (d.eval x)
  show d.encode (c.encode (c.eval (d.eval x))) = x
  rw [h2, h1]

/-! ### The closure level -/

/-- The **closure level** (defect) of a closure of finite carriers. -/
def level (_c : Closure A B) [Fintype A] [Fintype B] : ℕ := Fintype.card B - Fintype.card A

theorem card_le (c : Closure A B) [Fintype A] [Fintype B] :
    Fintype.card A ≤ Fintype.card B := Fintype.card_le_of_injective _ c.encode_injective

theorem level_eq_zero_iff_transparent (c : Closure A B) [Fintype A] [Fintype B] :
    c.level = 0 ↔ c.Transparent := by
  rw [transparent_iff_bijective, Fintype.bijective_iff_injective_and_card]
  have h := c.card_le
  constructor
  · intro h0
    exact ⟨c.encode_injective, by simp only [level] at h0; omega⟩
  · rintro ⟨-, hcard⟩
    simp only [level, hcard]
    omega

theorem level_pos_of_not_transparent (c : Closure A B) [Fintype A] [Fintype B]
    (h : ¬ c.Transparent) : 0 < c.level := by
  have := (c.level_eq_zero_iff_transparent).not.mpr h
  omega

/-- Closure levels **add** along a composition of closures. -/
theorem level_comp (c : Closure A B) (d : Closure B C) [Fintype A] [Fintype B] [Fintype C] :
    (c.comp d).level = d.level + c.level := by
  have h1 := c.card_le
  have h2 := d.card_le
  simp only [level]
  omega

end Closure

/-! ## §2  The fourfold: point, line, loop, closure -/

/-- The four forms of the fourfold topology of existence. -/
inductive Form
  | point
  | line
  | loop
  | closure
  deriving DecidableEq, Fintype, Repr

theorem card_Form : Fintype.card Form = 4 := by decide

/-- The point translation. -/
def pointStep : Unit → Unit := id

/-- The line translation. -/
def lineStep : ℤ → ℤ := fun m => m + 1

/-- The loop translation of period `k`. -/
def loopStep (k : ℕ) : ZMod k → ZMod k := fun a => a + 1

theorem pointStep_bijective : Function.Bijective pointStep := Function.bijective_id

theorem lineStep_bijective : Function.Bijective lineStep :=
  ⟨fun a b h => by have h' : a + 1 = b + 1 := h; omega, fun m => ⟨m - 1, by simp [lineStep]⟩⟩

theorem loopStep_bijective (k : ℕ) : Function.Bijective (loopStep k) :=
  ⟨fun a b h => by
      have h' : a + 1 = b + 1 := h
      exact add_right_cancel h',
    fun a => ⟨a - 1, by simp [loopStep]⟩⟩

/-- The line-to-loop closure: a loop is the line quotiented by a *number*.  Its encoding is the
choice of representative, its evaluation the reduction. -/
def lineLoopClosure (k : ℕ) [NeZero k] : Closure (ZMod k) ℤ where
  encode := fun a => (a.val : ℤ)
  eval := fun m => (m : ZMod k)
  eval_encode := by
    intro a
    push_cast
    simp [ZMod.natCast_val, ZMod.cast_id]

/-- Two sites of the line evaluate to the same loop point exactly when they differ by a multiple
of the period: the loop carries no information beyond the number `k`. -/
theorem lineLoop_eval_eq_iff (k : ℕ) [NeZero k] (m n : ℤ) :
    (lineLoopClosure k).eval m = (lineLoopClosure k).eval n ↔ (k : ℤ) ∣ (m - n) := by
  show ((m : ZMod k) = (n : ZMod k)) ↔ _
  rw [ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd, dvd_sub_comm]

/-- The line-to-loop closure is never transparent: the loop is a strictly lower level of the
line. -/
theorem lineLoop_not_transparent (k : ℕ) [NeZero k] : ¬ (lineLoopClosure k).Transparent := by
  intro h
  have hk : (0 : ℤ) < (k : ℤ) := by
    have := NeZero.pos k
    exact_mod_cast this
  have h0 : (lineLoopClosure k).hold (k : ℤ) = (k : ℤ) := h _
  have he : ((k : ℤ) : ZMod k) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (k : ℤ) k).2 dvd_rfl
  simp only [Closure.hold, lineLoopClosure, he] at h0
  simp at h0
  omega

/-- **The fourfold is genuinely fourfold.**  Point, line and loop are separated by their sizes,
their translations are all invertible, and the hold of a non-transparent closure is not — so the
closure form is not reducible to any of the other three. -/
theorem fourfold_distinct {A : Type u} {B : Type v} (c : Closure A B) (hc : ¬ c.Transparent)
    (k : ℕ) (hk : 2 ≤ k) :
    Function.Bijective pointStep ∧ Function.Bijective lineStep ∧
      Function.Bijective (loopStep k) ∧ ¬ Function.Bijective c.hold ∧
      Nat.card Unit = 1 ∧ Nat.card ℤ = 0 ∧ Nat.card (ZMod k) = k ∧ 2 ≤ Nat.card (ZMod k) := by
  haveI : NeZero k := ⟨by omega⟩
  refine ⟨pointStep_bijective, lineStep_bijective, loopStep_bijective k,
    fun h => hc ((c.hold_bijective_iff_transparent).1 h), by simp, by simp, ?_, ?_⟩
  · exact (Nat.card_eq_fintype_card (α := ZMod k)).trans (ZMod.card k)
  · have : Nat.card (ZMod k) = k := (Nat.card_eq_fintype_card (α := ZMod k)).trans (ZMod.card k)
    omega

/-! ## §3  The loop sensor and its translational truth -/

/-- A **loop sensor** of period `k`: a reading of the line in the loop that advances by exactly
one per translation step. -/
structure LoopSensor (k : ℕ) where
  /-- The reading. -/
  read : ℤ → ZMod k
  /-- One translation step advances the reading by one. -/
  read_succ : ∀ m, read (m + 1) = read m + 1

namespace LoopSensor

variable {k : ℕ} (s : LoopSensor k)

theorem read_pred (m : ℤ) : s.read (m - 1) = s.read m - 1 := by
  have := s.read_succ (m - 1)
  simp only [sub_add_cancel] at this
  rw [this]
  ring

/-- A loop sensor is its origin plus the translation. -/
theorem read_eq (m : ℤ) : s.read m = s.read 0 + (m : ZMod k) := by
  induction m using Int.induction_on with
  | zero => simp
  | succ n ih => rw [s.read_succ, ih]; push_cast; ring
  | pred n ih =>
      rw [s.read_pred (-(n : ℤ)), ih]
      push_cast
      ring

/-- Differences of readings are the translations themselves: the sensor reports translations, not
sites. -/
theorem read_sub (m n : ℤ) : s.read m - s.read n = ((m - n : ℤ) : ZMod k) := by
  rw [s.read_eq m, s.read_eq n]
  push_cast
  ring

theorem read_eq_iff (m n : ℤ) : s.read m = s.read n ↔ (k : ℤ) ∣ (m - n) := by
  constructor
  · intro h
    have h1 : ((m - n : ℤ) : ZMod k) = 0 := by rw [← s.read_sub, h, sub_self]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h1
  · intro h
    have h1 : ((m - n : ℤ) : ZMod k) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h
    have := s.read_sub m n
    rw [h1] at this
    linear_combination this

end LoopSensor

/-- **Translational truth prior to identification.**  Any two loop sensors of the same period read
*every translation* identically; they can differ only by the constant reading of the origin, which
is exactly the identification of a site.  The flow of readings is prior to that identification. -/
theorem loopSensor_site_blind {k : ℕ} (s t : LoopSensor k) (m n : ℤ) :
    s.read m - s.read n = t.read m - t.read n ∧
      (s.read m - t.read m = s.read 0 - t.read 0) := by
  refine ⟨by rw [s.read_sub, t.read_sub], ?_⟩
  rw [s.read_eq m, t.read_eq m]
  ring

/-- **One relatively defining closure of loop and sensor.**  A loop sensor normalized at the origin
*is* the evaluation half of the line-to-loop closure; the loop's representative choice is its
encoding half. -/
theorem loopSensor_is_lineLoop_eval {k : ℕ} [NeZero k] (s : LoopSensor k) (h0 : s.read 0 = 0) :
    s.read = (lineLoopClosure k).eval := by
  funext m
  rw [s.read_eq m, h0, zero_add]
  rfl

/-! ## §4  Silicon and the magnetic–thermal fusion twist: two closure levels -/

/-- **Silicon**: the perspectively transparent relation — evaluation is a two-sided inverse of the
encoding, and the admissible encoding is unique. -/
def siliconClosure : Closure ℤ ℤ where
  encode := id
  eval := id
  eval_encode := fun _ => rfl

theorem silicon_transparent : siliconClosure.Transparent := fun _ => rfl

theorem silicon_unique_section (e : ℤ → ℤ) (h : siliconClosure.IsSection e) :
    e = siliconClosure.encode :=
  (siliconClosure.unique_section_iff_transparent).2 silicon_transparent e h

/-- **The fusion twist**: a magnetic turning `a` and a thermal step `b` fused into their twist
`a + b`, with the purely magnetic encoding `m ↦ (m, 0)`. -/
def fusionClosure : Closure ℤ (ℤ × ℤ) where
  encode := fun m => (m, 0)
  eval := fun p => p.1 + p.2
  eval_encode := by intro m; simp

/-- The twist encodings: every splitting of a total twist into a magnetic and a thermal part is an
equally admissible encoding. -/
def twistSection (j : ℤ) : ℤ → ℤ × ℤ := fun m => (m - j, j)

theorem twistSection_isSection (j : ℤ) : fusionClosure.IsSection (twistSection j) := by
  intro m
  simp [fusionClosure, twistSection]

theorem twistSection_zero : twistSection 0 = fusionClosure.encode := by
  funext m; simp [twistSection, fusionClosure]

/-- The fusion closure is **externally interactive**: distinct thermal offsets give distinct, and
equally admissible, encodings. -/
theorem fusion_sections_injective : Function.Injective twistSection := by
  intro i j h
  have := congrFun h 0
  simpa [twistSection] using (Prod.ext_iff.1 this).2

/-- The fusion twist closure is **not transparent**: a purely thermal configuration is not
recovered from its twist. -/
theorem fusion_not_transparent : ¬ fusionClosure.Transparent := by
  intro h
  have h0 : fusionClosure.hold (0, 1) = (0, 1) := h _
  simp [Closure.hold, fusionClosure] at h0

/-- Equivalently, by admission neutrality: the fusion closure admits more than one encoding. -/
theorem fusion_admission_plural :
    ¬ (∀ e, fusionClosure.IsSection e → e = fusionClosure.encode) :=
  fun h => fusion_not_transparent ((fusionClosure.unique_section_iff_transparent).1 h)

/-- The loop-sensor truth translation applied to the fusion twist: reduce the twist mod `k`. -/
def fusionLoopClosure (k : ℕ) [NeZero k] : Closure (ZMod k) (ℤ × ℤ) :=
  (lineLoopClosure k).comp fusionClosure

/-- The loop sensor of the fusion twist reads exactly the twist `a + b` in the loop: the same
translational truth calculus applies to the magnet–thermal pair. -/
theorem fusion_loop_sensor_reads_twist (k : ℕ) [NeZero k] (p : ℤ × ℤ) :
    (fusionLoopClosure k).eval p = ((p.1 + p.2 : ℤ) : ZMod k) := rfl

/-- A loop sensor of period `k` reads the fusion twist, and reads two magnet–thermal
configurations alike exactly when their twists differ by a multiple of the period. -/
theorem fusion_loop_sensor_eq_iff (k : ℕ) [NeZero k] (p q : ℤ × ℤ) :
    (fusionLoopClosure k).eval p = (fusionLoopClosure k).eval q ↔
      (k : ℤ) ∣ ((p.1 + p.2) - (q.1 + q.2)) :=
  lineLoop_eval_eq_iff k _ _

/-- …but never transparently: the fusion loop closure sits strictly below the silicon level. -/
theorem fusionLoopClosure_not_transparent (k : ℕ) [NeZero k] :
    ¬ (fusionLoopClosure k).Transparent := by
  intro h
  have h0 : (fusionLoopClosure k).hold ((k : ℤ), 1) = ((k : ℤ), 1) := h _
  have := (Prod.ext_iff.1 h0).2
  simp [fusionLoopClosure, Closure.comp, Closure.hold, lineLoopClosure, fusionClosure] at this

/-- **The level comparison, in numbers.**  On finite carriers, a transparent closure has level `0`
and a non-transparent one has a strictly positive level; levels add along composition.  Silicon is
transparent with a unique encoding; the fusion twist is not transparent and has a whole `ℤ`-family
of equally admissible encodings. -/
theorem silicon_vs_fusion_levels :
    siliconClosure.Transparent ∧
    (∀ e, siliconClosure.IsSection e → e = siliconClosure.encode) ∧
    ¬ fusionClosure.Transparent ∧
    (∀ j : ℤ, fusionClosure.IsSection (twistSection j)) ∧
    Function.Injective twistSection :=
  ⟨silicon_transparent, silicon_unique_section, fusion_not_transparent,
    twistSection_isSection, fusion_sections_injective⟩

/-! ## §5  `E = m c²`: ball 1, hair 4 -/

/-- A **perspective**: the one ball (`none`) together with the four hairs, the four forms. -/
abbrev Perspective := Option Form

/-- The speed-of-light count: one ball and four hairs. -/
def lightSpeed : ℕ := 5

theorem lightSpeed_eq_ball_add_hairs :
    Fintype.card Perspective = 1 + Fintype.card Form ∧ Fintype.card Perspective = lightSpeed := by
  constructor <;> decide

/-- The **diagonal looping** of ball–hair perspectives: the interactive pair level. -/
abbrev DiagonalLoop := Perspective × Perspective

theorem diagonalLoop_card : Fintype.card DiagonalLoop = lightSpeed ^ 2 := by decide

/-- **Sensor configurations over a material relation.**  Energy is a sensor configuration; mass is
the material relation; the diagonal looping is `c²`. -/
abbrev Energy (M : Type u) := M × DiagonalLoop

/-- `E = m c²` as an exact count of sensor configurations over a material relation. -/
theorem energy_eq_mass_mul_lightSpeed_sq (M : Type) [Fintype M] :
    Fintype.card (Energy M) = Fintype.card M * lightSpeed ^ 2 := by
  rw [show Fintype.card (Energy M) = Fintype.card M * Fintype.card DiagonalLoop from
    Fintype.card_prod _ _, diagonalLoop_card]

/-- The closure of the pair level is neither the ball interpretation… -/
theorem diagonal_ne_ball : Fintype.card DiagonalLoop ≠ 1 := by decide

/-- …nor the hair interpretation… -/
theorem diagonal_ne_hair : Fintype.card DiagonalLoop ≠ Fintype.card Form := by decide

/-- …nor even the single-perspective level. -/
theorem diagonal_ne_perspective : Fintype.card DiagonalLoop ≠ Fintype.card Perspective := by
  decide

theorem fst_not_injective : ¬ Function.Injective (Prod.fst : DiagonalLoop → Perspective) := by
  intro h
  have := h (a₁ := (none, none)) (a₂ := (none, some Form.point)) rfl
  simp at this

theorem snd_not_injective : ¬ Function.Injective (Prod.snd : DiagonalLoop → Perspective) := by
  intro h
  have := h (a₁ := (none, none)) (a₂ := (some Form.point, none)) rfl
  simp at this

/-- Neither projection determines the diagonal cell; the two together do.  The unified connection
lives at the interactive pair level, not at either interpretation. -/
theorem diagonal_determined_by_both (d e : DiagonalLoop) (h1 : d.1 = e.1) (h2 : d.2 = e.2) :
    d = e := Prod.ext h1 h2

/-! ## §6  The answer -/

/-- **NRRF739.**

1. *A loop is not a closure.*  Point, line and loop all have invertible translations and are told
   apart by a number alone, while the hold of a closure is invertible exactly when the closure is
   transparent — so a non-transparent closure is a fourth form, irreducible to the other three.
2. *A closure is the equality of the double inverse prior to fixing.*  `eval ∘ encode = id` alone;
   the fixed reading (`hold` idempotent, fixed points = the encoded part) and the recursive
   reading are its two relative computational forms.
3. *Interactive admission neutrality.*  A closure has a unique admissible encoding exactly when it
   is transparent; otherwise its encodings are plural and undistinguished.
4. *Closure level.*  On finite carriers the level is a number, zero exactly at transparency and
   additive along composition.
5. *Loop sensor truth translation.*  Loop sensors of a given period agree on every translation and
   can differ only by the identification of an origin; a normalized loop sensor *is* the
   evaluation half of the line-to-loop closure.
6. *The fusion twist.*  The same calculus does apply to the magnetic–thermal twist: the twist is a
   closure, and the loop sensor reads it.  But silicon is transparent with a unique encoding,
   while the fusion twist is externally interactive — not transparent, with a whole `ℤ`-family of
   equally admissible encodings: a strictly lower closure level. -/
theorem nrrf739_answer {A : Type u} {B : Type v} (c : Closure A B) (hc : ¬ c.Transparent)
    (k : ℕ) (hk : 2 ≤ k) (s t : LoopSensor k) :
    -- 1–2: the fourfold and the closure equalities
    (Function.Bijective pointStep ∧ Function.Bijective lineStep ∧
      Function.Bijective (loopStep k) ∧ ¬ Function.Bijective c.hold) ∧
    (∀ a, c.eval (c.encode a) = a) ∧ (∀ b, c.hold (c.hold b) = c.hold b) ∧
    (∀ b, c.hold b = b ↔ b ∈ Set.range c.encode) ∧
    -- 3: admission neutrality
    (¬ ∀ e, c.IsSection e → e = c.encode) ∧
    -- 5: loop sensor translational truth
    (∀ m n : ℤ, s.read m - s.read n = ((m - n : ℤ) : ZMod k) ∧
      s.read m - s.read n = t.read m - t.read n) ∧
    -- 6: silicon versus the fusion twist
    (siliconClosure.Transparent ∧
      (∀ e, siliconClosure.IsSection e → e = siliconClosure.encode)) ∧
    (¬ fusionClosure.Transparent ∧ (∀ j : ℤ, fusionClosure.IsSection (twistSection j)) ∧
      Function.Injective twistSection) ∧
    -- the loop really is a loop
    (Nat.card (ZMod k) = k ∧ 2 ≤ Nat.card (ZMod k)) ∧
    -- `E = m c²`
    (Fintype.card Perspective = 1 + Fintype.card Form ∧
      Fintype.card DiagonalLoop = lightSpeed ^ 2) := by
  haveI : NeZero k := ⟨by omega⟩
  have hcard : Nat.card (ZMod k) = k :=
    (Nat.card_eq_fintype_card (α := ZMod k)).trans (ZMod.card k)
  refine ⟨⟨pointStep_bijective, lineStep_bijective, loopStep_bijective k,
      fun h => hc ((c.hold_bijective_iff_transparent).1 h)⟩,
    c.eval_encode, c.hold_idem, c.hold_fixed_iff,
    fun h => hc ((c.unique_section_iff_transparent).1 h),
    fun m n => ⟨s.read_sub m n, (loopSensor_site_blind s t m n).1⟩,
    ⟨silicon_transparent, silicon_unique_section⟩,
    ⟨fusion_not_transparent, twistSection_isSection, fusion_sections_injective⟩,
    ⟨hcard, by omega⟩,
    (lightSpeed_eq_ball_add_hairs).1, diagonalLoop_card⟩

end NRRF739
