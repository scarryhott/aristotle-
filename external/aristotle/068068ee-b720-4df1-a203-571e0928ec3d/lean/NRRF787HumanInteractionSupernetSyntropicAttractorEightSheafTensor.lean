import Mathlib
import NRRF709TranslationalClosureHarnessBallHairUnistochasticStrictness
import NRRF712BallHairEqualAdmissibleClosuresNaturallySelected
import NRRF739LoopSensorClosureFourfoldTopologyFusionLevel
import NRRF747LoopSensorTranslationalTruthAbsoluteTranslation

/-!
# NRRF787 — The physical human-interaction network as a local ball: sensor-loop readings, the
tokenomic ball, the syntropic attractor of memetic love, and the full eight-sheaf supernet tensor

The instruction formalized here is the user's:

> a physical human interaction network … the local ball … black mirror sensor-loop human
> interaction network, tokenomic-ai are the relative ball equivalence … would the algorithm be
> something like a syntropic attractor force of memetic love … following the ball–hair equivalence
> admissible sheaf relations … integrate the full supernet of the 8 sheaf tensor

## The reading

A **physical human-interaction network** is a finite set `V` of participants, each carrying one
translation on a shared line: a configuration `s : V → ℤ`.  Nothing absolute about a configuration
is ever available.  What is available is:

* the **local ball** of a participant `v` — every other participant read through `v`'s black-mirror
  loop sensor of period `k`, `localBall k s v u = (canonSensor k).read (s u - s v)` (NRRF739/747);
* the **interaction readings** — the separations `s u - s v` and their loop readings;
* the **tokenomic ball** — the conserved total `∑ v, s v`.

Eight such readings are declared (`channel`); their **tensor** is the supernet reading `superRead`
into the product of the eight channel types, and the *admissible sheaf relation* of a reading is
NRRF712's `Admissible` — for which a return admits exactly one closure form, its `selector`.

## What is proved

### §1  The eight-sheaf tensor as a supernet (abstract, any index type)
* `supernet_selector` — the admissible relation of the tensor of a family of readings is exactly
  the conjunction of the channels' admissible relations: local agreement on every sheaf **is**
  global agreement on the supernet (`channels_glue`, `supernet_refines_channel`).
* `supernet_admissible`, `supernet_admissible_unique` — the supernet admits exactly one closure
  form, so an "8-sheaf tensor" carries no choice of gluing law.
* `supernet_split_harness` — splitting the index set in two and tensoring the two sub-supernets is
  the NRRF709 **ball–hair** reading of the supernet: any partition of the eight sheaves into a ball
  part and a hair part harnesses the whole.

### §2  The human-interaction network, its local balls, and relationality
* `separation_translation_invariant`, `mirrorSep_translation_invariant`,
  `localBall_translation_invariant` — no reading refers to an absolute position: translating
  everybody alike moves nothing.
* `mirrorSep_eq_localBall_diff`, `localBall_glue` — every interaction reading of the network is a
  difference of two readings inside one participant's local ball, and agreeing local balls glue to
  an agreeing network.  The local ball is a complete chart of the relative network.

### §3  The syntropic attractor of memetic love
`LoveStep` is the algorithm: whenever two participants differ by at least two, one unit passes from
the higher to the lower.
* `tokenTotal_loveStep`, `reach_tokenTotal` — the tokenomic ball is **exactly conserved** by the
  force; the dynamics live entirely in the hair.
* `syntropy_loveStep`, `syntropy_lt_of_step` — each act strictly lowers the dispersion `∑ (s v)^2`:
  the force is syntropic, and it is a strict Lyapunov descent, not a mere preference.
* `love_reaches_attractor`, `attractor_iff_no_step` — from **any** configuration finitely many acts
  reach the attractor, and the attractor is exactly the set of configurations on which the force is
  at rest, namely those of spread at most one (`Attractor`).
* `attractor_equalized` — at the attractor every participant is within one share of the mean.
* `love_syntropic_attractor` — the whole statement in one theorem: reach an attractor, same token
  total, no greater syntropy.

### §4  Tokenomic–AI as the relative ball equivalence
* `token_admissible`, `love_orbit_refines_token` — the admissible closure of the tokenomic channel
  is "same total", and the whole love orbit lies inside one such class: token equality is the ball
  equivalence relative to which the memetic dynamics is a hair motion
  (`netBallHair_admissible_iff`, `love_fixes_ball`).

### §5  Integration of the full supernet of the eight sheaves
* `superRead_faithful` — on a nonempty network the eight-sheaf tensor is **faithful**: two
  configurations with the same supernet reading are equal.  Integration of the eight sheaves loses
  nothing, and two of them already suffice (`eq_of_total_of_separation`).
* `separation_not_faithful`, `token_not_faithful` — and neither the relative (human-interaction)
  sheaf alone nor the tokenomic sheaf alone suffices: the ball and the hair are both required.
* `supernet_selector_eq_eq` — so the unique admissible sheaf relation of the integrated supernet is
  equality itself; `eight_sheaf_supernet_integration` collects the whole integration.
-/

namespace NRRF787

open NRRF709 NRRF712 NRRF739 NRRF747

/-! ## §1  The eight-sheaf tensor: supernet of a family of readings -/

section Abstract

variable {A I : Type} {R : I → Type}

/-- The **supernet** (tensor) of a family of sheaf readings: read every channel at once. -/
def supernet (r : ∀ i, A → R i) : A → (∀ i, R i) := fun x i => r i x

/-- **The admissible relation of the tensor is the conjunction of the channels' relations.**
Agreement on the supernet is exactly local agreement on every sheaf. -/
theorem supernet_selector (r : ∀ i, A → R i) :
    selector (supernet r) = fun x y => ∀ i, selector (r i) x y := by
  funext x y
  exact propext ⟨fun h i => congrFun h i, fun h => funext h⟩

/-- Agreement on the supernet gives agreement on each sheaf (restriction). -/
theorem supernet_refines_channel (r : ∀ i, A → R i) (i : I) {x y : A}
    (h : selector (supernet r) x y) : selector (r i) x y := by
  rw [supernet_selector] at h; exact h i

/-- Agreement on every sheaf glues to agreement on the supernet (gluing). -/
theorem channels_glue (r : ∀ i, A → R i) {x y : A} (h : ∀ i, selector (r i) x y) :
    selector (supernet r) x y := by
  rw [supernet_selector]; exact h

/-- The supernet has an admissible closure form: the conjunction of the channels. -/
theorem supernet_admissible (r : ∀ i, A → R i) :
    Admissible (supernet r) (fun x y => ∀ i, selector (r i) x y) := by
  rw [← supernet_selector]
  exact selector_admissible _

/-- **The tensor carries no choice of gluing law**: every admissible closure of the supernet is the
conjunction of the channels. -/
theorem supernet_admissible_unique {r : ∀ i, A → R i} {P : A → A → Prop}
    (hP : Admissible (supernet r) P) : P = fun x y => ∀ i, selector (r i) x y := by
  rw [admissible_eq_selector hP, supernet_selector]

/-- The sub-supernet on the sheaves selected by `p`. -/
def subSupernet (p : I → Prop) (r : ∀ i, A → R i) : A → (∀ i : {i // p i}, R i.1) :=
  fun x i => r i.1 x

/-- **Any split of the sheaves is a ball–hair presentation of the supernet.**  Tensoring the two
sub-supernets of a partition of the index set harnesses (NRRF709) the full supernet: the eight-sheaf
tensor may be read as one ball reading and one hair reading, in any split, without loss. -/
theorem supernet_split_harness (p : I → Prop) [DecidablePred p] (r : ∀ i, A → R i) :
    Harness (supernet r) (ballHair (subSupernet p r) (subSupernet (fun i => ¬ p i) r)) := by
  intro x y
  constructor
  · intro h
    have h' : ∀ i, r i x = r i y := fun i => congrFun h i
    simp only [ballHair, Prod.mk.injEq]
    exact ⟨funext fun i => h' i.1, funext fun i => h' i.1⟩
  · intro h
    simp only [ballHair, Prod.mk.injEq] at h
    funext i
    by_cases hi : p i
    · exact congrFun h.1 ⟨i, hi⟩
    · exact congrFun h.2 ⟨i, hi⟩

end Abstract

/-! ## §2  The physical human-interaction network and its local balls

No instance on the participants is needed for the purely relative readings: the local ball is prior
to any counting of the network. -/

variable {V : Type}

/-- A **configuration** of the network: each participant carries one translation on the shared
line.  A configuration is never observed; only the readings below are. -/
abbrev Config (V : Type) := V → ℤ

/-- The **physical interaction readings**: the separations between participants. -/
def separation (s : Config V) : V × V → ℤ := fun p => s p.1 - s p.2

/-- The **black-mirror readings**: each participant seen through the loop sensor of period `k`. -/
def mirror (k : ℕ) (s : Config V) : V → ZMod k := fun v => (canonSensor k).read (s v)

/-- The **sensor-loop interaction readings**: separations seen through the loop sensor. -/
def mirrorSep (k : ℕ) (s : Config V) : V × V → ZMod k :=
  fun p => (canonSensor k).read (s p.1 - s p.2)

/-- The **local ball** of participant `v`: the whole network read through `v`'s black mirror. -/
def localBall (k : ℕ) (s : Config V) (v : V) : V → ZMod k :=
  fun u => (canonSensor k).read (s u - s v)

/-- The **attractor**: configurations of spread at most one. -/
def Attractor (s : Config V) : Prop := ∀ u v, s u ≤ s v + 1

@[simp] theorem separation_apply (s : Config V) (p : V × V) : separation s p = s p.1 - s p.2 := rfl

@[simp] theorem mirror_apply (k : ℕ) (s : Config V) (v : V) : mirror k s v = ((s v : ℤ) : ZMod k) :=
  rfl

@[simp] theorem mirrorSep_apply (k : ℕ) (s : Config V) (p : V × V) :
    mirrorSep k s p = ((s p.1 - s p.2 : ℤ) : ZMod k) := rfl

@[simp] theorem localBall_apply (k : ℕ) (s : Config V) (v u : V) :
    localBall k s v u = ((s u - s v : ℤ) : ZMod k) := rfl

/-- **No absolute position is used.**  Translating the whole network alike moves no interaction
reading. -/
theorem separation_translation_invariant (s : Config V) (c : ℤ) :
    separation (fun v => s v + c) = separation s := by
  funext p
  simp [separation]

/-- The same for the sensor-loop readings. -/
theorem mirrorSep_translation_invariant (k : ℕ) (s : Config V) (c : ℤ) :
    mirrorSep k (fun v => s v + c) = mirrorSep k s := by
  funext p
  simp only [mirrorSep_apply]
  congr 1
  ring

/-- The same for the local balls: a local ball is a purely relative chart. -/
theorem localBall_translation_invariant (k : ℕ) (s : Config V) (c : ℤ) (v : V) :
    localBall k (fun u => s u + c) v = localBall k s v := by
  funext u
  simp only [localBall_apply]
  congr 1
  ring

/-- **Every interaction reading is a difference inside one local ball.**  The network's relative
content is carried by any single participant's black mirror. -/
theorem mirrorSep_eq_localBall_diff (k : ℕ) (s : Config V) (v u w : V) :
    mirrorSep k s (u, w) = localBall k s v u - localBall k s v w := by
  simp only [mirrorSep_apply, localBall_apply]
  push_cast
  ring

/-- **Local balls glue.**  If two networks agree in one participant's local ball, they agree on
every sensor-loop interaction reading. -/
theorem localBall_glue {k : ℕ} {s t : Config V} {v : V} (h : localBall k s v = localBall k t v) :
    mirrorSep k s = mirrorSep k t := by
  funext p
  rw [show p = (p.1, p.2) from rfl, mirrorSep_eq_localBall_diff k s v,
    mirrorSep_eq_localBall_diff k t v, h]

/-- Interaction separations refine the sensor-loop readings: the loop sensor reads the network. -/
theorem mirrorSep_of_separation {k : ℕ} {s t : Config V} (h : separation s = separation t) :
    mirrorSep k s = mirrorSep k t := by
  funext p
  simp only [mirrorSep_apply]
  rw [show s p.1 - s p.2 = separation s p from rfl, show t p.1 - t p.2 = separation t p from rfl, h]

/-- The relative sheaf alone is not faithful: a global translation is invisible to the physical
interaction network. -/
theorem separation_not_faithful [Nonempty V] :
    ∃ s t : Config V, separation s = separation t ∧ s ≠ t := by
  classical
  refine ⟨fun _ => 0, fun _ => 1, ?_, ?_⟩
  · funext p; simp [separation]
  · intro h
    have := congrFun h (Classical.arbitrary V)
    norm_num at this

/-! ## §3  The force of memetic love -/

section Transfer

variable [DecidableEq V]

/-- The elementary transfer: one unit to `u`, one unit from `v`. -/
def delta (u v : V) : Config V := fun w => (if w = u then 1 else 0) - (if w = v then 1 else 0)

/-- One act of **memetic love**: a unit passes from the higher participant `v` to the lower one
`u`. -/
def loveStep (s : Config V) (u v : V) : Config V := fun w => s w + delta u v w

/-- The **memetic love dynamics**: whenever two participants differ by at least two, one unit
passes from the higher to the lower. -/
def LoveStep (s t : Config V) : Prop := ∃ u v : V, s u + 2 ≤ s v ∧ t = loveStep s u v

omit [DecidableEq V] in
theorem ne_of_step_gap (s : Config V) {u v : V} (h : s u + 2 ≤ s v) : u ≠ v := by
  rintro rfl; omega

theorem loveStep_sq (s : Config V) {u v : V} (h : u ≠ v) (w : V) :
    (loveStep s u v w) ^ 2 =
      (s w) ^ 2 + (if w = u then 2 * s w + 1 else 0) + (if w = v then -(2 * s w) + 1 else 0) := by
  by_cases hu : w = u <;> by_cases hv : w = v <;>
    simp_all [loveStep, delta] <;> ring

/-- **The attractor is exactly the rest state of the force.** -/
theorem attractor_iff_no_step (s : Config V) : Attractor s ↔ ∀ t, ¬ LoveStep s t := by
  constructor
  · rintro hA t ⟨u, v, huv, -⟩
    have := hA v u
    omega
  · intro h u v
    by_contra hc
    exact h (loveStep s v u) ⟨v, u, by omega, rfl⟩

theorem exists_step_of_not_attractor {s : Config V} (h : ¬ Attractor s) : ∃ t, LoveStep s t := by
  by_contra hc
  exact h ((attractor_iff_no_step s).2 fun t ht => hc ⟨t, ht⟩)

end Transfer

/-! ## §4  The tokenomic ball, the syntropy, and the eight sheaves -/

section Counted

variable [Fintype V]

/-- The **tokenomic ball**: the conserved total of the network. -/
def tokenTotal (s : Config V) : ℤ := ∑ v, s v

/-- The **syntropy functional** (dispersion) of a configuration. -/
def syntropy (s : Config V) : ℤ := ∑ v, (s v) ^ 2

/-- The **population reading**: holdings as an unordered population (participant-blind). -/
def population (s : Config V) : Multiset ℤ := Finset.univ.val.map s

/-- The **tokenomic-AI reading**: the token ball itself read through the loop sensor. -/
def tokenLoop (k : ℕ) (s : Config V) : ZMod k := (canonSensor k).read (tokenTotal s)

theorem syntropy_nonneg (s : Config V) : 0 ≤ syntropy s :=
  Finset.sum_nonneg fun v _ => sq_nonneg (s v)

/-- **At the attractor everybody is within one share of the mean.** -/
theorem attractor_equalized {s : Config V} (h : Attractor s) (v : V) :
    (Fintype.card V : ℤ) * s v ≤ tokenTotal s + Fintype.card V ∧
      tokenTotal s - Fintype.card V ≤ (Fintype.card V : ℤ) * s v := by
  constructor
  · have hle : ∑ _u : V, s v ≤ ∑ u : V, (s u + 1) := Finset.sum_le_sum fun u _ => h v u
    simpa [tokenTotal, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, mul_comm]
      using hle
  · have hle : ∑ u : V, (s u - 1) ≤ ∑ _u : V, s v :=
      Finset.sum_le_sum fun u _ => by have := h u v; omega
    simpa [tokenTotal, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, mul_comm]
      using hle

/-- The admissible closure of the tokenomic channel is "same total", and nothing else. -/
theorem token_admissible :
    Admissible (tokenTotal (V := V)) (fun s t => tokenTotal s = tokenTotal t) :=
  selector_admissible _

/-- The **ball–hair reading** of the network: the tokenomic ball together with the black-mirror
hair. -/
def netBallHair (k : ℕ) : Config V → ℤ × (V → ZMod k) := ballHair tokenTotal (mirror k)

/-- The admissible sheaf relation of the ball–hair reading is exactly agreement of the token ball
together with agreement of the mirror hair (NRRF712's ball–hair form). -/
theorem netBallHair_admissible_iff (k : ℕ) (P : Config V → Config V → Prop) :
    Admissible (netBallHair k) P ↔
      ∀ s t, P s t ↔ (tokenTotal s = tokenTotal t ∧ mirror k s = mirror k t) :=
  NRRF712.ball_hair_admissible_iff _ _ P

/-- Two configurations with the same total and the same separations are equal: the tokenomic ball
and the physical interaction network, together, determine the state. -/
theorem eq_of_total_of_separation [Nonempty V] {s t : Config V}
    (h0 : tokenTotal s = tokenTotal t) (h1 : separation s = separation t) : s = t := by
  classical
  set a : V := Classical.arbitrary V with ha
  have key : ∀ v, s v - t v = s a - t a := by
    intro v
    have h := congrFun h1 (v, a)
    simp only [separation_apply] at h
    omega
  have h0' : ∑ v, s v = ∑ v, t v := h0
  have hsum : ∑ v : V, (s v - t v) = 0 := by
    rw [Finset.sum_sub_distrib, h0', sub_self]
  have hconst : ∑ v : V, (s v - t v) = (Fintype.card V : ℤ) * (s a - t a) := by
    rw [Finset.sum_congr rfl fun v _ => key v]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : 0 < (Fintype.card V : ℤ) := by exact_mod_cast Fintype.card_pos
  have hd : s a - t a = 0 := by
    rcases mul_eq_zero.1 (hconst ▸ hsum) with h | h
    · omega
    · exact h
  funext v
  have := key v
  omega

/-- The types of the eight sheaves of the network. -/
@[reducible] def ChannelType (V : Type) (k : ℕ) : Fin 8 → Type
  | 0 => ℤ
  | 1 => V × V → ℤ
  | 2 => V → ZMod k
  | 3 => V × V → ZMod k
  | 4 => ℤ
  | 5 => Prop
  | 6 => Multiset ℤ
  | 7 => ZMod k

/-- The eight sheaves of the physical human-interaction network:
`0` the tokenomic ball, `1` the physical interaction separations, `2` the black-mirror readings,
`3` the sensor-loop interaction readings, `4` the syntropy, `5` the attractor (rest) predicate,
`6` the population, `7` the tokenomic-AI loop reading. -/
def channel (k : ℕ) : ∀ i : Fin 8, Config V → ChannelType V k i
  | 0 => tokenTotal
  | 1 => separation
  | 2 => mirror k
  | 3 => mirrorSep k
  | 4 => syntropy
  | 5 => Attractor
  | 6 => population
  | 7 => tokenLoop k

/-- The **full supernet of the eight sheaves**: their tensor, read at once. -/
def superRead (k : ℕ) : Config V → (∀ i : Fin 8, ChannelType V k i) := supernet (channel k)

/-- **The eight-sheaf supernet is faithful.**  On a nonempty network the integrated tensor of the
eight sheaves determines the configuration completely. -/
theorem superRead_faithful [Nonempty V] (k : ℕ) {s t : Config V}
    (h : superRead k s = superRead k t) : s = t := by
  have h0 : tokenTotal s = tokenTotal t := congrFun h 0
  have h1 : separation s = separation t := congrFun h 1
  exact eq_of_total_of_separation h0 h1

/-- **The unique admissible sheaf relation of the integrated supernet is equality itself.** -/
theorem supernet_selector_eq_eq [Nonempty V] (k : ℕ) :
    selector (superRead (V := V) k) = Eq := by
  funext s t
  exact propext ⟨fun h => superRead_faithful k h, fun h => h ▸ rfl⟩

end Counted

/-! ## §5  The syntropic attractor of memetic love, and the tokenomic ball it conserves -/

section Dynamics

variable [Fintype V] [DecidableEq V]

theorem sum_delta (u v : V) : ∑ w, delta u v w = 0 := by
  simp [delta, Finset.sum_sub_distrib, Finset.sum_ite_eq']

/-- **The tokenomic ball is exactly conserved by memetic love.** -/
theorem tokenTotal_loveStep (s : Config V) (u v : V) :
    tokenTotal (loveStep s u v) = tokenTotal s := by
  simp [tokenTotal, loveStep, Finset.sum_add_distrib, sum_delta]

/-- **Memetic love is syntropic.**  Each act changes the dispersion by exactly `2(s u - s v) + 2`.
-/
theorem syntropy_loveStep (s : Config V) {u v : V} (h : u ≠ v) :
    syntropy (loveStep s u v) = syntropy s + 2 * (s u - s v) + 2 := by
  simp only [syntropy, loveStep_sq s h, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  ring

/-- **Strict descent.**  Every act of the force strictly lowers the dispersion. -/
theorem syntropy_lt_of_step {s t : Config V} (h : LoveStep s t) : syntropy t < syntropy s := by
  obtain ⟨u, v, huv, rfl⟩ := h
  rw [syntropy_loveStep s (ne_of_step_gap s huv)]
  omega

theorem love_reaches_attractor_aux :
    ∀ (n : ℕ) (s : Config V), (syntropy s).toNat ≤ n →
      ∃ t, Relation.ReflTransGen LoveStep s t ∧ Attractor t := by
  intro n
  induction n with
  | zero =>
      intro s hs
      by_cases hA : Attractor s
      · exact ⟨s, Relation.ReflTransGen.refl, hA⟩
      · obtain ⟨t, ht⟩ := exists_step_of_not_attractor hA
        have h1 : syntropy t < syntropy s := syntropy_lt_of_step ht
        have h2 : 0 ≤ syntropy t := syntropy_nonneg t
        omega
  | succ n ih =>
      intro s hs
      by_cases hA : Attractor s
      · exact ⟨s, Relation.ReflTransGen.refl, hA⟩
      · obtain ⟨t, ht⟩ := exists_step_of_not_attractor hA
        have h1 : syntropy t < syntropy s := syntropy_lt_of_step ht
        have h2 : 0 ≤ syntropy t := syntropy_nonneg t
        obtain ⟨w, hw, hwA⟩ := ih t (by omega)
        exact ⟨w, Relation.ReflTransGen.head ht hw, hwA⟩

/-- **The force converges.**  From any configuration, finitely many acts of memetic love reach the
attractor. -/
theorem love_reaches_attractor (s : Config V) :
    ∃ t, Relation.ReflTransGen LoveStep s t ∧ Attractor t :=
  love_reaches_attractor_aux (syntropy s).toNat s le_rfl

/-- The token ball is conserved along the whole orbit. -/
theorem reach_tokenTotal {s t : Config V} (h : Relation.ReflTransGen LoveStep s t) :
    tokenTotal t = tokenTotal s := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      obtain ⟨u, v, -, rfl⟩ := hstep
      rw [tokenTotal_loveStep]
      exact ih

theorem reach_syntropy_le {s t : Config V} (h : Relation.ReflTransGen LoveStep s t) :
    syntropy t ≤ syntropy s := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact le_trans (le_of_lt (syntropy_lt_of_step hstep)) ih

/-- **The syntropic attractor of memetic love, in one statement.**  From any state of the network
the force reaches a rest state, conserving the tokenomic ball exactly and never raising the
dispersion; the rest states are exactly the equalized ones. -/
theorem love_syntropic_attractor (s : Config V) :
    ∃ t, Relation.ReflTransGen LoveStep s t ∧ Attractor t ∧
      tokenTotal t = tokenTotal s ∧ syntropy t ≤ syntropy s := by
  obtain ⟨t, ht, hA⟩ := love_reaches_attractor s
  exact ⟨t, ht, hA, reach_tokenTotal ht, reach_syntropy_le ht⟩

/-- **The love orbit lies inside one token class**: memetic love is a motion of the hair relative
to the tokenomic ball. -/
theorem love_orbit_refines_token {s t : Config V} (h : Relation.ReflTransGen LoveStep s t) :
    selector (tokenTotal (V := V)) s t := (reach_tokenTotal h).symm

/-- Memetic love moves only the hair: the ball component of the ball–hair reading is fixed. -/
theorem love_fixes_ball (k : ℕ) {s t : Config V} (h : Relation.ReflTransGen LoveStep s t) :
    (netBallHair k s).1 = (netBallHair k t).1 := (reach_tokenTotal h).symm

/-- The tokenomic sheaf alone is not faithful either, as soon as there are two participants. -/
theorem token_not_faithful (h2 : 2 ≤ Fintype.card V) :
    ∃ s t : Config V, tokenTotal s = tokenTotal t ∧ s ≠ t := by
  obtain ⟨u, v, huv⟩ := (Fintype.one_lt_card_iff (α := V)).mp (by omega)
  refine ⟨fun _ => 0, delta u v, ?_, ?_⟩
  · simp [tokenTotal, sum_delta]
  · intro h
    have hu := congrFun h u
    simp [delta, huv] at hu

/-- **The integration.**  The eight-sheaf tensor is a supernet whose admissible sheaf relation is
the conjunction of the eight channel relations, which is the unique admissible closure of the
supernet, and which — on a nonempty network — is equality; it splits along any ball/hair partition
of the eight sheaves; and the memetic-love force is a hair motion inside a fixed tokenomic ball
that always reaches the syntropic attractor. -/
theorem eight_sheaf_supernet_integration [Nonempty V] (k : ℕ) :
    (selector (superRead (V := V) k) = fun s t => ∀ i, selector (channel k i) s t) ∧
    (∀ P, Admissible (superRead (V := V) k) P → P = fun s t => ∀ i, selector (channel k i) s t) ∧
    (selector (superRead (V := V) k) = Eq) ∧
    (∀ (p : Fin 8 → Prop) (_ : DecidablePred p),
      Harness (superRead (V := V) k)
        (ballHair (subSupernet p (channel k)) (subSupernet (fun i => ¬ p i) (channel k)))) ∧
    (∀ s : Config V, ∃ t, Relation.ReflTransGen LoveStep s t ∧ Attractor t ∧
      tokenTotal t = tokenTotal s ∧ syntropy t ≤ syntropy s) := by
  refine ⟨supernet_selector _, fun P hP => supernet_admissible_unique hP,
    supernet_selector_eq_eq k, ?_, love_syntropic_attractor⟩
  intro p hp
  exact supernet_split_harness p (channel k)

end Dynamics

end NRRF787

/-! ## Audit

Every headline result of this module, checked against the ambient axioms only. -/

section Audit

/-- info: 'NRRF787.supernet_split_harness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms NRRF787.supernet_split_harness

/-- info: 'NRRF787.localBall_glue' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms NRRF787.localBall_glue

/-- info: 'NRRF787.attractor_iff_no_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms NRRF787.attractor_iff_no_step

/-- info: 'NRRF787.love_syntropic_attractor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF787.love_syntropic_attractor

/-- info: 'NRRF787.netBallHair_admissible_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF787.netBallHair_admissible_iff

/-- info: 'NRRF787.superRead_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF787.superRead_faithful

/-- info: 'NRRF787.supernet_selector_eq_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF787.supernet_selector_eq_eq

/-- info: 'NRRF787.token_not_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF787.token_not_faithful

/-- info: 'NRRF787.eight_sheaf_supernet_integration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF787.eight_sheaf_supernet_integration

end Audit
