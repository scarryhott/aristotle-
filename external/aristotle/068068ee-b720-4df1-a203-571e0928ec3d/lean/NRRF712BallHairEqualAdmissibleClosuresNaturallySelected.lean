import Mathlib
import NRRF709TranslationalClosureHarnessBallHairUnistochasticStrictness
import NRRF710NaturalTranslationalEqualityPriorZeroInfinityClosure
import NRRF711OnlyTranslationalProofNaturallyUniversallyCloses

/-!
# NRRF712 — Ball–hair returns are equal admissible closures, naturally selected

The request formalized here is:

> ball hair returns are equal admissible closures, where the selected closure form of maze
> partition and unitary curvature is naturally selected; further this applies to the `0 ↔ ∞`
> closure and all other derived forms, where *natural* is the translational equality selector.

## Reading of the words

* **admissible closure of a return.**  A closure form on occurrences is a relation
  `P : A → A → Prop`.  It is *admissible* for a return `r : A → R` when some criterion that
  naturally universally closes (NRRF711 `NaturalUniversal`) delivers exactly `P` on that
  presentation.  So admissibility is not a stipulation about `P`: it is the demand that `P` be the
  verdict of a criterion that closes, does not consult the parametrization of the occurrences, does
  not consult the names in the return language, and is not vacuous.

* **natural = the translational equality selector.**  By NRRF711 there is exactly one such
  criterion, `r x = r y`.  Naturality therefore *is* a selector: given a return, it selects the
  translational equality at the resolution of that return, `selector r`.  This is `Admissible`'s
  only solution (`admissible_iff_kernel`).

* **equal admissible closures.**  Any two admissible closures of one return are literally the same
  relation (`admissible_closures_are_equal`), and two returns have the same admissible closures
  exactly when they are an NRRF709 harness — same induced partition — in which case there is a
  unique invertible dictionary between their return languages
  (`equal_admissible_closures_iff_harness`, `unique_dictionary_of_equal_admissible_closures`).

* **derived form.**  A closure form is *derived* when it is read off some evaluation
  `e : A → S` as `e x = e y` (`readingForm`).  Maze partition (cells of a maze), unitary curvature
  (holonomy in a unitary frame) and the `0 ↔ ∞` reciprocal closure are all derived forms, as is
  every equivalence relation (`derived_iff_equivalence`).

## What is proved

* `admissible_iff_kernel` — `P` is an admissible closure of `r` iff `P = selector r`.
* `admissible_closures_are_equal` — admissible closures of one return are equal.
* `ball_hair_admissible_iff` / `ball_hair_returns_are_equal_admissible_closures` — for a ball–hair
  return `x ↦ (ball x, hair x)` the admissible closure is exactly "same ball *and* same hair", and
  every admissible closure of it is that one relation.  Two ball–hair returns are equal admissible
  closures iff they harness one another, and then the dictionary between them is unique and
  injective.
* `maze_partition_admissible_iff`, `selected_maze_partition`, `maze_partition_selected_unique` — a
  maze partition is an admissible closure of a return iff its cells cut the occurrences exactly at
  the return's resolution; the return's own partition is always such a maze, and any admissible
  maze coincides with it.  `mazeQuotient_equiv_range` identifies the selected maze's cells with the
  values actually returned.
* `curvature_gauge_invariant`, `unitary_curvature_admissible_iff`,
  `unitary_curvature_selected` — the curvature form read from a holonomy is unchanged by a change
  of unitary frame (conjugation), and it is admissible exactly when the holonomy harnesses the
  return.  Instantiated at `Matrix.unitaryGroup (Fin 2) ℂ`.
* `maze_and_curvature_naturally_selected` — a maze partition and a unitary curvature that both
  harness the same ball–hair return are *the same* closure form, and it is the one the natural
  selector picks.
* `zeroInf_admissible`, `zero_inf_closes`, `zeroInf_naturally_selected`,
  `zeroInf_admissible_closure_unique` — the `0 ↔ ∞` reciprocal closure of NRRF710 is the admissible
  closure of the reciprocal return; `0` and `∞` close under it although `0 ≠ ∞`; every natural
  universal criterion gives that verdict, and no other admissible closure of that return exists.
* `derived_iff_equivalence`, `derived_form_naturally_selected`,
  `admissible_form_is_derived` — the derived forms are exactly the equivalence relations; each is
  the admissible closure of its own reading, selected by naturality, and nothing else is admissible
  there; and every admissible form is derived.
* `natural_is_the_translational_equality_selector` — naturality *is* the selector: a criterion is
  natural universal iff it returns `selector r` everywhere.
* `nrrf712_ball_hair_equal_admissible_closures_naturally_selected` — the headline conjunction.
-/

namespace NRRF712

open Function NRRF711

/-! ## §1  Closure forms, admissibility, and the selector -/

variable {A B C R S : Type}

/-- The closure form **read off** an evaluation `e`: two occurrences close when `e` does not
distinguish them.  Maze partitions, unitary curvatures and reciprocal charts are all of this
shape. -/
def readingForm (e : A → S) : A → A → Prop := fun x y => e x = e y

/-- **The natural selector.**  Naturality is not an extra condition applied after a closure form is
chosen; by NRRF711 it *selects* one form from the return, namely translational equality at the
resolution of that return. -/
def selector (r : A → R) : A → A → Prop := readingForm r

theorem selector_eq_readingForm (r : A → R) : selector r = readingForm r := rfl

/-- A closure form `P` is an **admissible closure** of the return `r` when it is the verdict of some
criterion that naturally universally closes. -/
def Admissible (r : A → R) (P : A → A → Prop) : Prop :=
  ∃ Cr : ClosureCriterion, NaturalUniversal Cr ∧ ∀ x y, P x y ↔ Cr A R r x y

/-- **Admissibility has exactly one solution.**  A closure form is admissible for a return iff it is
the translational equality the natural selector picks. -/
theorem admissible_iff_kernel (r : A → R) (P : A → A → Prop) :
    Admissible r P ↔ ∀ x y, P x y ↔ selector r x y := by
  constructor
  · rintro ⟨Cr, hCr, hP⟩ x y
    rw [hP x y]
    exact kernel_of_naturalUniversal hCr A R r x y
  · intro h
    exact ⟨kernelClosure, kernelClosure_naturalUniversal, h⟩

/-- The selected form is admissible: the notion is not empty. -/
theorem selector_admissible (r : A → R) : Admissible r (selector r) :=
  (admissible_iff_kernel r _).2 fun _ _ => Iff.rfl

/-- An admissible closure is *equal* to the selected one, as a relation. -/
theorem admissible_eq_selector {r : A → R} {P : A → A → Prop} (hP : Admissible r P) :
    P = selector r := by
  funext x y
  exact propext ((admissible_iff_kernel r P).1 hP x y)

/-- **Equal admissible closures.**  A return does not admit a choice of closure: any two admissible
closures of it are the same relation. -/
theorem admissible_closures_are_equal {r : A → R} {P Q : A → A → Prop}
    (hP : Admissible r P) (hQ : Admissible r Q) : P = Q := by
  rw [admissible_eq_selector hP, admissible_eq_selector hQ]

/-- A reading form is admissible for a return exactly when reading and return harness one another,
i.e. cut the occurrences into the same cells. -/
theorem readingForm_admissible_iff (r : A → R) (e : A → S) :
    Admissible r (readingForm e) ↔ NRRF709.Harness r e := by
  rw [admissible_iff_kernel]
  exact ⟨fun h x y => (h x y).symm, fun h x y => (h x y).symm⟩

/-- Two returns have the same admissible closures exactly when they harness one another. -/
theorem equal_admissible_closures_iff_harness (r : A → R) (e : A → S) :
    (∀ P : A → A → Prop, Admissible r P ↔ Admissible e P) ↔ NRRF709.Harness r e := by
  constructor
  · intro h x y
    have := (h (selector e)).2 (selector_admissible e)
    have hxy := (admissible_iff_kernel r (selector e)).1 this x y
    exact hxy.symm
  · intro h P
    constructor
    · intro hP
      refine (admissible_iff_kernel e P).2 fun x y => ?_
      exact ((admissible_iff_kernel r P).1 hP x y).trans (h x y)
    · intro hP
      refine (admissible_iff_kernel r P).2 fun x y => ?_
      exact ((admissible_iff_kernel e P).1 hP x y).trans (h x y).symm

/-- **The proof that two returns are equal admissible closures is a translation.**  Over a
surjective return there is exactly one dictionary carrying it to the other reading. -/
theorem unique_dictionary_of_equal_admissible_closures {r : A → R} {e : A → S} (hr : Surjective r)
    (h : ∀ P : A → A → Prop, Admissible r P ↔ Admissible e P) :
    ∃! t : R → S, ∀ x, t (r x) = e x :=
  NRRF709.harness_translation_existsUnique hr ((equal_admissible_closures_iff_harness r e).1 h)

/-- The dictionary is injective: neither return language is privileged. -/
theorem dictionary_injective_of_equal_admissible_closures {r : A → R} {e : A → S} {t : R → S}
    (hr : Surjective r) (h : ∀ P : A → A → Prop, Admissible r P ↔ Admissible e P)
    (ht : ∀ x, t (r x) = e x) : Injective t :=
  NRRF709.harness_translation_injective hr ((equal_admissible_closures_iff_harness r e).1 h) ht

/-- **Natural is the translational equality selector.**  A criterion naturally universally closes
iff, on every presentation, it returns exactly the selected translational equality. -/
theorem natural_is_the_translational_equality_selector (Cr : ClosureCriterion) :
    NaturalUniversal Cr ↔ ∀ (A R : Type) (r : A → R) (x y : A), Cr A R r x y ↔ selector r x y := by
  rw [naturalUniversal_iff_kernelClosure]
  exact Iff.rfl

/-! ## §2  Ball–hair returns -/

/-- The admissible closure of a ball–hair return is "same ball *and* same hair". -/
theorem ball_hair_admissible_iff (b : A → B) (hair : A → C) (P : A → A → Prop) :
    Admissible (NRRF709.ballHair b hair) P ↔ ∀ x y, P x y ↔ (b x = b y ∧ hair x = hair y) := by
  rw [admissible_iff_kernel]
  constructor
  · intro h x y
    rw [h x y]
    exact (NRRF709.ballHair_eq_iff b hair x y)
  · intro h x y
    rw [h x y]
    exact (NRRF709.ballHair_eq_iff b hair x y).symm

/-- **Ball–hair returns are equal admissible closures.**  Whatever admissible closures are offered
for a ball–hair return, they are one and the same relation, the selected one. -/
theorem ball_hair_returns_are_equal_admissible_closures (b : A → B) (hair : A → C)
    {P Q : A → A → Prop} (hP : Admissible (NRRF709.ballHair b hair) P)
    (hQ : Admissible (NRRF709.ballHair b hair) Q) :
    P = Q ∧ P = selector (NRRF709.ballHair b hair) :=
  ⟨admissible_closures_are_equal hP hQ, admissible_eq_selector hP⟩

/-- Two ball–hair returns are equal admissible closures exactly when they harness one another. -/
theorem ball_hair_equal_admissible_iff_harness (b : A → B) (hair : A → C)
    (b' : A → R) (hair' : A → S) :
    (∀ P : A → A → Prop, Admissible (NRRF709.ballHair b hair) P ↔
        Admissible (NRRF709.ballHair b' hair') P) ↔
      NRRF709.Harness (NRRF709.ballHair b hair) (NRRF709.ballHair b' hair') :=
  equal_admissible_closures_iff_harness _ _

/-- The ball alone is a coarser reading than the ball–hair return: closing at ball–hair resolution
implies closing at ball resolution, and (in general) not conversely. -/
theorem ball_hair_refines_ball (b : A → B) (hair : A → C) {x y : A}
    (h : selector (NRRF709.ballHair b hair) x y) : selector b x y :=
  NRRF709.ballHair_refines_ball b hair h

theorem ball_hair_refines_hair (b : A → B) (hair : A → C) {x y : A}
    (h : selector (NRRF709.ballHair b hair) x y) : selector hair x y :=
  NRRF709.ballHair_refines_hair b hair h

/-- The ball–hair admissible closure is the *conjunction* of the two admissible closures: hairs are
not extra structure imposed on the closure, they are part of the resolution being read. -/
theorem ball_hair_admissible_eq_inf (b : A → B) (hair : A → C) :
    selector (NRRF709.ballHair b hair) = fun x y => selector b x y ∧ selector hair x y := by
  funext x y
  exact propext (NRRF709.ballHair_eq_iff b hair x y)

/-! ## §3  The maze partition form -/

/-- A **maze partition** of the occurrences: an assignment of cells.  Its closure form is "same
cell". -/
def mazeForm {Cell : Type} (cell : A → Cell) : A → A → Prop := readingForm cell

/-- A maze partition is an admissible closure of a return iff its cells are cut exactly at the
resolution of the return. -/
theorem maze_partition_admissible_iff {Cell : Type} (r : A → R) (cell : A → Cell) :
    Admissible r (mazeForm cell) ↔ NRRF709.Harness r cell :=
  readingForm_admissible_iff r cell

/-- **The selected maze partition.**  A return always carries one maze whose cells are its own
fibres, and that maze is admissible. -/
theorem selected_maze_partition (r : A → R) : Admissible r (mazeForm r) :=
  selector_admissible r

/-- Any admissible maze partition *is* the selected one: the maze is not chosen, it is read. -/
theorem maze_partition_selected_unique {Cell : Type} {r : A → R} {cell : A → Cell}
    (h : Admissible r (mazeForm cell)) : mazeForm cell = mazeForm r :=
  admissible_eq_selector h

/-- The setoid of the selected maze partition. -/
def mazeSetoid (r : A → R) : Setoid A := Setoid.ker r

/-- The cells of the selected maze are exactly the values the return actually takes: the maze
partition adds nothing to, and loses nothing from, the return. -/
noncomputable def mazeQuotient_equiv_range (r : A → R) :
    Quotient (mazeSetoid r) ≃ Set.range r :=
  Setoid.quotientKerEquivRange r

/-! ## §4  The unitary curvature form -/

section Curvature

variable {G : Type} [Group G]

/-- The **curvature form** read from a holonomy `hol : A → G` valued in a (unitary) group: two
occurrences close when the holonomy returned along them is the same. -/
def curvatureForm (hol : A → G) : A → A → Prop := readingForm hol

/-- A change of unitary frame, i.e. conjugation of the holonomy by a fixed group element. -/
def gauge (u : G) (hol : A → G) : A → G := fun x => u * hol x * u⁻¹

/-- Gauge conjugation is a lossless relabelling of the return language, which is why it cannot move
the verdict of a natural criterion. -/
theorem gauge_injective (u : G) : Injective fun g : G => u * g * u⁻¹ := fun _ _ h =>
  mul_left_cancel (mul_right_cancel h)

/-- **Unitarity of the curvature form**: the closure form is invariant under a change of frame.  The
form does not depend on the frame in which the holonomy is named — only on which occurrences carry
the same holonomy. -/
theorem curvature_gauge_invariant (u : G) (hol : A → G) :
    curvatureForm (gauge u hol) = curvatureForm hol := by
  funext x y
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · exact gauge_injective u h
  · show u * hol x * u⁻¹ = u * hol y * u⁻¹
    rw [show hol x = hol y from h]

omit [Group G] in
/-- A unitary curvature is an admissible closure of a return iff the holonomy harnesses the
return. -/
theorem unitary_curvature_admissible_iff (r : A → R) (hol : A → G) :
    Admissible r (curvatureForm hol) ↔ NRRF709.Harness r hol :=
  readingForm_admissible_iff r hol

/-- **The selected unitary curvature.**  The curvature form of a holonomy is the admissible closure
of the holonomy read as a return, and remains so after any change of frame. -/
theorem unitary_curvature_selected (hol : A → G) (u : G) :
    Admissible hol (curvatureForm hol) ∧ Admissible hol (curvatureForm (gauge u hol)) := by
  refine ⟨selector_admissible hol, ?_⟩
  rw [curvature_gauge_invariant]
  exact selector_admissible hol

omit [Group G] in
/-- Any admissible unitary curvature of a return is the selected translational equality. -/
theorem unitary_curvature_unique {r : A → R} {hol : A → G}
    (h : Admissible r (curvatureForm hol)) : curvatureForm hol = selector r :=
  admissible_eq_selector h

end Curvature

/-- The unitary curvature statement at a concrete unitary group: `2 × 2` complex unitaries. -/
theorem unitary_curvature_admissible_iff_matrix (r : A → R)
    (hol : A → Matrix.unitaryGroup (Fin 2) ℂ) :
    Admissible r (curvatureForm hol) ↔ NRRF709.Harness r hol :=
  unitary_curvature_admissible_iff r hol

/-- The concrete gauge invariance: conjugating a `2 × 2` unitary holonomy leaves the curvature
closure form unchanged. -/
theorem curvature_gauge_invariant_matrix (u : Matrix.unitaryGroup (Fin 2) ℂ)
    (hol : A → Matrix.unitaryGroup (Fin 2) ℂ) :
    curvatureForm (gauge u hol) = curvatureForm hol :=
  curvature_gauge_invariant u hol

/-! ## §5  Maze partition and unitary curvature are one selected form -/

/-- **The selected closure form of maze partition and of unitary curvature is naturally selected.**
If a maze partition and a unitary curvature both harness a ball–hair return, they are literally the
same closure form; it is admissible for the return, and every criterion that naturally universally
closes returns exactly it. -/
theorem maze_and_curvature_naturally_selected {Cell G : Type} [Group G]
    (b : A → B) (hair : A → C) (cell : A → Cell) (hol : A → G)
    (hmaze : NRRF709.Harness (NRRF709.ballHair b hair) cell)
    (hcurv : NRRF709.Harness (NRRF709.ballHair b hair) hol) :
    mazeForm cell = curvatureForm hol ∧
      mazeForm cell = selector (NRRF709.ballHair b hair) ∧
      Admissible (NRRF709.ballHair b hair) (mazeForm cell) ∧
      ∀ Cr : ClosureCriterion, NaturalUniversal Cr → ∀ x y,
        Cr A (B × C) (NRRF709.ballHair b hair) x y ↔ mazeForm cell x y := by
  have hm : Admissible (NRRF709.ballHair b hair) (mazeForm cell) :=
    (maze_partition_admissible_iff _ cell).2 hmaze
  have hc : Admissible (NRRF709.ballHair b hair) (curvatureForm hol) :=
    (unitary_curvature_admissible_iff _ hol).2 hcurv
  refine ⟨admissible_closures_are_equal hm hc, admissible_eq_selector hm, hm, ?_⟩
  intro Cr hCr x y
  rw [kernel_of_naturalUniversal hCr]
  exact ((admissible_iff_kernel _ _).1 hm x y).symm

/-- Gauge freedom does not disturb the identification: conjugating the holonomy gives the same
selected form. -/
theorem maze_and_gauged_curvature_agree {Cell G : Type} [Group G]
    (b : A → B) (hair : A → C) (cell : A → Cell) (hol : A → G) (u : G)
    (hmaze : NRRF709.Harness (NRRF709.ballHair b hair) cell)
    (hcurv : NRRF709.Harness (NRRF709.ballHair b hair) hol) :
    mazeForm cell = curvatureForm (gauge u hol) := by
  rw [curvature_gauge_invariant]
  exact (maze_and_curvature_naturally_selected b hair cell hol hmaze hcurv).1

/-! ## §6  The `0 ↔ ∞` closure -/

section ZeroInf

/-- The reciprocal return of NRRF710: a magnitude is returned by its `0 ↔ ∞` closure class. -/
def zeroInfReturn : ENNReal → Quotient NRRF710.recipSetoid := NRRF710.closureClassZeroInf

/-- The `0 ↔ ∞` closure form: `x` and `y` close when one is the reciprocal of the other. -/
def zeroInfForm : ENNReal → ENNReal → Prop := NRRF710.recipRel

/-- The `0 ↔ ∞` closure form is exactly the translational equality of the reciprocal return: it is
a derived form, and an admissible closure. -/
theorem zeroInf_admissible : Admissible zeroInfReturn zeroInfForm := by
  refine (admissible_iff_kernel _ _).2 fun x y => ?_
  constructor
  · intro h
    exact Quotient.sound h
  · intro h
    exact Quotient.exact h

/-- `0` and `∞` close under it, although they are not the same magnitude. -/
theorem zero_inf_closes : zeroInfForm 0 ⊤ ∧ (0 : ENNReal) ≠ ⊤ :=
  ⟨Or.inr (by simp), NRRF710.zero_ne_top_absolutely⟩

/-- **The `0 ↔ ∞` closure is naturally selected.**  Every criterion that naturally universally
closes gives exactly the reciprocal verdict on the reciprocal return; in particular it closes `0`
with `∞`. -/
theorem zeroInf_naturally_selected (Cr : ClosureCriterion) (hCr : NaturalUniversal Cr) :
    (∀ x y, Cr ENNReal (Quotient NRRF710.recipSetoid) zeroInfReturn x y ↔ zeroInfForm x y) ∧
      Cr ENNReal (Quotient NRRF710.recipSetoid) zeroInfReturn 0 ⊤ := by
  have hkey : ∀ x y, Cr ENNReal (Quotient NRRF710.recipSetoid) zeroInfReturn x y ↔
      zeroInfForm x y := by
    intro x y
    rw [kernel_of_naturalUniversal hCr]
    exact ((admissible_iff_kernel _ _).1 zeroInf_admissible x y).symm
  exact ⟨hkey, (hkey 0 ⊤).2 zero_inf_closes.1⟩

/-- No other admissible closure of the reciprocal return exists. -/
theorem zeroInf_admissible_closure_unique {P : ENNReal → ENNReal → Prop}
    (hP : Admissible zeroInfReturn P) : P = zeroInfForm :=
  admissible_closures_are_equal hP zeroInf_admissible

end ZeroInf

/-! ## §7  All other derived forms -/

/-- A closure form is **derived** when it is read off some evaluation of the occurrences. -/
def Derived (P : A → A → Prop) : Prop := ∃ (S : Type) (e : A → S), P = readingForm e

/-- **The derived forms are exactly the equivalence relations.**  Nothing else can be read off an
evaluation, and every equivalence relation is read off its own quotient. -/
theorem derived_iff_equivalence (P : A → A → Prop) : Derived P ↔ Equivalence P := by
  constructor
  · rintro ⟨S, e, rfl⟩
    exact ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩
  · intro hP
    let s : Setoid A := ⟨P, hP⟩
    refine ⟨Quotient s, Quotient.mk s, ?_⟩
    funext x y
    exact propext ⟨fun h => Quotient.sound h, fun h => Quotient.exact h⟩

/-- **Every derived form is naturally selected, at exactly one resolution.**  A derived form is the
admissible closure of the reading it is derived from, it is the form the natural selector picks
there, and no other closure form is admissible for that reading. -/
theorem derived_form_naturally_selected {P : A → A → Prop} (hP : Derived P) :
    ∃ (S : Type) (e : A → S), Admissible e P ∧ P = selector e ∧
      ∀ Q : A → A → Prop, Admissible e Q → Q = P := by
  obtain ⟨S, e, rfl⟩ := hP
  refine ⟨S, e, selector_admissible e, rfl, ?_⟩
  intro Q hQ
  exact admissible_eq_selector hQ

/-- Conversely, every admissible closure is a derived form. -/
theorem admissible_form_is_derived {r : A → R} {P : A → A → Prop} (hP : Admissible r P) :
    Derived P :=
  ⟨R, r, admissible_eq_selector hP⟩

/-- Ball–hair, maze partition, unitary curvature and the reciprocal chart are all derived forms. -/
theorem ball_hair_maze_curvature_zeroInf_derived {Cell G : Type} [Group G]
    (b : A → B) (hair : A → C) (cell : A → Cell) (hol : A → G) :
    Derived (selector (NRRF709.ballHair b hair)) ∧ Derived (mazeForm cell) ∧
      Derived (curvatureForm hol) ∧ Derived zeroInfForm :=
  ⟨⟨B × C, NRRF709.ballHair b hair, rfl⟩, ⟨Cell, cell, rfl⟩, ⟨G, hol, rfl⟩,
    ⟨Quotient NRRF710.recipSetoid, zeroInfReturn, admissible_eq_selector zeroInf_admissible⟩⟩

/-! ## §8  The headline statement -/

/-- **NRRF712.**  Ball–hair returns are equal admissible closures; the selected closure form —
whether presented as a maze partition or as a unitary curvature — is naturally selected, naturality
being the translational equality selector; and the same holds for the `0 ↔ ∞` closure and for every
other derived form.

The six clauses are:

1. naturality *is* the translational equality selector;
2. a return's admissible closures are all equal to the selected form, and the selected form is
   admissible;
3. for a ball–hair return the selected form is "same ball and same hair", and any two ball–hair
   returns are equal admissible closures exactly when a unique injective dictionary translates one
   into the other;
4. a maze partition and a unitary curvature that harness the return are the same selected form, and
   the curvature form is invariant under change of unitary frame;
5. the `0 ↔ ∞` reciprocal closure is that selected form for the reciprocal return, closing `0` with
   `∞` although `0 ≠ ∞`;
6. the derived forms are exactly the equivalence relations, each naturally selected at its own
   resolution, and every admissible form is derived. -/
theorem nrrf712_ball_hair_equal_admissible_closures_naturally_selected :
    -- 1. natural = the translational equality selector
    (∀ Cr : ClosureCriterion, NaturalUniversal Cr ↔
        ∀ (A R : Type) (r : A → R) (x y : A), Cr A R r x y ↔ selector r x y) ∧
    -- 2. admissible closures of a return are equal, and the selected form is admissible
    (∀ (A R : Type) (r : A → R), Admissible r (selector r) ∧
        ∀ P Q : A → A → Prop, Admissible r P → Admissible r Q → P = Q ∧ P = selector r) ∧
    -- 3. ball–hair returns
    (∀ (A B C : Type) (b : A → B) (hair : A → C),
        (selector (NRRF709.ballHair b hair) =
          fun x y => selector b x y ∧ selector hair x y) ∧
        ∀ (S : Type) (e : A → S), Surjective (NRRF709.ballHair b hair) →
          (∀ P : A → A → Prop, Admissible (NRRF709.ballHair b hair) P ↔ Admissible e P) →
          ∃! t : B × C → S, ∀ x, t (NRRF709.ballHair b hair x) = e x) ∧
    -- 4. maze partition and unitary curvature
    (∀ (A R Cell G : Type) [Group G] (r : A → R) (cell : A → Cell) (hol : A → G) (u : G),
        NRRF709.Harness r cell → NRRF709.Harness r hol →
          mazeForm cell = curvatureForm hol ∧
          curvatureForm (gauge u hol) = curvatureForm hol ∧
          mazeForm cell = selector r) ∧
    -- 5. the `0 ↔ ∞` closure
    (Admissible zeroInfReturn zeroInfForm ∧ zeroInfForm 0 ⊤ ∧ (0 : ENNReal) ≠ ⊤ ∧
      ∀ Cr : ClosureCriterion, NaturalUniversal Cr →
        Cr ENNReal (Quotient NRRF710.recipSetoid) zeroInfReturn 0 ⊤) ∧
    -- 6. all other derived forms
    (∀ (A : Type) (P : A → A → Prop),
        (Derived P ↔ Equivalence P) ∧
        (Derived P → ∃ (S : Type) (e : A → S), Admissible e P ∧ P = selector e ∧
          ∀ Q : A → A → Prop, Admissible e Q → Q = P)) := by
  refine ⟨natural_is_the_translational_equality_selector, ?_, ?_, ?_, ?_, ?_⟩
  · intro A R r
    exact ⟨selector_admissible r, fun P Q hP hQ =>
      ⟨admissible_closures_are_equal hP hQ, admissible_eq_selector hP⟩⟩
  · intro A B C b hair
    refine ⟨ball_hair_admissible_eq_inf b hair, ?_⟩
    intro S e hsurj h
    exact unique_dictionary_of_equal_admissible_closures hsurj h
  · intro A R Cell G _ r cell hol u hmaze hcurv
    have hm : Admissible r (mazeForm cell) := (maze_partition_admissible_iff r cell).2 hmaze
    have hc : Admissible r (curvatureForm hol) := (unitary_curvature_admissible_iff r hol).2 hcurv
    exact ⟨admissible_closures_are_equal hm hc, curvature_gauge_invariant u hol,
      admissible_eq_selector hm⟩
  · exact ⟨zeroInf_admissible, zero_inf_closes.1, zero_inf_closes.2,
      fun Cr hCr => (zeroInf_naturally_selected Cr hCr).2⟩
  · intro A P
    exact ⟨derived_iff_equivalence P, derived_form_naturally_selected⟩

end NRRF712

/-! ## §9  Axiom audit -/

section Audit

open NRRF712

#print axioms NRRF712.admissible_iff_kernel
#print axioms NRRF712.admissible_closures_are_equal
#print axioms NRRF712.ball_hair_returns_are_equal_admissible_closures
#print axioms NRRF712.maze_and_curvature_naturally_selected
#print axioms NRRF712.zeroInf_naturally_selected
#print axioms NRRF712.derived_iff_equivalence
#print axioms NRRF712.nrrf712_ball_hair_equal_admissible_closures_naturally_selected

end Audit
