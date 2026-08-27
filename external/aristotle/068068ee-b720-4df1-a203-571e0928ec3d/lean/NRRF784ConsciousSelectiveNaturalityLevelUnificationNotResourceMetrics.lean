/-!
# NRRF784 — Consequences of selection by *conscious selective naturality at level unification*, rather than by resource-driven metrics

The development selects forms by **naturality across levels**: a form is selected when the
selection criterion is unchanged by a change of level (a translation), so that the verdict is a
property of the *orbit* — the level-unified object — and not of any particular level in which the
object happens to be presented.  The rival convention selects by a **resource-driven metric**: a
cost function on forms, with the cheapest form selected.

This file makes the difference into theorems.  Nothing is asserted informally that is not
machine-checked below, and the file has **no `import` line**: only Lean's kernel is in scope, so
no library convention can be smuggled in.  §9 fixes the exact axiom list of every headline result.

## The setting (§1)

A **level arena** `Arena F S` is a type `F` of forms together with an action of an abelian group
`S` of **level shifts** (translations, changes of description level).  A **selector** is a
predicate `sel : F → Prop`; it is **natural** when `sel (s · f) ↔ sel f` for every shift `s` — its
verdict survives every change of level.  A **resource metric** is a cost `F → Int`, whose selector
is "is a global minimiser of the cost".

## The consequences

1. **Naturality is exactly self-consistency of the selector under level change** (§2).  Level
   shifts act on selectors as well as on forms, and `natural_iff_fixed` says: a selector is
   natural iff it is a *fixed point* of that action.  The criterion is not applied from outside
   the system; a natural selector is one that is already invariant in the system it selects in.

2. **Natural selection is precisely selection of levels-unified objects** (§3).
   `natural_iff_factors`: a selector is natural iff it factors through the orbit quotient — the
   level-unification.  So a natural criterion carries exactly the information of a predicate on
   unified levels, no more and no less.  Natural selectors are closed under all the propositional
   operations (`Natural.and`, `Natural.or`, `Natural.not`, `Natural.forall_`), so the natural
   verdicts form a full logic of their own.

3. **The dichotomy for resource metrics** (§4).  A resource metric is either
   *level-dependent* — and then its verdict changes with the level, so it is not a criterion about
   the object at all — or *level-blind on what it selects*, and then it distinguishes nothing that
   the naturality criterion has not already distinguished:
   * `invariant_selection_natural`: an invariant cost selects naturally;
   * `resource_dichotomy`: if a cost selects naturally, the cost is **constant on the orbit of
     every selected form** — the resource numbers collapse exactly where they were supposed to
     decide;
   * `natural_metric_is_orbit_criterion`: such a selection factors through level unification, i.e.
     it *is* a naturality criterion;
   * `bias_selection_not_natural`: an explicit two-form arena where a resource metric's verdict is
     reversed by a single shift of level.

4. **Resource selection can fail to exist; natural selection cannot** (§5).  `no_argmin_shift`:
   on the translation arena of `Int` with cost `id`, *no* form is cheapest — the resource
   convention returns no verdict at all — while the criterion is perfectly natural there and the
   natural selectors always include inhabited ones (`natural_top`).

5. **The criterion is selected by its own criterion; the resource criterion is not** (§6).  This
   is the "conscious" part: the selector is inside the system, so the criterion must survive being
   applied to itself.  `naturality_criterion_self_natural`: naturality, viewed as a selector *of
   selectors*, is natural.  `resource_criterion_not_self_natural`: "is the argmin-selector of this
   cost" is **not** — a change of level takes the argmin-selector to something that is no longer
   the argmin-selector.  A resource criterion therefore requires an external, unmoved authority to
   fix the level in which costs are counted; the naturality criterion requires none.

6. **Level unification: natural verdicts transport, cheapest verdicts do not** (§7).  Along any
   equivariant map of levels a natural selector pulls back to a natural selector
   (`natural_comap`), and this composes (`natural_comap_comp`), so one natural verdict is a
   verdict at every level at once.  Resource verdicts do not compose: `local_min_not_global` and
   `resource_selection_does_not_transport` exhibit a two-level system in which the form selected
   as cheapest at the lower level is **never** part of anything cheapest at the upper level, while
   the naturality criterion transports without change.
-/

namespace NRRF784

universe u v w

/-! ## §1  Levels, forms, selectors, naturality

A level shift is a translation: there is a neutral shift, shifts compose, every shift is
reversible, and shifts commute (changing level twice in either order is the same change).  This is
the situation the development always works in — translation, with no selected origin. -/

/-- A **level arena**: forms `F` carrying an action of an abelian group `S` of **level shifts**. -/
structure Arena (F : Type u) (S : Type v) where
  /-- Change the level of a form. -/
  act : S → F → F
  /-- The neutral change of level. -/
  unit : S
  /-- Composition of level changes. -/
  comp : S → S → S
  /-- Reversal of a level change. -/
  inv : S → S
  act_unit : ∀ f, act unit f = f
  act_comp : ∀ s t f, act s (act t f) = act (comp s t) f
  comp_comm : ∀ s t, comp s t = comp t s
  comp_assoc : ∀ s t u, comp (comp s t) u = comp s (comp t u)
  comp_unit : ∀ s, comp s unit = s
  comp_inv : ∀ s, comp s (inv s) = unit

namespace Arena

variable {F : Type u} {G : Type w} {S : Type v}

/-- Reversing a level change undoes it. -/
theorem act_inv_act (A : Arena F S) (s : S) (f : F) : A.act (A.inv s) (A.act s f) = f := by
  rw [A.act_comp, A.comp_comm, A.comp_inv, A.act_unit]

/-- Undoing a level change by performing it. -/
theorem act_act_inv (A : Arena F S) (s : S) (f : F) : A.act s (A.act (A.inv s) f) = f := by
  rw [A.act_comp, A.comp_inv, A.act_unit]

end Arena

/-- A **selector**: the verdict "this form is selected". -/
def Selector (F : Type u) : Type u := F → Prop

variable {F : Type u} {G : Type w} {S : Type v}

/-- A selector is **natural** when its verdict is unchanged by every change of level. -/
def Natural (A : Arena F S) (sel : Selector F) : Prop := ∀ s f, sel (A.act s f) ↔ sel f

/-- The action of a level shift on a *selector*: read the verdict one level over. -/
def shift (A : Arena F S) (s : S) (sel : Selector F) : Selector F := fun f => sel (A.act s f)

/-! ## §2  Naturality is self-consistency of the selector under level change -/

/-- **Naturality is being a fixed point of the level action on selectors.**  A natural criterion
is not imposed from outside the system: it is one that the system's own changes of level leave
where it was. -/
theorem natural_iff_fixed (A : Arena F S) (sel : Selector F) :
    Natural A sel ↔ ∀ s, shift A s sel = sel := by
  constructor
  · intro h s
    funext f
    exact propext (h s f)
  · intro h s f
    exact Iff.of_eq (congrFun (h s) f)

/-- The everywhere-true selector is natural. -/
theorem natural_top (A : Arena F S) : Natural A (fun _ => True) := fun _ _ => Iff.rfl

/-- The everywhere-false selector is natural. -/
theorem natural_bot (A : Arena F S) : Natural A (fun _ => False) := fun _ _ => Iff.rfl

namespace Natural

/-- Natural verdicts are closed under conjunction. -/
theorem and {A : Arena F S} {p q : Selector F} (hp : Natural A p) (hq : Natural A q) :
    Natural A (fun f => p f ∧ q f) := fun s f =>
  ⟨fun h => ⟨(hp s f).mp h.1, (hq s f).mp h.2⟩, fun h => ⟨(hp s f).mpr h.1, (hq s f).mpr h.2⟩⟩

/-- Natural verdicts are closed under disjunction. -/
theorem or {A : Arena F S} {p q : Selector F} (hp : Natural A p) (hq : Natural A q) :
    Natural A (fun f => p f ∨ q f) := fun s f =>
  ⟨fun h => h.elim (fun h => Or.inl ((hp s f).mp h)) (fun h => Or.inr ((hq s f).mp h)),
   fun h => h.elim (fun h => Or.inl ((hp s f).mpr h)) (fun h => Or.inr ((hq s f).mpr h))⟩

/-- Natural verdicts are closed under negation. -/
theorem not {A : Arena F S} {p : Selector F} (hp : Natural A p) :
    Natural A (fun f => ¬ p f) := fun s f =>
  ⟨fun h hf => h ((hp s f).mpr hf), fun h hf => h ((hp s f).mp hf)⟩

/-- Natural verdicts are closed under arbitrary indexed conjunction. -/
theorem forall_ {A : Arena F S} {ι : Type w} {p : ι → Selector F} (hp : ∀ i, Natural A (p i)) :
    Natural A (fun f => ∀ i, p i f) := fun s f =>
  ⟨fun h i => (hp i s f).mp (h i), fun h i => (hp i s f).mpr (h i)⟩

end Natural

/-! ## §3  Natural selection *is* selection at the unification of levels

The orbit of a form under all level shifts is the form with its level forgotten — the object
unified across levels.  A criterion is natural exactly when it is a criterion about that. -/

/-- Two forms are at the same unified level when one is a level shift of the other. -/
def OrbitRel (A : Arena F S) (f g : F) : Prop := ∃ s, A.act s f = g

/-- The **level unification**: forms modulo change of level. -/
def Orbit (A : Arena F S) : Type u := Quot (OrbitRel A)

/-- A form, read at the unification of levels. -/
def orb (A : Arena F S) (f : F) : Orbit A := Quot.mk _ f

/-- Forms differing by a level shift are the same unified object. -/
theorem orb_act (A : Arena F S) (s : S) (f : F) : orb A (A.act s f) = orb A f :=
  (Quot.sound ⟨s, rfl⟩).symm

/-- **A selector is natural iff it factors through the unification of levels.**  Natural selection
carries exactly the content of a predicate on level-unified objects. -/
theorem natural_iff_factors (A : Arena F S) (sel : Selector F) :
    Natural A sel ↔ ∃ P : Orbit A → Prop, ∀ f, sel f ↔ P (orb A f) := by
  constructor
  · intro h
    refine ⟨Quot.lift sel ?_, fun _ => Iff.rfl⟩
    rintro a b ⟨s, rfl⟩
    exact (propext (h s a)).symm
  · rintro ⟨P, hP⟩ s f
    exact (hP (A.act s f)).trans (by rw [orb_act]; exact (hP f).symm)

/-! ## §4  Resource-driven metrics, and the dichotomy they face -/

/-- A **resource metric** on forms: a cost, counted in some unit. -/
structure Metric (F : Type u) where
  /-- The resource cost of a form. -/
  cost : F → Int

/-- The resource-driven verdict: a form is selected when nothing costs less. -/
def Metric.Selected (m : Metric F) (f : F) : Prop := ∀ g, m.cost f ≤ m.cost g

/-- A metric is **level-invariant** when a change of level does not change any cost. -/
def Metric.Invariant (A : Arena F S) (m : Metric F) : Prop := ∀ s f, m.cost (A.act s f) = m.cost f

/-- A level-invariant cost selects naturally. -/
theorem invariant_selection_natural (A : Arena F S) (m : Metric F) (h : m.Invariant A) :
    Natural A m.Selected := by
  intro s f
  constructor
  · intro hf g; rw [← h s f]; exact hf g
  · intro hf g; rw [h s f]; exact hf g

/-- **The dichotomy.**  If a resource-driven verdict is natural, then the cost is *constant on the
orbit* of every form it selects: exactly where the metric was supposed to decide, its numbers are
level-blind.  A resource metric is therefore either level-dependent — its verdict is about the
presentation, not the object — or it decides nothing beyond the unified level. -/
theorem resource_dichotomy (A : Arena F S) (m : Metric F) (hnat : Natural A m.Selected)
    {f : F} (hf : m.Selected f) (s : S) : m.cost (A.act s f) = m.cost f :=
  Int.le_antisymm ((hnat s f).mpr hf f) (hf (A.act s f))

/-- A naturally-selecting resource metric *is* a naturality criterion: its verdict factors through
the unification of levels. -/
theorem natural_metric_is_orbit_criterion (A : Arena F S) (m : Metric F)
    (hnat : Natural A m.Selected) : ∃ P : Orbit A → Prop, ∀ f, m.Selected f ↔ P (orb A f) :=
  (natural_iff_factors A m.Selected).mp hnat

/-- Contrapositive form: a metric that a single change of level makes cheaper (or dearer) at a
form it selects cannot be selecting naturally. -/
theorem not_natural_of_cost_moves (A : Arena F S) (m : Metric F) {f : F} {s : S}
    (hf : m.Selected f) (hmove : m.cost (A.act s f) ≠ m.cost f) : ¬ Natural A m.Selected :=
  fun hnat => hmove (resource_dichotomy A m hnat hf s)

/-! ### An explicit arena where a resource verdict is reversed by one change of level -/

/-- Two forms, one level shift: the arena of a single reversible change of level. -/
def flipArena : Arena Bool Bool where
  act s f := xor s f
  unit := false
  comp := xor
  inv := id
  act_unit f := by cases f <;> rfl
  act_comp s t f := by cases s <;> cases t <;> cases f <;> rfl
  comp_comm s t := by cases s <;> cases t <;> rfl
  comp_assoc s t u := by cases s <;> cases t <;> cases u <;> rfl
  comp_unit s := by cases s <;> rfl
  comp_inv s := by cases s <;> rfl

/-- A resource metric on those two forms: the second costs one unit more. -/
def biasMetric : Metric Bool where
  cost b := cond b 1 0

theorem bias_selects_false : biasMetric.Selected false := by
  intro g; cases g <;> decide

theorem bias_rejects_true : ¬ biasMetric.Selected true := by
  intro h
  exact absurd (h false) (by decide)

/-- **The resource verdict is not natural**: one change of level turns the selected form into the
rejected one.  The metric ranks presentations, not objects. -/
theorem bias_selection_not_natural : ¬ Natural flipArena biasMetric.Selected := by
  intro h
  exact bias_rejects_true ((h true false).mpr bias_selects_false)

/-- The same fact through the dichotomy: the cost of the selected form moves under a shift. -/
theorem bias_cost_moves : biasMetric.cost (flipArena.act true false) ≠ biasMetric.cost false := by
  decide

/-! ## §5  Resource selection may return no verdict at all; naturality always returns one -/

/-- The translation arena: `Int` shifted by `Int`, the development's standing picture of a level
line with no selected origin. -/
def shiftArena : Arena Int Int where
  act s f := s + f
  unit := 0
  comp s t := s + t
  inv s := -s
  act_unit f := by omega
  act_comp s t f := by omega
  comp_comm s t := by omega
  comp_assoc s t u := by omega
  comp_unit s := by omega
  comp_inv s := by omega

/-- Cost = position on the level line: the archetype of a resource metric that presupposes an
origin. -/
def positionMetric : Metric Int where
  cost f := f

/-- **No form is cheapest.**  On a level line with no selected origin the resource convention
returns no verdict whatsoever. -/
theorem no_argmin_shift : ¬ ∃ f, positionMetric.Selected f := by
  rintro ⟨f, hf⟩
  have := hf (f - 1)
  simp only [positionMetric] at this
  omega

/-- The naturality criterion, by contrast, is available on that same arena and does select. -/
theorem natural_selection_available :
    Natural shiftArena (fun _ => True) ∧ (fun _ : Int => True) 0 :=
  ⟨natural_top shiftArena, trivial⟩

/-! ## §6  The conscious part: the criterion applied to itself

The selector is not outside the system.  Level shifts act on selectors exactly as they act on
forms, so a criterion is a form in the arena of criteria, and one may ask whether it selects
itself.  Naturality does; being-the-cheapest does not. -/

/-- Level shifts acting on selectors: the **meta-arena** of criteria. -/
def metaArena (A : Arena F S) : Arena (Selector F) S where
  act := shift A
  unit := A.unit
  comp := A.comp
  inv := A.inv
  act_unit sel := by
    funext f; show sel (A.act A.unit f) = sel f; rw [A.act_unit]
  act_comp s t sel := by
    funext f
    show sel (A.act t (A.act s f)) = sel (A.act (A.comp s t) f)
    rw [A.act_comp, A.comp_comm]
  comp_comm := A.comp_comm
  comp_assoc := A.comp_assoc
  comp_unit := A.comp_unit
  comp_inv := A.comp_inv

/-- **The naturality criterion satisfies its own criterion.**  Viewed as a selector of selectors,
`Natural A` is natural for the meta-arena: changing the level at which criteria are read does not
change which criteria are selected.  The criterion needs no unmoved external authority; it is a
form of the system it judges. -/
theorem naturality_criterion_self_natural (A : Arena F S) :
    Natural (metaArena A) (Natural A) := by
  intro s sel
  show Natural A (shift A s sel) ↔ Natural A sel
  constructor
  · intro h t g
    have key : A.comp (A.comp s t) (A.inv s) = t := by
      rw [A.comp_assoc, A.comp_comm t (A.inv s), ← A.comp_assoc, A.comp_inv, A.comp_comm,
        A.comp_unit]
    have e₁ : A.act s (A.act t (A.act (A.inv s) g)) = A.act t g := by
      rw [A.act_comp, A.act_comp, key]
    have e₂ : A.act s (A.act (A.inv s) g) = g := A.act_act_inv s g
    have h' : sel (A.act s (A.act t (A.act (A.inv s) g)))
        ↔ sel (A.act s (A.act (A.inv s) g)) := h t (A.act (A.inv s) g)
    rw [e₁, e₂] at h'
    exact h'
  · intro h t g
    show sel (A.act s (A.act t g)) ↔ sel (A.act s g)
    exact ((h s (A.act t g)).trans (h t g)).trans (h s g).symm

/-- The criterion "this selector is the argmin-selector of the cost `m`", as a selector of
selectors. -/
def IsArgminSelector (m : Metric F) : Selector (Selector F) := fun sel => ∀ f, sel f ↔ m.Selected f

/-- **The resource criterion does not satisfy its own criterion.**  In the two-form arena, one
change of level carries the argmin-selector to a selector that is no longer the argmin-selector:
the resource convention is not stable under the level changes of the system it is applied to, so
it can only be maintained by fixing a level from outside. -/
theorem resource_criterion_not_self_natural :
    ¬ Natural (metaArena flipArena) (IsArgminSelector biasMetric) := by
  intro h
  have hself : IsArgminSelector biasMetric biasMetric.Selected := fun _ => Iff.rfl
  have hshift : IsArgminSelector biasMetric (shift flipArena true biasMetric.Selected) :=
    (h true biasMetric.Selected).mpr hself
  refine bias_selection_not_natural (fun s f => ?_)
  cases s
  · exact Iff.of_eq (congrArg biasMetric.Selected (show flipArena.act false f = f by cases f <;> rfl))
  · exact hshift f

/-! ## §7  Level unification: natural verdicts transport, cheapest verdicts do not -/

/-- A **map of levels**: a translation-respecting map between arenas over the same shifts. -/
structure LevelMap (A : Arena F S) (B : Arena G S) where
  /-- The underlying map of forms. -/
  map : F → G
  /-- It respects change of level. -/
  equivariant : ∀ s f, map (A.act s f) = B.act s (map f)

/-- **Natural verdicts transport across levels.**  A criterion given at one level is, pulled back
along any map of levels, still a criterion — still natural.  One natural verdict is a verdict at
every level at once: this is the level unification. -/
theorem natural_comap {A : Arena F S} {B : Arena G S} (L : LevelMap A B) {sel : Selector G}
    (h : Natural B sel) : Natural A (fun f => sel (L.map f)) := by
  intro s f
  show sel (L.map (A.act s f)) ↔ sel (L.map f)
  rw [L.equivariant s f]
  exact h s (L.map f)

/-- Maps of levels compose. -/
def LevelMap.comp {H : Type u} {A : Arena F S} {B : Arena G S} {C : Arena H S}
    (L : LevelMap A B) (M : LevelMap B C) : LevelMap A C where
  map f := M.map (L.map f)
  equivariant s f := by rw [L.equivariant, M.equivariant]

/-- Transport of natural verdicts is compatible with composition of levels. -/
theorem natural_comap_comp {H : Type u} {A : Arena F S} {B : Arena G S} {C : Arena H S}
    (L : LevelMap A B) (M : LevelMap B C) {sel : Selector H} (h : Natural C sel) :
    Natural A (fun f => sel ((L.comp M).map f)) := natural_comap (L.comp M) h

/-! ### A two-level system in which the cheapest verdict does not transport

Lower level: a single binary choice.  Upper level: that choice followed by a second one, with the
total resource counted.  The first choice is cheap and the continuation forced on it is dear. -/

/-- Cost of the lower-level choice alone. -/
def stage1 (a : Bool) : Int := cond a 1 0

/-- Cost of the continuation, given the lower-level choice. -/
def stage2 (a : Bool) (_b : Bool) : Int := cond a 0 10

/-- Total cost at the upper level. -/
def total (p : Bool × Bool) : Int := stage1 p.1 + stage2 p.1 p.2

/-- The lower-level metric. -/
def lowerMetric : Metric Bool where
  cost := stage1

/-- The upper-level metric. -/
def upperMetric : Metric (Bool × Bool) where
  cost := total

/-- The lower level selects `false`: it is the cheaper choice there. -/
theorem lower_selects_false : lowerMetric.Selected false := by
  intro g; cases g <;> decide

/-- The upper level selects a form built on `true`. -/
theorem upper_selects_true : upperMetric.Selected (true, false) := by
  rintro ⟨a, b⟩; cases a <;> cases b <;> decide

/-- **The locally cheapest choice is never globally cheapest.**  No completion of the lower-level
verdict is selected at the upper level, so resource verdicts do not compose across levels. -/
theorem local_min_not_global : ∀ b, ¬ upperMetric.Selected (false, b) := by
  intro b h
  exact absurd (h (true, false)) (by cases b <;> decide)

/-- Forgetting the second choice is a map of levels: level shifts act on the first coordinate. -/
def pairArena : Arena (Bool × Bool) Bool where
  act s p := (xor s p.1, p.2)
  unit := false
  comp := xor
  inv := id
  act_unit p := by cases p with | mk a b => cases a <;> rfl
  act_comp s t p := by cases p with | mk a b => cases s <;> cases t <;> cases a <;> rfl
  comp_comm s t := by cases s <;> cases t <;> rfl
  comp_assoc s t u := by cases s <;> cases t <;> cases u <;> rfl
  comp_unit s := by cases s <;> rfl
  comp_inv s := by cases s <;> rfl

/-- The projection of levels. -/
def project : LevelMap pairArena flipArena where
  map p := p.1
  equivariant _ _ := rfl

/-- **Natural verdicts do transport along that very map**: whatever is natural downstairs is
natural upstairs, unchanged. -/
theorem natural_transports {sel : Selector Bool} (h : Natural flipArena sel) :
    Natural pairArena (fun p => sel (project.map p)) := natural_comap project h

/-- **Resource verdicts do not transport along it.**  The lower level selects `false`; the upper
level selects a form over `true`; and nothing over the lower verdict is selected upstairs.  The
cost numbers of the two levels are simply different criteria, with no unification between them —
whereas one natural criterion serves both levels at once. -/
theorem resource_selection_does_not_transport :
    lowerMetric.Selected false ∧ upperMetric.Selected (true, false) ∧
      (∀ p : Bool × Bool, project.map p = false → ¬ upperMetric.Selected p) := by
  refine ⟨lower_selects_false, upper_selects_true, ?_⟩
  rintro ⟨a, b⟩ ha
  have : a = false := ha
  subst this
  exact local_min_not_global b

/-! ## §8  The consequences, collected -/

/-- **NRRF784.**  The consequences of selecting by conscious selective naturality at the
unification of levels, rather than by resource-driven metrics, in one statement:

1. naturality is self-consistency of the selector under change of level;
2. natural selection is exactly selection at the unification of levels;
3. a resource metric that selects naturally has level-blind costs on everything it selects, and
   its verdict is then already a naturality verdict;
4. an explicit resource verdict that one change of level reverses;
5. an arena on which the resource convention returns no verdict at all;
6. the naturality criterion satisfies its own criterion, while the resource criterion does not;
7. natural verdicts transport across levels, and there is a two-level system in which the
   cheapest verdict does not. -/
theorem nrrf784_consequences :
    (∀ (F S : Type) (A : Arena F S) (sel : Selector F),
        Natural A sel ↔ ∀ s, shift A s sel = sel) ∧
    (∀ (F S : Type) (A : Arena F S) (sel : Selector F),
        Natural A sel ↔ ∃ P : Orbit A → Prop, ∀ f, sel f ↔ P (orb A f)) ∧
    (∀ (F S : Type) (A : Arena F S) (m : Metric F), Natural A m.Selected →
        ∀ f : F, m.Selected f → ∀ s, m.cost (A.act s f) = m.cost f) ∧
    (¬ Natural flipArena biasMetric.Selected) ∧
    (¬ ∃ f, positionMetric.Selected f) ∧
    (∀ (F S : Type) (A : Arena F S), Natural (metaArena A) (Natural A)) ∧
    (¬ Natural (metaArena flipArena) (IsArgminSelector biasMetric)) ∧
    (∀ (F G S : Type) (A : Arena F S) (B : Arena G S) (L : LevelMap A B) (sel : Selector G),
        Natural B sel → Natural A (fun f => sel (L.map f))) ∧
    (∀ b, ¬ upperMetric.Selected (false, b)) :=
  ⟨fun _ _ A sel => natural_iff_fixed A sel,
   fun _ _ A sel => natural_iff_factors A sel,
   fun _ _ A m h _ hf s => resource_dichotomy A m h hf s,
   bias_selection_not_natural,
   no_argmin_shift,
   fun _ _ A => naturality_criterion_self_natural A,
   resource_criterion_not_self_natural,
   fun _ _ _ _ _ L _ h => natural_comap L h,
   local_min_not_global⟩

end NRRF784

/-! ## §9  Axiom audit — machine-checked

Only `propext` and `Quot.sound` — propositional extensionality and the quotient axiom behind
function extensionality — ever occur.  `Classical.choice` occurs nowhere: the whole account of
selection is constructive. -/

section Audit

/-- info: 'NRRF784.natural_iff_fixed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms NRRF784.natural_iff_fixed

/-- info: 'NRRF784.natural_iff_factors' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms NRRF784.natural_iff_factors

/-- info: 'NRRF784.invariant_selection_natural' does not depend on any axioms -/
#guard_msgs in #print axioms NRRF784.invariant_selection_natural

/-- info: 'NRRF784.resource_dichotomy' depends on axioms: [propext] -/
#guard_msgs in #print axioms NRRF784.resource_dichotomy

/-- info: 'NRRF784.natural_metric_is_orbit_criterion' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms NRRF784.natural_metric_is_orbit_criterion

/-- info: 'NRRF784.bias_selection_not_natural' does not depend on any axioms -/
#guard_msgs in #print axioms NRRF784.bias_selection_not_natural

/-- info: 'NRRF784.no_argmin_shift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms NRRF784.no_argmin_shift

/-- info: 'NRRF784.naturality_criterion_self_natural' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms NRRF784.naturality_criterion_self_natural

/-- info: 'NRRF784.resource_criterion_not_self_natural' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms NRRF784.resource_criterion_not_self_natural

/-- info: 'NRRF784.natural_comap' does not depend on any axioms -/
#guard_msgs in #print axioms NRRF784.natural_comap

/-- info: 'NRRF784.local_min_not_global' does not depend on any axioms -/
#guard_msgs in #print axioms NRRF784.local_min_not_global

/-- info: 'NRRF784.resource_selection_does_not_transport' does not depend on any axioms -/
#guard_msgs in #print axioms NRRF784.resource_selection_does_not_transport

/-- info: 'NRRF784.nrrf784_consequences' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms NRRF784.nrrf784_consequences

end Audit
