# NRRF784 — Consequences under conscious selective naturality at level unification, rather than resource-driven metrics

Module: `NRRF784ConsciousSelectiveNaturalityLevelUnificationNotResourceMetrics.lean`
(registered in `lakefile.toml`, builds, no `sorry`, no new axioms, **no `import` line** — only the
Lean kernel is in scope, so no library convention enters the argument).

## The two conventions, made precise

* A **level arena** `Arena F S`: forms `F` with an action of an abelian group `S` of *level
  shifts* (translations; changes of the level at which a form is presented).
* A **selector** `sel : F → Prop` is the verdict "selected".  It is **natural** when
  `sel (s · f) ↔ sel f` for every shift — the verdict survives every change of level.
* A **resource metric** is a cost `F → Int`; its verdict is `Selected f := ∀ g, cost f ≤ cost g`
  ("nothing is cheaper").

Everything below is a theorem in the module, not a gloss.

## The consequences

1. **Naturality is self-consistency of the selector under change of level.**
   `natural_iff_fixed` — shifts act on selectors too, and a selector is natural exactly when it is
   a fixed point of that action.  The criterion is not applied from outside the system; it is
   already invariant inside it.  This is the sense in which the selection is *conscious*: the
   selector is a form of the same arena.

2. **Natural selection is selection at the unification of levels.**
   `natural_iff_factors` — a selector is natural iff it factors through the orbit quotient
   `Orbit A` (forms modulo change of level).  Its content is exactly a predicate on level-unified
   objects.  `Natural.and/or/not/forall_` — the natural verdicts are closed under all
   propositional operations, so they form a logic of their own.

3. **The dichotomy every resource metric faces.**
   * `invariant_selection_natural` — a level-invariant cost selects naturally.
   * `resource_dichotomy` — conversely, if a cost selects naturally then the cost is **constant on
     the orbit of every form it selects**: precisely where the metric was to decide, its numbers
     are level-blind.
   * `natural_metric_is_orbit_criterion` — such a verdict then factors through level unification,
     i.e. it *is* a naturality verdict; the resource numbers add nothing.
   * `bias_selection_not_natural`, `bias_cost_moves` — a two-form arena in which one change of
     level reverses the metric's verdict.  So a resource metric either ranks presentations rather
     than objects, or it decides nothing new.

4. **Resource selection can return no verdict; naturality always can.**
   `no_argmin_shift` — on the level line (`Int` translated by `Int`) with cost = position, *no*
   form is cheapest: the resource convention is silent.  `natural_top`,
   `natural_selection_available` — the naturality criterion is defined and inhabited there.

5. **The criterion applied to itself.**  `metaArena` makes selectors themselves forms of an arena.
   * `naturality_criterion_self_natural` — **naturality satisfies its own criterion**: it is
     natural as a selector of selectors.
   * `resource_criterion_not_self_natural` — "is the argmin-selector of this cost" is **not**: a
     change of level carries the argmin-selector to a selector that is no longer one.  A resource
     convention therefore needs an external unmoved authority fixing the level in which costs are
     counted; the naturality criterion needs none.

6. **Level unification: natural verdicts transport, cheapest verdicts do not.**
   * `natural_comap`, `natural_comap_comp`, `natural_transports` — along any equivariant map of
     levels a natural verdict pulls back to a natural verdict, compatibly with composition: one
     natural criterion is a criterion at every level at once.
   * `local_min_not_global`, `resource_selection_does_not_transport` — an explicit two-level
     system (a binary choice, then its continuation) in which the form selected as cheapest at the
     lower level is *never* part of anything cheapest at the upper level.  Cost verdicts of
     different levels are simply different criteria, with no unification between them.

`nrrf784_consequences` collects (1)–(6) in one statement.

## Axiom audit

§9 of the module passes each headline result through `#print axioms` inside `#guard_msgs`, so the
build fails if the axiom list ever changes.  Only `propext` and `Quot.sound` occur;
`Classical.choice` occurs nowhere — the whole account of selection is constructive.

## Scope

The statements are about the two selection conventions as formalized above: invariance under a
group of level shifts versus minimisation of a cost function.  The counterexamples are explicit
finite (or `Int`-linear) arenas; the positive results (1)–(3), (5), (6) hold for an arbitrary
arena.
