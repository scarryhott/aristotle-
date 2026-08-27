# NRRF782 — Translational truth creates unique isomorphic sets; sizes and potentials are relative absolutes of the closure

**Reading formalised.**

> Translational truth creates unique isomorphic sets. For each closure whose sizes and potentials
> are themselves relative absolutes of closure.

**Module.** `NRRF782TranslationalTruthUniqueIsomorphicSetsSizesPotentialsRelativeAbsolutes.lean`
(namespace `NRRF782`, registered in `lakefile.toml`, imports `NRRF772`). Builds with no `sorry`,
no new axioms, and carries an in-file axiom audit.

## Set-up

A *reading* of a domain `ι` in a group of levels `G` is a function `u : ι → G`: a potential at each
site. *Translational truth* (`TransTruth x y`) says the two readings differ by one global shift.
The *closure* `Closure x` is the set of readings translationally equal to `x`.

Everything is proved for an arbitrary additive commutative group `G` — no real numbers, no
completion, no analysis.

## What is proved

1. **Translational truth is an equality** (`transTruth_refl`, `TransTruth.symm`, `TransTruth.trans`,
   `transSetoid`), so it does create sets: the closures. The closure is the orbit of the shift
   action (`closure_eq_range`), and a reading belongs to its own closure (`self_mem_closure`), so
   closing loses nothing.
2. **The sets are unique.** Two closures are equal or disjoint (`closure_eq_or_disjoint`), and every
   reading lies in exactly one closure (`exists_unique_closure`); equality of closures is exactly
   translational truth (`closure_eq_iff_transTruth`).
3. **The sets are isomorphic, and the isomorphism is unique.** Over a nonempty domain the shift
   witnessing translational truth is unique (`shift_unique`), so each closure is a torsor over `G`:
   `closureEquiv : G ≃ Closure x`, and it is the *only* base-point-preserving, shift-respecting
   enumeration (`closureEquiv_unique`). Hence any two closures — even disjoint ones — are
   canonically isomorphic (`closureIso`, `closureIso_apply`).
4. **Sizes are relative absolutes of the closure.** The size of a closure is the size of the shift
   group (`closure_mk_eq`, `closure_nat_card_eq`): *relative*, because it measures the freedom
   translational truth leaves, and readable only at closure level; *absolute*, because it is the
   same for every closure (`sizes_absolute`) and independent of the representative read
   (`size_representative_independent`).
5. **Potentials are relative absolutes of the closure.** The individual level `u i` is not
   determined: as soon as a nonzero shift exists, every value moves inside the closure
   (`value_not_absolute`). The relative potential `potential x i j = x i - x j` is constant on the
   closure (`potential_invariant`) and conversely determines it (`potential_complete`) — the
   complete invariant. The potentials are precisely the cocycles (`potential_cocycle`,
   `cocycle_iff_potential`), so closures and cocycles correspond bijectively
   (`closure_potential_bijection`).
6. **Strictly finer than bare translation of readings.** Translational truth implies NRRF772
   translational equality (`transTruth_transEq`), but not conversely
   (`transEq_not_transTruth`: `id` and `fun i => 2 * i` on `ℤ` refine each other yet differ by no
   shift). So translational truth in this sense pins down the isomorphism type of the closure — a
   torsor over the shift group — which mutual refinement alone does not.

`nrrf782_answer` collects the clauses in one theorem.
