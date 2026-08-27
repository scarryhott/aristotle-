# NRRF781 — The unique closure independently resolves the need for renormalisation

Module: `NRRF781ClosureResolvesRenormalizationTranslationalTruthNotZFC.lean` (namespace `NRRF781`),
registered as a library in `lakefile.toml`. Builds clean, no `sorry`.

## The reading

> Prove our unique closure independently resolves need for renormalization, using not ZFC but
> translational truth.

Renormalisation is treated here as a *relational* statement, not an analytic recipe. A regularised
family is a collection of amplitudes `a i n` — one per member `i` of the family, read at cutoff `n`.
The individual amplitude has no value (it runs away with the cutoff). The classical repair chooses a
counterterm `c n`, subtracts it, and takes the limit — and that repair requires an external
renormalisation condition, because the counterterm is only fixed up to a constant.

## What is proved

**§1 The classical repair is ambiguous.** `shift_scheme`: shifting the counterterm by a constant is
again an admissible scheme. `renormalised_value_not_determined`: it moves *every* renormalised value.
`no_absolute_reading`: hence no assignment of absolute values is forced by the regularised data — an
external condition must be imported. That import is exactly the need for renormalisation.

**§2 All schemes agree on relations.** `difference_scheme_independent`: differences of renormalised
values are the same in every scheme, because the counterterm cancels before the limit is taken.

**§3 The closure needs no scheme, no limit, no cutoff removal.** When the divergence is common to
the members of the family (`CommonDivergence` — universality of the divergent part), the relation
between members is literally constant in the cutoff (`diff_cutoff_independent`,
`relAmp_cutoff_independent`) and equals what any admissible scheme would have produced in the limit
(`rel_eq_scheme_diff`). The headline `closure_resolves_renormalization` collects the three clauses:
the closure reading is total, finite, scheme-free and limit-free; it reproduces the renormalised
relations exactly; and the only thing it drops — the absolute level — was never determined by the
data anyway, so nothing is lost.

**§4 The closure is unique, with no analysis at all.** For value assignments in an arbitrary
additive group: `relRead_shiftInvariant` (the relative reading is invariant under the scheme
freedom), `shiftInvariant_iff_refines` (a reading is scheme-invariant *exactly when* it is a
translation of the relative reading, in the `NRRF772.Refines` sense), `closure_unique` (anything with
the same property is `NRRF772.TransEq` to it), `relRead_not_complete` (the absolute level is exactly
what it drops), and `diffG_cutoff_independent` (the cutoff-freeness of the relation, group-valued).

**§5 A concrete log-divergent family.** `logAmp_diverges`, `logAmp_no_limit`: every member diverges
and has no value. `logAmp_scheme`: minimal subtraction is admissible. `logAmp_rel`: the closure
reading is finite and readable at cutoff `0`, without performing any subtraction, and equals the
renormalised relation (`logAmp_closure_eq_renormalised`).

**§6 The closure is selected, not chosen.** `relRel` is a rigid relational determination built from
the raw data; NRRF775's natural form selector returns the closure reading (`relSel_eq`), and it is
the unique determination (`relSel_unique`). No agent and no external condition enter.

**§7–§8 Not ZFC but translational truth.** The two load-bearing clauses — cutoff-freeness of the
relation and uniqueness of the relative reading — are proved for arbitrary additive groups and audit
to `propext` (+`Quot.sound`) only: no choice, no completion, no limit. The real-valued clauses use
`Classical.choice`, but only through the construction of `ℝ`. §8 contains the `#print axioms` audit.

## Honest scope

* The resolution is stated for families with a *common* divergent part (the universality hypothesis).
  Where the divergence is member-dependent, the relative reading is not cutoff-free, and the theorems
  of §3 do not apply — this is where the hypothesis is load-bearing.
* "Resolves the need for renormalisation" is proved in the precise sense above: the scheme-invariant
  content is obtainable without a counterterm, a limit, or an external renormalisation condition, and
  it is the maximal such content. It is not a claim about any particular physical Lagrangian.
