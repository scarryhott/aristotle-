# NRRF797 — How the unified work closes specific constraints, variables and scenarios of QG

Machine-checked module: `NRRF797UnifiedWorkClosesQGConstraintsVariablesScenarios.lean`
(added to `lakefile.toml`; builds with no `sorry` and no warnings; the axiom audit at the end of
the file is machine-checked — every headline result depends only on `propext`, `Classical.choice`,
`Quot.sound`).

Nothing new is assumed. The module takes the objects the earlier work already built — the local
relation `LocalRel` with its scale reading `divg`, hair reading `hair = curl / 2` and neutral
(shear) sector `shearPart` (NRRF683/NRRF791/NRRF793), the seam field (NRRF791), the loop-sensor
states with `gravRel` and `phase` (NRRF786/NRRF794), and the inversion `relInv`, the self limit,
the bracket `entangle` and the `Demon` (NRRF796) — and names the *specific* items being closed:
one variable set, three constraints, seven scenarios.

## The variables

`qgVars A = (divg A, hair A, shearPart A)` — the scale variable, the hair variable, the neutral
variable.

* `qgVars_injective`: the three variables fix the relation. There is no hidden fourth datum.
* `qgRel`, `qgVars_qgRel`, `qgVars_surjective`: the variables are *free* — every admissible triple
  (any scale, any hair, any neutral relation) is realised by an actual relation. So the set is
  neither redundant nor over-constrained; `qgVars_independent` moves each one with the other two
  held fixed.
* `qgVars_relInv`: under the one inversion the triple transforms by `(−, +, −)` — scale reverses,
  hair is preserved (the inversion equality), the neutral variable reverses.

## The constraints

The constraint functions are the readings themselves:
`hamiltonianConstraint = divg` (scale/source), `gaussConstraint = hair` (rotation),
`diffeoConstraint = shearPart` (neutral). All three are linear (`constraints_linear`).

* One at a time: `ham_solution_iff` (no dilation sector), `gauss_solution_iff` (no hair sector),
  `diffeo_solution_iff` (scale plus hair only).
* Pairwise, the solution sets are exactly the three sectors: `ham_gauss_solution_iff` gives the
  neutral field, `gauss_diffeo_solution_iff` the pure scale relations, `ham_diffeo_solution_iff`
  the pure hair relations.
* `constraints_closed`: **the joint constraint surface is the single point `0`.** This is the self
  limit read backwards — `divg A ^ 2 / 3 + (∑ i, curl A i ^ 2) / 2 + nrm2 (shearPart A) = nrm2 A`
  leaves nothing over once all three constraints hold.
* `constraint_surfaces_nontrivial`: none of the three is vacuous and none is empty, so the closure
  above is a real constraint, not a triviality.
* Constraint algebra: `ham_entangle` (a bracket carries no source), `entangle_neutral_pure_gauss`
  (the bracket of two neutral relations is pure hair — brackets of the neutral constraint close on
  the Gauss sector), `entangle_scale_central` (the scale sector is central), `entangle_eq_zero_iff`
  (brackets vanish exactly on commuting pairs). Collected in `constraint_algebra_closes`.
* `constraints_relInv`: the constraint set is carried to itself by the one inversion.

## The scenarios

1. **Pure gravity** (`scenario_pure_gravity`, `scenario_pure_gravity_absolute`): the gravitational
   relation solves the Gauss and neutral constraints identically; its Hamiltonian constraint value
   *is* the ball translation, and that value recovers it exactly.
2. **Quantum phase** (`scenario_phase_returns`, `scenario_ball_does_not_return`): the hair sector
   returns after one loop; the ball sector never returns.
3. **Approach to a singularity** (`scenario_singularity_unbounded`): along the seam field the hair
   stays parallel to the single direction `v` while both readings leave every bound.
4. **At the seam** (`scenario_seam_all_constraints`): at `tan(π/2)` the scale and Gauss constraints
   hold, only the neutral variable is left, and the relation is still nonzero when the background
   carries shear. The seam is where the constraint surface is reached, not where the relation ends.
5. **Entanglement** (`scenario_entanglement`): the order defect of two translations is sourceless
   pure hair, antisymmetric in the pair, zero exactly on commuting pairs, genuinely nonzero.
6. **Superposition and demons** (`scenario_superposition`, `scenario_demon`): the hair variable is
   linear, interference leaves a nonzero neutral residue, and a hair-preserving demon that never
   loses source on the neutral field gains none.
7. **Finite observation** (`scenario_finite_observation`): no finite battery of loop tests fixes the
   state, the whole family fixes it exactly, and the geometric configuration `qgConfig` makes
   precisely the identifications the sensors make.

`nrrf797_closure` collects the clauses in a single statement.

As throughout the project, the physical words name the constructions defined in these modules;
every claim is a claim about those constructions and nothing is asserted about physical quantum
gravity as such.
