# External Lean reference ledger

This checkout uses its committed closure-translational runtime as the
operative executable specification. The items below are external formal
references: their reported Lean sources are not present in `lean/`, are not
registered by this checkout's `lakefile.toml`, and were not rebuilt here.

The linked Harmonic dashboard request may require authentication. It records
the external report but does not substitute for importing the exact `.lean`
files and dependencies:

- [Harmonic request 068068ee-b720-4df1-a203-571e0928ec3d](https://aristotle.harmonic.fun/dashboard/requests/068068ee-b720-4df1-a203-571e0928ec3d)

## Terminology

IVI is expanded in project prose as **intangible verified information**.
Existing external Lean identifiers containing an older spelling, such as
`IntangiblyVerified`, may remain unchanged for API compatibility. An identifier
name is not treated as a competing definition.

## NRRF639: IVI and translational completion

The external report attributes the following results to
`NRRF639IVITranslationalCompletionClosureThesis.lean`:

- `reach_equivalence_iff_complete` and `complete_iff_reach_symm`;
- `receipt_unique_factorization`, `receipt_is_not_cause`, and
  `resolve_invariant`;
- `ivi_present_iff_discloses`, `no_disclosure_of_not_ivi`, and related
  non-vacuity statements;
- `closure_thesis_iff` and finite examples separating completion from IVI.

Repository status: **REPORTED PROVED OUTSIDE CHECKOUT — NOT LOCALLY
AUDITED**. The bounded runtime uses the distinct executable gate

```text
completion AND LocalIVI_W AND exact reach/equality alignment
```

and does not identify that three-premise proxy definitionally with the
external `ClosureThesis`.

## NRRF640: topological maze and fractal hypotenuse

The external report attributes the following results to
`NRRF640TopologicalMazePreTuringFractalHypotenuse.lean`:

- a wall topology for a symmetric maze line set, including
  `isOpen_iff_wall`, `hull_eq_closure`, `line_ends_fold`, and
  `inseparable_iff_reach`;
- generated-translation orbit characterization `reach_genMaze_iff_orbit`;
- extensional agreement of step enumeration, least wall, passage hull, and
  topological closure in `completion_pre_turing`;
- the completion/maze comparison `complete_iff_systemMaze_reach` and the
  reported quotient fold `translational_completion_is_topological_maze`;
- lattice and staircase results including `hypotenuse_not_a_line`,
  `lattice_dist_eq_l1`, `stairPath_selfSimilar`, `stair_uniform`,
  `stairLength_eq`, `hyp_lt_stairLength`, and
  `fractal_hypotenuse_connection`.

Repository status: **REPORTED PROVED OUTSIDE CHECKOUT — NOT LOCALLY
AUDITED**. “Pre-Turing” is recorded as the reported extensional equality of
mathematical constructions; it is not used here as evidence of historical
priority, causal priority, or an autonomous machine run.

## Required runtime bridge

Before the external results become local formal evidence, this repository
must:

1. import the exact NRRF599 and NRRF633–640 source/dependency chain;
2. run `lake build` and repeat the `sorry`/axiom audit locally;
3. instantiate NRRF640's line, reach, wall, topology, and quotient definitions
   from the frozen runtime artifacts;
4. prove whether the current finite equality-saturation topology equals the
   reported maze wall topology, rather than inferring this from matching
   terminology;
5. retain the distinction between the runtime's return monodromy and any
   future proof-relevant holonomy or homotopy layer.

Until those steps close, external Lean results guide comparison and future
formalization but are not premises of the executable evidence.
