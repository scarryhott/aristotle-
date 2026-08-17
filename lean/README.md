# Formal kernel

The canonical locally audited formal artifact for this project is:

`NRRF627ClosureTranslationalFrameworkAxiometryASIEvolutionaryVerification.lean`

It is the self-contained Lean/Mathlib module establishing the `TransFrame` closure, axiometry, ASI-gauge, evolutionary-verification, parity-residue, and non-vacuity results described in the repository documentation.

The exact source artifact is carried here and is a registered build root in `lakefile.toml`.

## Important formal boundary: supplied frames versus closure-native evolution

`TransFrame` is a **conditional supplied-frame theory**. Its local languages/frames and their `W/E/J/C` structure are already constituted when pairwise translations are evaluated. It establishes that no supplied language must be privileged as an absolute origin and proves the consequences of coherent translation and return.

It does **not by itself prove the stronger closure-native thesis that completed translation and independent return generate or alter the axiometry of the next frame**.

The project therefore distinguishes:

```text
origin-free comparison of supplied frames
    !=
closure-native evolution of the frames themselves
```

and:

```text
experimental evidence freeze
    !=
metaphysically frozen axiometry.
```

The next formal target is an evolving layer with objects such as `ClosureState`, `EpisodeProposal`, `ReturnEvidence`, `CompletedEpisode`, and `nextFrame`, where a completed episode may derive `F_(t+1)` with a genuinely changed admitted equality/geometry while preserving immutable relational lineage from `F_t`.

This work is specified in [`../docs/CLOSURE_NATIVE_AXIOMETRY_EVOLUTION.md`](../docs/CLOSURE_NATIVE_AXIOMETRY_EVOLUTION.md). It is currently a **formalization and experiment target**, not a theorem already supplied by `TransFrame`.

## Current bridges

`NRRF627WeakRequirementsRepresentation.lean` imports the kernel and proves the current representation bridge. It constructs the translation/return layer from a common relational carrier and reversible presentation codecs, then shows how explicit carrier-level `J` and `C` operations construct the full `TransFrame`.

`NRRF627IndependentReturnBridge.lean` formalizes frame-relative equality forms, witness-based one-token admission, self-certification separation, and the construction of a `TransFrame` from a canonical independent return plus reversible temporary-presentation codecs. It has no static audit enum: a selected comparison is the relational form `(T,phi)` with its commuting return square, and the full runtime checks `(W,E,T,phi,pi,J,C)` together.

`NRRF631RuntimeFrameConditionalBridge.lean` makes the executable frame boundary explicit: `ReferenceFrame` is admitted equality, `ResolvedIn` is quotient factorization, and `GeomEquiv` preserves and reflects equality. `openIn_iff_exists_separating_pair` proves that every `OpenIn` claim is equivalent to explicit data `x ~ y` with unequal question values. `assumeAxiomGeometry` installs a supplied `Setoid` as the exact local evaluation frame without adding an axiom; `resolvedIn_assumed_geometry_iff` confirms that no external equality is substituted. Cross-frame transport still requires a later `GeomEquiv`.

Build all four modules with the pinned toolchain:

```bash
lake build
```

The executable full-stack and paired-comparison D4 runs are finite Python evidence rather than Lean theorems that learning occurred. Lean establishes the conditional framework; the frozen runtime artifacts establish what the independent classical proxies actually selected and executed.

NRRF599 and NRRF633–640 are external formal references, not build roots in this checkout. Their reported theorem names and source status are recorded in `docs/EXTERNAL_LEAN_REFERENCES.md`. They must be imported with their exact dependencies and rebuilt before any runtime-to-NRRF639/640 bridge is labelled locally machine-checked.
