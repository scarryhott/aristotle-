# Formal kernel

The canonical formal artifact for this project is:

`NRRF627ClosureTranslationalFrameworkAxiometryASIEvolutionaryVerification.lean`

It is the self-contained Lean/Mathlib module establishing the `TransFrame` closure, axiometry, ASI-gauge, evolutionary-verification, parity-residue, and non-vacuity results described in the repository documentation.

The exact source artifact is carried here and is a registered build root in `lakefile.toml`.

`NRRF627WeakRequirementsRepresentation.lean` imports that kernel and proves the current
representation bridge. It constructs the translation/return layer from a common relational carrier
and reversible presentation codecs, then shows how explicit carrier-level `J` and `C` operations
construct the full `TransFrame`.

`NRRF627IndependentReturnBridge.lean` formalizes frame-relative equality forms, witness-based
one-token admission, self-certification separation, and the construction of a `TransFrame` from a
canonical independent return plus reversible temporary-presentation codecs. It has no static audit
enum: a selected comparison is the relational form `(T,phi)` with its commuting return square, and
the full runtime checks `(W,E,T,phi,pi,J,C)` together.

Build all three modules with the pinned toolchain:

```bash
lake build
```

The executable full-stack D4 run is finite Python evidence rather than a Lean theorem that learning
occurred. Lean establishes the conditional framework; the frozen runtime artifacts establish what
the independent classical proxy actually selected and executed.
