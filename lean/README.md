# Formal Kernel

## Modules

- `NRRF627ClosureTranslationalFrameworkAxiometryASIEvolutionaryVerification.lean` is the exact,
  self-contained NRRF627 source. It imports only Mathlib and contains the `TransFrame`, axiometric
  characterization, ASI/restructuring, evolutionary, parity, model, and bundled capstone theorems.
- `NRRF627WeakRequirementsRepresentation.lean` separates the translation-and-return layer and
  derives it from a common relational carrier plus reversible presentation codecs. Explicit
  carrier-level reversal and curvature operations then extend that construction to a full
  `TransFrame`.

## Status boundary

**PROVED:** the named Lean theorems and constructions in these modules.

**CONJECTURED / OPEN:** derive the common carrier and codecs from weaker observational principles,
rather than accepting reversible codecs as the representation hypothesis.

The weaker-requirements module prints the axioms of its main bridge and inherited characterization
theorems at build time.

## Build

The repository pins Lean and Mathlib to `v4.33.0`.

```bash
lake update
lake build
```

No experimental claim should be marked PROVED merely because a model produced Lean-looking text.
The checked module, toolchain, build log, and `#print axioms` output are the evidence.
