# Classical-versus-Closure Comparative Runtime

## Purpose

This benchmark compares two **verification architectures** over the same frozen mathematical
artifacts. It does not compare a weak classical model with a stronger closure model, and it does
not claim that either executable arm is an actual ASI.

The fixed-frame arm performs local group/kernel-style checks and a strong conventional baseline:
it enumerates and verifies every ordinary cross-presentation isomorphism. The closure arm receives
the same artifacts and raw candidate maps, but no verdict from the fixed-frame arm. It proceeds in
the precommitted order:

```text
precommitted local axiom-geometry assumptions
  → internal evaluation and frozen frame equalities
  → raw candidate T
  → GeomEquiv admission by equality preservation and reflection
  → explicit translational form (T,phi,pi)
  → W,E,J,C and operation naturality
  → quotient ResolvedIn or witnessed OpenIn
  → next-basis transfer
```

`T` is candidate data before admission. It becomes an admitted translation only when the
`GeomEquiv` predicate and downstream laws are verified. The discrete frame is a same-question
frame-relativity control; it is not the definition of classical mathematics.

## Circularity guard

Each local equality assumption and each total question must be committed before learning and
cross-frame search. The frame process instantiates and audits the declared relation in its own
language; it may reject an unsupported or incoherent geometry but may not replace it. Constructing
or revising an equality after seeing `T` tests compatibility by design and invalidates the
comparison. Both arms receive one content-addressed input bundle, including both assumption
protocols, and each runs in a fresh subprocess. Neither arm receives the other's report.

The baseline is deliberately not a strawman. It must accept all valid D4 isomorphisms, including
noncanonical and orientation-reversing maps, and it must reject the sign-erasing deformation by an
ordinary bijection/homomorphism counterexample.

## Interpretation

The bounded proxy asks whether the closure arm records additional auditable relations—not whether
ordinary mathematics is incapable of expressing them. A frame-qualified result counts only when
it includes its frame, question, quotient factor or explicit separating witness. Missing comparison
data is `PENDING_COMPARISON`; structural non-selection is `UNSELECTED_COMPARISON`; neither is
`OpenIn`.

Here “all closure forms follow” means the runtime's declared return, orientation, curvature,
quotient, and frame-question relations are downstream of admitted translation. It does not claim
to classify every closure operator or equality geometry in mathematics.

Every candidate result must include `explicit_translational_form`; every question result must
include `explicit_relational_closure_form`; and the next-basis result must cite the exact selected
translational-form ID. See [`../../docs/ASSUMED_AXIOM_GEOMETRIES.md`](../../docs/ASSUMED_AXIOM_GEOMETRIES.md).

## Commands

```bash
python3 experiments/classical_vs_closure_asi.py --assert-reference
python3 -m unittest discover -s tests -v
```

The command regenerates `runs/classical_vs_closure/latest/`. A later Harmonic/Aristotle execution
must replace the D4 source fixture with independently generated richer systems while preserving the
same freeze, budget, question, comparison, and evidence boundaries.
