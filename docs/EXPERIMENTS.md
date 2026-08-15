# Experimental Program

## E0 — Preregistered blind D4 translation

Status: **EXPERIMENTAL — OPEN**.

Two isolated Aristotle sessions formalize the square-symmetry group independently:

- permutation action on four vertices;
- semidirect normal forms `Z/4 ⋊ Z/2`.

The return `W` is frozen first as the complete induced vertex action. After both source artifacts
are byte-frozen, a third session attempts the translator. The gate exhaustively checks 8 element
returns and 64 ordered products. See [`../benchmarks/d4/RUNBOOK.md`](../benchmarks/d4/RUNBOOK.md).

**PROVED BY EXHAUSTIVE FINITE TEST:** the local reference gate classifies its three fixed fixtures
as `TRUE`, `FALSE`, and `OPEN` respectively. This validates the gate implementation, not Aristotle.

**Pending evidence:** no actual Aristotle evidence bundle is represented as complete in this
repository. Until the isolated run, immutable artifacts, Lean builds, and score receipt exist, the
experimental claim remains OPEN.

## E1 — Representation re-expression

Status: **EXPERIMENTAL DESIGN**.

Repeat E0 on nontrivial mathematical benchmarks with materially different definitions. Establish
translations only after generation and compare independently computed returns fixed before either
artifact was seen.

## E2 — Axiom/geometry migration

Status: **EXPERIMENTAL DESIGN**.

Express a structure through related foundations or geometries. Do not define the target return by
copying the source verdict. Determine which bridge assumptions provide reflection as well as
preservation.

## E3 — Full-stack learning and execution

Status: **EXPERIMENTAL DESIGN**.

Allow a classical learning/execution stack to modify proof strategy, decomposition, intermediate
representation, and formal language. The closure evaluator remains an external relation over
frozen artifacts; it is not replaced by the model's confidence. Separate admitted, adversarial,
and unresolved transformations.

## E4 — Evolutionary histories

Status: **EXPERIMENTAL DESIGN**.

Generate multiple independently chosen paths between endpoint formalisms. Test path independence
as a prediction. Do not generate paths using `TransFrame.T_comp`, because that would encode the
desired result.

## E5 — Adversarial closure break

Status: **IMPLEMENTED FOR D4; OPEN BEYOND D4**.

Search for transformations `F` with `W(F x) ≠ W(x)`. Preserve three outcomes:

- `TRUE`: every required return and relation closes;
- `FALSE`: an explicit counterexample exists;
- `OPEN`: no counterexample exists yet, but required evidence is missing.

The D4 suite includes a total sign-erasing map (`FALSE`) and a rotations-only partial map (`OPEN`).

## E6 — Fibre classification

Status: **CONJECTURED / OPEN**.

NRRF627 proves parity for its generated reversal walk but does not classify every fibre of `W`.
Determine whether richer language-independent residue exists. A non-`Z/2` fibre is a useful
counterexample to the stronger prose claim that parity is the only invisible content.

## E7 — Necessity theorem

Status: **PARTIALLY PROVED; STRONG FORM OPEN**.

The current Lean bridge derives the translation-and-return layer from a relational carrier and
reversible presentation codecs. The next target is to derive that carrier/codec representation—or
an obstruction—from weaker principles:

1. no privileged origin language;
2. recoverable comparison;
3. coherent identity and composition;
4. verdict stability under equivalent re-expression;
5. nontrivial representational freedom.

The result should say which NRRF627 laws are necessary, optional, or false.

## Evidence rule

Every run must preserve prompts, exact inputs and outputs, hashes, environment versions, proof
kernel output, counterexamples, and unresolved cases. A counterexample counts as successful
research; an undocumented retry selected only because it closes does not.
