# Experimental Program

## E1 — Representation re-expression

Take independently generated formal problems and produce materially different encodings. Establish explicit translations and test whether independently computed verification returns agree.

**Pass:** invariant recovered across re-expression.

**Fail:** counterexample identifies a representation-sensitive verdict.

## E2 — Axiom/geometry migration

Express a mathematical structure through different but related foundations or geometries. Do not define the target return by copying the source verdict. Ask which weaker bridge assumptions are sufficient for reflection as well as preservation.

## E3 — Self-improvement simulation

Allow an agent to modify proof strategy, intermediate representation, decomposition, and language. Separate transformations known to preserve return from transformations with unknown status.

Measure whether verification survives capability change without constraining the agent to syntactic identity.

## E4 — Evolutionary histories

Generate multiple paths between the same endpoint languages. Test `route_eq_direct` as an empirical/runtime prediction rather than only a consequence of assumed composition coherence.

## E5 — Adversarial closure break

Search specifically for transformations `F` where `W(F x) ≠ W(x)`. Classify each result as genuine verification failure, evidence that `W` encoded a presentation artifact, a missing translation/coherence hypothesis, or an OPEN obstruction.

## E6 — Fibre classification

NRRF627 proves parity for the reversal walk but does not classify every fibre of `W`. Determine whether richer language-independent residue exists. This directly tests any stronger claim that Z/2 is the only invisible content.

## E7 — Necessity theorem

Attempt to derive a TransFrame-like structure from weaker principles:

1. no privileged origin language;
2. pairwise recoverable comparison;
3. identity and compositional coherence of comparison;
4. a verdict stable under equivalent re-expression;
5. nontrivial representational freedom.

The target is a theorem showing which closure/return laws are necessary, which are optional, and which are false.