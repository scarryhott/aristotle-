# Experimental Program

## E0 — Static blind D4 translation

Status: **EXPERIMENTAL PROTOCOL — ARISTOTLE RUN UNRESOLVED**.

Two isolated Aristotle sessions formalize square symmetries as permutations and as
`Z/4 ⋊ Z/2` normal forms. A third session receives only the frozen artifacts and attempts the
translation. The complete vertex-action return is committed first. The local return audit and its
`RETURNED`, `CONTRADICTED`, and `UNRESOLVED` fixtures are implemented, but no qualifying Aristotle evidence bundle
has yet been produced. See [`../benchmarks/d4/RUNBOOK.md`](../benchmarks/d4/RUNBOOK.md).

## E0.5 — Independent full-stack classical mathematical agents

Status: **EXPERIMENTAL — EXECUTED**.

Two separate subprocesses learned different D4 operations from different data and hypothesis
languages. Each then executed all 64 products and all 512 associativity cases. Their artifacts were
frozen before a third process searched for a bridge. A fourth process applied the precommitted
return that the translator could not inspect.

The returned relation was:

```text
W_precommit → independent learn → local execute → freeze
             → post-hoc translate → compare the withheld W-square
             → external ReturnAudit record → next basis
```

Its enforced causal order is
`W_precommit ≺ (A,B)_learn+execute ≺ freeze ≺ T_posthoc ≺ ReturnAudit_W(T_posthoc)`. This order is more important than
the raw accuracy totals: neither learner can learn the translator's intended correspondence, and
the translator cannot alter a frozen learned artifact.

The main relative-contact case returned the relation on 8/8 elements and 64/64 products. Abstract
structure alone retained eight isomorphisms and therefore remained `UNRESOLVED`; reversed contact gave a
concrete `CONTRADICTED`; self-certification remained `UNRESOLVED`. Exactly one token was issued, and the accepted
relation supported the next execution basis. See
[`FULL_STACK_RUN.md`](FULL_STACK_RUN.md) and
[`../benchmarks/full_stack_d4/RUNBOOK.md`](../benchmarks/full_stack_d4/RUNBOOK.md).

This closes the classical proxy milestone. It does not close E0's actual Aristotle run.

The structural-only branch tests `A ≅ B` separately from a returned bridge
`A ↔[T, return] B`. Isomorphism without sufficient relative contact stays `UNRESOLVED`; the evaluator does
not arbitrarily select one of eight origins. The reversed-contact branch is `CONTRADICTED`, not merely
unproved, because four explicit contradictions witness failure. Self-certification remains `UNRESOLVED`,
so a claim of identity is not substituted for returned identity.

## E1 — Representation re-expression

Status: **EXPERIMENTAL DESIGN**.

Repeat the independent-generation protocol on nontrivial mathematical benchmarks with materially
different definitions. Establish translations only after generation and compare independently
computed returns fixed before either artifact was seen.

## E2 — Axiom/geometry migration

Status: **EXPERIMENTAL DESIGN**.

Express a structure through related foundations or geometries. Do not define the target return by
copying the source verdict. Determine which bridge assumptions provide reflection as well as
preservation.

## E3 — Open-ended learning and execution

Status: **BOUNDED PROXY EXECUTED; OPEN-ENDED AGENT UNRESOLVED**.

The D4 full-stack run now verifies the causal architecture using finite program-synthesis learners.
The next stage must allow a stronger mathematical agent to modify proof strategy, decomposition,
intermediate representation, and formal language beyond an enumerated hypothesis family. The
return auditor remains an external relation over frozen artifacts and is not replaced by model
confidence.

## E4 — Evolutionary histories

Status: **EXPERIMENTAL DESIGN**.

Generate multiple independently chosen paths between endpoint formalisms. Test path independence
as a prediction. Do not generate paths using `TransFrame.T_comp`, because that would encode the
desired result.

## E5 — Adversarial closure break

Status: **IMPLEMENTED FOR BOTH D4 GATES; UNRESOLVED BEYOND D4**.

Search for transformations `F` with `W(F x) ≠ W(x)`. Preserve three audit records:

- `RETURNED`: every required return and relation closes;
- `CONTRADICTED`: an explicit counterexample exists;
- `UNRESOLVED`: no counterexample exists yet, but required evidence is missing.

The full-stack suite supplies a return-breaking reversed orientation and hash-tampering control.

## E6 — Fibre classification

Status: **CONJECTURED / UNRESOLVED**.

NRRF627 proves parity for its generated reversal walk but does not classify every fibre of `W`.
Determine whether richer language-independent residue exists. A non-`Z/2` fibre is a useful
counterexample to the stronger prose claim that parity is the only invisible content.

## E7 — Necessity theorem

Status: **PARTIALLY PROVED; STRONG FORM UNRESOLVED**.

The current Lean bridge derives the translation-and-return layer from a relational carrier and
reversible presentation codecs. The next target is to derive that carrier/codec representation—or
an obstruction—from weaker principles:

1. no privileged origin language;
2. recoverable comparison;
3. coherent identity and composition;
4. verdict stability under equivalent re-expression;
5. nontrivial representational freedom.

## Evidence rule

Every run must preserve exact inputs and outputs, hashes, environment versions, proof-kernel output,
counterexamples, and unresolved cases. A counterexample counts as successful research; an
undocumented retry selected only because it closes does not.

## Programme-level falsification

The architecture fails if, under increasing representational freedom, post-hoc translation cannot
reliably distinguish:

- independently returned equivalence;
- merely structural equivalence with unresolved relative origin;
- explicit return contradiction; and
- self-certified identity without independent return.

The scale-up protocol must preserve precommit, learner isolation, immutable freeze, post-hoc bridge
construction, and the external audit of the commuting return square. Relaxing those controls would test a different
claim.
