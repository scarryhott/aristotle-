# Verified axiometric ASI architecture

## Status

**Architecture and research protocol.** This note organizes the local Lean
results, source-attested external modules, and bounded runtime controls into a
single succession discipline. It does not claim an autonomous ASI, a universal
truth predicate, or invariance between arbitrary axiom-geometries. Those
boundaries remain governed by [Claim Status](CLAIM_STATUS.md) and the
[external-reference ledger](EXTERNAL_LEAN_REFERENCES.md).

## The unit of verification

A verification level is a published, frozen record:

```text
L_n = (Q_n, A_n, G_n, M_n, Gamma_n)
```

`Q_n` is the registered question-language, `A_n` the axiom presentation,
`G_n` the geometry/perspective presentation, `M_n` the local verifier, and
`Gamma_n` the provenance and audit record. None is silently a final or
privileged language.

At a level, the relevant test is translated relational-answer agreement. It is
deliberately weaker than structural reconstruction:

```text
TruthCompletion_n(x, y)
  = equal translated answers for the admitted questions in Q_n,
    with an admitted return and independent provenance.
```

It can coexist with structural failure or non-unique local presentation. The
Aristotle C2 slot-assembly obstruction is therefore structural scope
information, not a truth verdict. T1 remains `OPEN_TRUTH_BOUNDARY`.

## Successive question languages

Truth completion need not erase every difference between presentations. The
retained, typed difference is the residue `Delta_n`. Form depth measures when
an admitted question stream first separates two forms:

```text
Depth(x, y) = least n at which x and y cease to be truth-equal at level n.
```

The source-reported NRRF668 construction supplies this pattern for its frozen
generated question stream: first separation is unique and its examples
distinguish a coarse unitary reading from a deeper partition reading. This is a
formal result about supplied forms and questions, not a general discovery
procedure or evidence that all residue is meaningful.

Residue and depth create a **candidate** next question, never automatic
admission:

```text
TruthCompletion_n + Delta_n / form depth
  -> candidate q_(n+1)
  -> independent warrant, relevance, nonredundancy, provenance review
  -> Q_(n+1) = Q_n union {q_(n+1)} only if admitted.
```

The warrant must precede knowledge of the desired next truth verdict. A
question selected merely because it produces agreement or separation is
invalid evidence. Without such a warrant, the result remains an open boundary.

## Two independent axes

Each transition must pass both a truth axis and a lineage axis:

```text
ValidSuccession_n = TruthCompletion_n AND PublishedLineage_n.
```

- **Truth axis:** registered answers align under admitted translation and
  return, or a registered answer witnesses obstruction.
- **Lineage axis:** a published record shows that the next frame, verifier,
  and question language derive from admissible prior evidence and can be
  independently replayed.

Truth agreement alone cannot authenticate provenance; provenance alone cannot
turn a false answer relation into a true one. The external NRRF658--660 reports
model bounded derived-verifier and published-succession cases; their source and
relabelling limits still apply.

## Evolving frames without self-grounding

A warranted transition may yield a changed presentation and verifier:

```text
(Q_n, A_n, G_n, M_n, Gamma_n)
  -> published transition record R_n
  -> (Q_(n+1), A_(n+1), G_(n+1), M_(n+1), Gamma_(n+1)).
```

The successor verifier may check mathematics at its level. It is not the
evidence that certifies its own external succession. That evidence is the
independently replayable record `R_n`; self-authored, withheld, contradicted,
or forged records fail the lineage axis. This is anti-self-grounding, not a
prohibition on verifier evolution.

## Truth is not transformation cost

Transformation cost is a separate optimization/audit quantity:

```text
TruthEq_n(x, y)    and    Cost_n(translation).
```

A translation may be truth-preserving and costly, or inexpensive and invalid.
The programme may compare costs among already admissible translations, but may
not use cost to promote an answer into truth or demote a truthful answer. No
universal, basis-invariant transformation-cost object is defined or proved.

## Immediate frontier

The next frontier is an independently preregistered answer-level bridge for
the frozen Aristotle packet: it must supply a warranted correspondence and
non-local return without repairing C2/T1 inputs. Only then can the project
evaluate a truth relation, retain residue, and test a separately published
succession into a changed question-language/frame/verifier on a genuinely
held-out relation.
