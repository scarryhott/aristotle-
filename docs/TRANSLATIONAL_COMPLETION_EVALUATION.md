# Translational-completion evaluation

## Purpose

This document is the active evaluation contract for the general framework.
It corrects a recurring category error: a frozen language is an auditable
finite interface, not the truth that completion must literally reconstruct.

The framework evaluates how the registered definitions of two bounded
presentations translate into one another.  Completion is equality of the
resulting relational answers under an admitted translation; it is not literal
identity of local terms, bases, signs, endpoints, trajectories, or carriers.

## A bounded frozen language

For a frozen comparison, write

```text
L = (P, Q, D, A)
```

where:

- `P` is the declared presentation interface and its named roles;
- `Q` is the finite registered family of closure questions;
- `D` is the declared local definitions and operations used to answer `Q`;
- `A` is the evidence/provenance boundary, including exclusions and
  abstentions.

Freezing `L` prevents a translator from retrospectively changing `P`, `Q`,
`D`, or `A` to fit a desired result.  It does **not** make that finite
vocabulary an absolute language, a privileged global basis, or a complete
description of truth.

## Evaluation by equal translation

For two frozen languages `L_A` and `L_B`, an evaluation candidate is:

```text
E = (T, rho, Align, Delta, Gamma)
```

where:

- `T` is an admitted forward translation;
- `rho` is an independently generated return;
- `Align` states how the registered questions of the two limited languages
  are compared;
- `Delta` is the retained residue, orientation, or non-unique reopening
  record; and
- `Gamma` is independent confirmation or a published audit record.

The truth-level predicate is deliberately relational:

```text
TruthEq_LA_LB(E)
  := for every admitted aligned question q,
       answer_LA(q) and answer_LB(Align(q), T, rho)
       agree in the registered closure relation.
```

`TruthCompletion(E)` requires `TruthEq`, independent return, provenance, and
no registered contradiction to that relational equality.  It explicitly
permits different local implementations, local/global readings, opposite
orientation, nonzero residue, and multiple admissible reopenings.

Thus the intended inference is:

```text
equal translation of registered relational answers
    => bounded truth-level completion
```

not:

```text
same slots / same trajectory / same endpoint label / same carrier
    => completion.
```

Conversely, matching markers or matching one isolated probe cannot certify
completion without the registered answer family and return lineage.

## Terminal classifications

The active protocol uses these terminal outcomes:

| Classification | Meaning |
| --- | --- |
| `TRUTH_COMPLETION` | An admitted translation, independent return, alignment, and confirmation establish `TruthEq` for the registered scope. |
| `TRUTH_OBSTRUCTION` | A retained witness contradicts `TruthEq` itself for an admitted aligned question. |
| `OPEN_TRUTH_BOUNDARY` | The frozen language, alignment, return, or confirmation is insufficient to decide `TruthEq`. |
| `INVALID_LEAKAGE_OR_SELF_CERTIFICATION` | The alleged independent evidence was derived from the translator, evaluator, or desired verdict. |

The conclusion is always scoped to the registered limited languages.  It may
never be promoted automatically to whole-frame identity, universal language
independence, `GeomEquiv`, IVI, topology naturality, or empirical transfer.

## Relation to the frozen Aristotle interface

The existing B2/C1 and C2 artifacts remain immutable evidence.  C2 asks a
narrower question: whether its admitted slots support a single-valued,
structural cross-frame assembly.  Its obstruction or interface boundary is a
result about that representation layer.  It is neither a `TRUTH_OBSTRUCTION`
nor a `TRUTH_COMPLETION` unless a separately registered `Align` and
truth-level contradiction or confirmation make it one.

The next admissible frontier protocol is therefore a `TruthAssembly` over the
frozen evidence:

```text
TruthAssembly = (T, rho, Align, Delta, Gamma).
```

It must retain every B2/C1/C2 exclusion and witness, must not repair frozen
roles, and must test relational-answer equality rather than request
single-valued reconstruction of local slots.

## Formal status

The local runtime implements bounded proxies of this discipline.  The external
NRRF662 source-attested module supplies a formal model in which completion is
translation of an answer language and is blind to basis, trajectory, and
endpoint markers.  Neither source attestation nor the bounded proxies derives
the appropriate question language, contact relation, or alignment for an
arbitrary independently generated frame pair.  Those remain the core
frontier obligations.
