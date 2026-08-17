# Closure-native relative-completion run

Frozen local presentations are content-addressed receipts, not absolute
axiomatic identities. The runtime evaluates only an admitted interface through
a named translation and independently supplied return.

```text
frozen A -> translation T -> independent return rho
         -> preservation / reflection / recovery
         -> relative completion, opening, or obstruction
```

It contains two two-point overlap controls:

1. `g0(x)=0` and `g1(x)=1` do not literally glue. Translation by `+1` plus an
   inverse return yields `RELATIVE_COMPLETION_WITH_OPENING`: the relation
   recovers, while residue `1` remains a next opening.
2. `f0(x)=x` and `f1(x)=x` literally glue. A non-reflecting return collapses
   two admitted positions, yielding `RELATIVE_OBSTRUCTION`.

It also contains a separate identity-round control. It recovers every admitted
position with neutral residue but moves none, so it is classified
`FROZEN_AXIOMETRY`, not translation.

Thus freezing is methodological; completion is relational. This finite control
does not assert arbitrary sheaf gluing, a global topos, or a result for the
frozen Aristotle Phase B/C frames.

NRRF653 gives the corresponding external formal diagnosis: recovery alone is
blind, because a frozen identity round and a genuinely translating round can
both recover. The runtime therefore records whether the admitted presentation
moves and requires preservation, reflection, recovery, and an explicit bridge
rather than treating a zero residue as sufficient evidence of translation.

Run it with `python3 -m experiments.closure_native_relative_completion`.
