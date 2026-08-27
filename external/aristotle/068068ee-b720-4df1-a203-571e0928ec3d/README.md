# Authenticated Aristotle delta snapshot

This directory records the sources retrieved with the official `aristotlelib` client from Aristotle
project `068068ee-b720-4df1-a203-571e0928ec3d`. No API credential is stored here.

The snapshot is deliberately not an active Lake root. It preserves the provider-authored files in
their pinned Lean 4.28/mathlib environment, while the repository continues to build its verified
Lean 4.33 base. `manifest.json` binds each independently authored category to its Aristotle task ID,
and `SHA256SUMS` binds the retained source and note bytes.

The active incremental integrations are
`lean/NRRFTradingDeltaDerivedCostTranslationalClosure.lean` and
`lean/NRRFTradingFullClosureNaturalFormIntegration.lean`. They implement

```text
B_(n+1) = B_n ∪_(verified interface) Δ_n
```

rather than transferring or rebuilding the unchanged base. Its categories are connected by proved
translations, not collapsed into one representation:

```text
quote relation
  → unique selected fill
  → filled local price ball
  → derived zero-hair cost
  → relative-potential P&L assessment
```

The cost never selects the trade. It is computed only after the relational fill has closed, and a
common translation of all local price levels changes neither the derived cost nor the relative
potential. The second bridge derives the unique entry-normalized natural form of that same orbit;
it adds no representation and leaves the empirical profit predicate downstream.
