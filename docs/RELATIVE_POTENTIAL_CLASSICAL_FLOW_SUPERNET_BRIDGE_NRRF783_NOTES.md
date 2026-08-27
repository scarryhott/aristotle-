# NRRF783 — Relative potential and classical flow in the Supernet

NRRF783 records the exact combined consequence of the reported classical-evaluation NRRF780 and
translational-closure NRRF782 results for the locally checked NRRF781 Supernet.

The reported source files are not available in this checkout or its fetched remote branches.
NRRF783 therefore exposes only the two required certificate surfaces and does not reconstruct the
six classical layers or the shift-orbit development.

## Relative-potential classification

`RelativePotentialBridge` requires two equivalences:

```text
equal returned token readings
  ↔ translational truth
  ↔ equal complete relative-potential fields.
```

The potential field is an arbitrary carrier. It can hold all pairwise differences from the
reported NRRF782 result; NRRF783 does not collapse it to one scalar.

This yields `token_eq_iff_potential_eq`: token equality is exactly equality of the complete
relative-potential field. The statement is conditional until the exact NRRF782 source is imported
and instantiates the bridge.

## Classical flow surface

`ClassicalFlow` retains only the downstream result of the reported six-layer evaluator:

```text
net = priceMove - cost,
0 ≤ cost.
```

The bid, ask, fill, mark, signed size, and fee constructions remain the responsibility of the exact
NRRF780 source. This adapter neither invents them nor substitutes the earlier NRRF780Local
price/global-cost interface for them.

The earlier local adapter was moved from namespace `NRRF780` to `NRRF780Local`. That prevents its
collected theorem from colliding with the reported classical module's own
`NRRF780.nrrf780_answer` when the exact source becomes available.

## Inside one closure occurrence

An NRRF781 `TradingOccurrence` already proves equal token readings at entry and exit. Through the
relative-potential bridge, `OccurrenceFlow.potential_eq` proves that their complete potential
fields agree. Any numerical reading of those fields therefore has zero movement.

The classical equation reduces to

```text
priceMove = 0,
net = -cost,
net ≤ 0.
```

These are `priceMove_eq_zero`, `net_eq_neg_cost`, `net_nonpositive`, and `not_profitable`.

This identifies the earlier architectural error precisely: one closure-preserving interaction is
an execution/internal translation. Asking that same interaction to generate positive P&L asks a
return-invariant relation to change its own returned potential.

## Across closure classes in time

`TemporalFlow` compares completed global forms in one Supernet without assuming that they have the
same token return. It derives

```text
0 < net ↔ cost < relativePotential(exit) - relativePotential(entry).
```

Thus profit is a temporal relation whose invariant potential movement exceeds friction.

`profit_requires_token_change` proves that positive flow forces distinct returned token classes.
`profit_requires_new_translational_closure` states the same boundary in the reported NRRF782
language: temporal endpoints of a profitable flow cannot be translationally true inside one
closure orbit.

This does not mean a profitable trade violates the framework. It means continual trading moves
between successively completed closures. Each local execution may close internally while the
market's relative-potential form changes between stages.

## Result

`nrrf783_answer` collects:

- exact negative friction within one closure occurrence;
- nonpositive internal net flow;
- the temporal profit inequality; and
- necessary returned-token change for positive temporal flow.

The module builds without `sorry`. Its collected theorem uses only
`propext`, `Classical.choice`, and `Quot.sound`, inherited through the locally verified Supernet
chain.

No historical price run is relabelled by this theorem. A valid empirical instantiation still needs
synchronized, causal observations, an independently supplied potential bridge, declared costs,
and held-out temporal evaluation.

