# Derived Interactive Signal Relations

> **Interpretation superseded by NRRF808.** This remains an immutable diagnostic of cross-stage
> route probes. Its route-local completed-return maxima are resource-selected isolations, not
> translational-truth-derived natural forms. See
> [`EXECUTOR_REACTOR_TRANSLATIONAL_TRUTH_REUNIFICATION.md`](EXECUTOR_REACTOR_TRANSLATIONAL_TRUTH_REUNIFICATION.md).

NRRF807 makes the signal itself a relation across two independently recorded interactions. It does
not define a signal inside one price snapshot and then call its accounting identity closure.

## Closure derivation

At stage `t`, the NRRF805 route-local probe and its zero-fee full-route potential are
already committed by the source event hash:

```text
prior potential P_t = zero-fee full-route return selected at t
```

The first route edge is the action and is evaluated only on the order books at `t`. The remaining
return-to-origin edges are the inverse-potential continuation and are evaluated only on the
separately captured order books at `t+1`. This gives a later zero-hair realization `R_(t,t+1)` and
a cost-completed realization `C_(t,t+1)`. Local hair is derived after that interaction:

```text
local hair H_local = zero-fee split result - cost-completed split result
local accounting  = C_(t,t+1) - (R_(t,t+1) - H_local)
global hair H_inf = C_(t,t+1) - (P_t - H_local)
```

When local accounting closes, the global residual simplifies to the relation between stages:

```text
H_inf = R_(t,t+1) - P_t
```

Therefore `H_inf = 0` if and only if the later interaction preserves the previously committed
potential. `InteractiveFlow.globalHair_eq_zero_iff_signalRel` proves this equivalence. The separate
counterexample `accounting_does_not_force_interactive_closure` proves that correct local accounting
does not force the interactive relation to close.

The local ball remains the open reactor: `ballReturn priorLife` lies in the prior reactor and
`hairReturn laterLife` lies in the later reactor. The executor admits only the conjunction of local
accounting closure and cross-stage signal preservation.

## Locked public-book replay

The replay is bound to the immutable NRRF767, NRRF805, and NRRF806 ledgers. The source observations
are 12 hash-chained rounds captured from `2026-08-26T02:20:38.949698Z` through
`2026-08-26T02:20:49.610513Z` from Bitstamp's public grouped order-book endpoints for BTC/USD,
ETH/BTC, and ETH/USD. Eleven rounds contain identified books and one is explicitly open. The cost
translation deducts the source configuration's declared 25 basis points after each leg.

The 11 adjacent stage pairs produced 117 numeric interactive relations across the 9 pairs whose
two sides both had identified books:

| Result | Count |
|---|---:|
| Local accounting closures | 117 |
| Global-hair-zero signal preservations | 74 |
| Nonzero global-hair changes | 43 |
| Positive completed presentations | 0 |
| Open commands | 11 |
| Orders / authenticated fills | 0 / 0 |

The maximum absolute cross-stage global hair was
`0.0002938602495429326083603042168`. The best cost-completed return was
`-0.0048944079063233482101848889620941201` on `USD>BTC>USD`, so the locked sample contains no
profitable completed presentation.

The 74 zero relations are not algebraic necessities. They occur when the later captured books leave
the relevant continuation unchanged. The 43 nonzero relations demonstrate that the same equation
also detects changed interaction. All commands remain open because authenticated execution
authority is unpresented and no completed potential is positive.

## Boundary

This is an adjacent-public-book counterfactual, not an exchange fill. It fixes the candidate at
`t` without future lookahead, applies the first leg to the `t` book and the return continuation to
the `t+1` books, and submits no order. It therefore tests a temporal signal relation on real public
market observations while making no claim about fill probability, latency, market impact, settled
P&L, or guaranteed profit.

The committed evidence is in
`runs/nrrf807_derived_interactive_signal_relations/bitstamp_public_20260826T0221Z` and is replayed
semantically from the three bound source ledgers. A forged cross-stage admission is rejected even
when the attacker recomputes the event hash chain.
