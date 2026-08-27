# Natural-form selection throughout the trading interface

NRRF803's mathematics does not require an equality form to remain external or fixed. The active
bridge therefore uses a `FormSchedule`: at every round, and from the current local phase reading,
it may select a different equality. Every selected equality is required to be natural for the
black-mirror return. The old fixed presentation is recovered by `constantSchedule`; the canonical
return-generated equality is produced directly by `canonicalSchedule`, with no external equality
datum.

The distinction that matters in trading is naturality versus exactness. NRRF803 proves the
return-generated equality is the finest natural equality, so exact reciprocal closure is visible
through every natural selected form. The converse is false: a coarser form can identify extra
states. `naturality_alone_can_overidentify` gives the sharp example—total equality is natural but
accepts a pair that is not reciprocal. A selected form can replace exact closure only with the
additional `FaithfulAt` evidence; `selected_iff_canonical` then proves the two relations equivalent.

This prevents result-driven form changes from rewriting the market audit. A natural form may
select throughout as a perspective. It may not turn `DISTINCT_CLOSURE` or `OPEN` into an exact
trade witness unless its translation back to the canonical closure is supplied. The current
runtime therefore retains the canonical NRRF802 classification: 5 `SAME_CLOSURE`, 28
`DISTINCT_CLOSURE`, and 3 `OPEN` in the locked 36-pair Bitstamp phase audit.

Finally, form selection is not allowed to author price, cost, or P&L. `assessedTrade` ignores the
schedule and evaluates the authenticated receipt's existing natural form.
`assessedTrade_independent`, `assessedTrade_net`, and `assessedTrade_hair` prove that changing the
selected equality cannot alter the receipt-derived result.
