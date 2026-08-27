# NRRF780 — Local price, global cost equality

NRRF780 corrects the price/cost reading without rewriting the evidence.

```text
price = one local market presentation
cost  = the global returned equality translating that presentation into its completed form
```

“Global” here does not mean a centralized true price or an external authority.
It means the common returned carrier in which entry and exit can be compared
after passing through the same completion interface.

The corrected order is:

```text
local entry price ─complete─→ global entry equality
local exit price  ─complete─→ global exit equality

assessment(global entry equality, global exit equality)
```

There is no primitive operation

```text
isolated price − external cost.
```

## Formal interface

The registered Lean module is
`lean/NRRF780LocalPriceGlobalCostEquality.lean`.

`PriceCostInterface Local Global` supplies only

```text
complete : Local → Global.
```

`LocalPriceGlobalCost` then carries a local price, its global cost equality,
and the equation

```text
complete(localPrice) = globalCostEqual.
```

The carriers are arbitrary. A local price need not be a scalar and the global
form need not be ordered. `completions_eq_of_global_equal` proves that two
different local presentations with the same global equality complete equally;
it does not identify the local presentations literally.

`CompletedTransaction` contains completed entry and exit forms.
`GlobalAssessment` compares only their global equalities.
`assess_eq_completed_locals` proves that the assessment is exactly the
comparison after both local presentations complete, and
`assessment_invariant_under_local_reexpression` proves that changing either
local presentation without changing its global equality cannot change the
assessment.

`PositiveCompletedOutcome` keeps positivity as additional empirical evidence.
Neither a local price nor a completed equality manufactures it.

## Why a correct refactor need not change the numbers

For the multiplicative realization, let

```text
L = local price-route ratio before declared fees
R = already observed cost-completed ratio.
```

The global cost equality relating them is

```text
C = L / R.
```

Completion is therefore

```text
L / C = L / (L / R) = R.
```

`derivedGlobalCostEqual` and `complete_by_derived_global_equal` prove this for
an arbitrary commutative group, without an order or positivity assumption.

This matters: changing the factorization from “net after costs” to “local
price completed through its global cost equality” is a semantic correction,
but it is not a license to change an already observed result. A different
number requires different local data, a different completion map, or a
different interaction.

## Actual Bitstamp public-receipt replay

The executable realization is
`experiments/nrrf780_local_price_global_cost_equality.py`. It verifies the
locked NRRF767 run and uses its exact content-addressed Bitstamp order-book
receipts. For every receipt, orientation, and notional it replays the same
depth walk twice:

1. zero declared fees produce the local price-route form `L`;
2. the recorded declared-fee replay produces the completed form `R`;
3. the overlay derives `C = L / R`;
4. it verifies `L / C = R` to `1e-70` decimal tolerance; and
5. it verifies that the completed residual and its sign equal the source
   candidate result.

The immutable result is in
`runs/nrrf780_local_price_global_cost_equality/bitstamp_public_20260826T0221Z`.

| Measure | Result |
|---|---:|
| Public receipt rounds | 12 |
| Local/global completion records | 72 |
| Numeric completed records | 66 |
| OPEN records retained without a numeric default | 6 |
| Positive numeric residuals | 0 |
| Negative numeric residuals | 66 |
| Signs equal to the source realization | 66 / 66 |
| Minimum derived global cost-equality ratio | 1.0075365054705735… |
| Maximum derived global cost-equality ratio | 1.0075376568379951… |
| Maximum completion identity error | 5 × 10⁻¹¹⁰ |
| Orders / authenticated fills / formal admissions | 0 / 0 / 0 |

The cost-equality ratio is not forced to one fixed `fee³` scalar. It is derived
from the actual zero-fee and fee-completed depth walks, so the downstream
notional and depth effects participate in the equality.

## Interpretation of the unchanged negative signs

The new input has now been applied operationally. The signs remain negative
because the new equation is an exact refactor of the same observed completed
forms. This is a useful result: it locates the remaining trading problem in
the local data, completion map, or interaction/selection policy—not in the
price/cost vocabulary.

It would be invalid to force these residuals positive by defining closure as
positive. Closure states which local forms share a completed equality.
Profit remains a later falsifiable relation between completed entry and exit
receipts.

## Evidence boundary

The overlay is deterministic, hash-chained, bound to the verified NRRF767
source manifest and raw receipts, and independently replayed by its verifier.
Its tests include an internally rehashed semantic forgery, which is rejected.

It remains public-paper counterfactual evidence. The books were acquired by
separate public REST calls and are not an atomic fill. Account balances, the
authenticated fee tier, order authorization, fills, settlement, and profit
are not claimed.
