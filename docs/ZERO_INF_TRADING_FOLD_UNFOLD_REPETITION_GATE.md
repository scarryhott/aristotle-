# 0–∞ Trading Fold/Unfold Repetition Gate

NRRF809 integrates the 0–∞ closure as an ordering of equality forms, not as a numerical trading
indicator.

## Formal bridge

For a supplied translation `step`, the bridge defines:

```text
∞ = infPole step  = returnSetoid step  = least internal form
0 = zeroPole      = ⊤                 = greatest internal form
```

`internal_iff_between` proves that a form `E` is internal precisely when

```text
∞ ≤ E ≤ 0.
```

The poles are therefore derived from translational truth. They are not selected by a price,
return, cost, or profit metric. `zeroPole_eq_returnSetoid_const` also proves that the 0 pole is the
closure of a constant return, so both poles are closure equalities of translations.

For the active life beat, `trading_infPole_iff_reactor` identifies the ∞ pole exactly with equality
of local reactor readings. The 0 pole identifies every pair. `trading_zero_ne_inf` proves they are
distinct: the beat closes handedness while retaining the four ball phases.

Folding is `cl step`; unfolding is the forward orbit of `step`. `unfold_stays_in_fold` proves every
unfolded point remains in its fold. `Repeats step x` means that this orbit returns to `x` after a
positive number of steps.

The formal life beat repeats in two turns, and the separately authored action and potential each
repeat in four. This is a theorem about those formal returns. It does not make repeated public
prices into an authored market translation.

## Trading gate

The market interface keeps repetition partial:

```text
authored translation step = none
⇒ fold reading             = none
⇒ unfold reading           = none
⇒ repetition reading       = none
⇒ second-level 00/∞∞       = none
```

This is the key integration result. Time order, numerical similarity, or a recurring quote cannot
silently become `step`. The system must first supply authenticated evidence that one of its own
interactions authored the action or potential translation.

## Locked replay

The NRRF809 ledger derives the following from the locked Bitstamp public books and the verified
NRRF808 ledger:

| Result | Count |
|---|---:|
| Captured rounds | 12 |
| Rounds with ∞-reactor geometry | 11 |
| ∞-reactor fibres | 33 |
| Reciprocal ∞ presentations | 66 |
| Universal 0-pole readings | 12 |
| Authored translation steps | 0 |
| Fold / unfold / repetition readings | 0 / 0 / 0 |
| Second-level readings | 0 |
| Profit assessments | 0 |
| Open commands | 12 |
| Orders / authenticated fills | 0 / 0 |

All commands are `OPEN_ZERO_INF_TRANSLATION`. The result is not that the ∞ path failed to repeat;
there is not yet an authored path on which repetition could be evaluated.

The ledger is in
`runs/nrrf809_zero_inf_fold_unfold_repetition_gate/bitstamp_public_20260826T0221Z`. Exact offline
replay rejects a forged market-time translation even when the attacker recomputes every event
hash and manifest endpoint.

## Source boundary

The reported `NRRF806ZeroInfClosureFoldUnfoldRepetition.lean` and companion note were not present in
the active checkout, the accessible `scarryhott/aristotle-` branches, the currently indexed
repositories, or local synced sources at integration time. The bridge therefore does not claim to
import or audit that exact file. It derives the trading-relevant pole interval and repetition gate
from the locally verified NRRF802 and NRRF808 objects, following the theorem surface supplied in
the report.
