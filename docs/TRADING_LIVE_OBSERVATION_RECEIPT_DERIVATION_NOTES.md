# Trading Live Observation Receipt Derivation

The active trading closure now has a typed boundary from a source-identified local quote to a
completed temporal receipt. The implementation is
`lean/NRRFTradingLiveObservationReceiptDerivation.lean`, namespace `NRRFTradingReceipt`.

## What closes when

An `OpenReceipt` contains only the entry observation, orientation, positive magnitude, and entry
fee. Its `entryTrade` is selected by the local quote relation:

- long entry: buy at the entry ask;
- short entry: sell at the entry bid.

There is no exit observation, return, or profit field in this type. Consequently the theorem
`entry_selection_no_future` is not a statistical promise: it follows from the construction's data
dependency. Changing a later observation cannot change an already selected entry.

A `ClosedReceipt` adds an exit observation only when its source, venue, and instrument match the
entry and its sequence is strictly later (with non-reversed observation time). The opposite local
quote relation then closes the exit:

- long exit: sell at the exit bid;
- short exit: buy at the exit ask.

The source, venue, instrument, sequence, and observation time are retained in the receipt. No
future outcome is used to choose either fill.

## Derived cost and assessment

For every closed local leg,

```text
zeroHair = fee + (selectedFill - localMark) * signedQuantity.
```

The bid–mark–ask condition, positive magnitude, and nonnegative fee prove
`entryHair_nonnegative` and `exitHair_nonnegative` for both orientations. Cost is downstream of
the local fill and is not a resource metric selecting the fill.

Only after the later compatible observation arrives is P&L defined:

```text
net = signedEntryQuantity * (exitMark - entryMark)
      - (entryZeroHair + exitZeroHair).
```

This is `net_eq_relativePotential_sub_hairs`, and
`profitable_iff_relativePotential_exceeds_hairs` states its exact positive case. If the exit mark
equals the entry mark, `returning_nonpositive` proves the receipt cannot be profitable.

## Connection to the full closure

The derived receipt becomes the existing `TemporalClosure` with the two already closed local legs.
The representation-free `naturalForm` translates the entry mark to zero while preserving total
hair and net P&L (`naturalForm_preserves_assessment`). Every admissible closure derivation is forced
to return that same form (`derivation_forced`).

`live_receipt_derivation` collects unique entry and exit selection, nonnegative derived hairs, the
exact P&L equation, the profit condition, and uniqueness/invariance of the natural form.

## Delimitation

This module proves the observation-to-receipt interface. It does not claim that closure guarantees
profit, does not infer a future mark, and does not turn candle OHLC values into bid/ask observations.
An empirical adapter must document how an exchange dataset supplies bid, ask, mark, fees, and event
ordering before it may construct these receipts. Once constructed, the equations above leave no
freedom in their assessment.
