# NRRF810 exchange-authored interactive closure data

NRRF810 operates closure on Bitstamp's public live-order event stream. The source supplies an
`event_id` and `pre_event_id` for every interaction. Those links author the path; wall-clock
adjacency, repeated prices, costs, and profit do not.

For each exchange-authored order identity:

```text
order_created  -> unfold the natural form into the infinity path
order_changed  -> translate within the same form
order_deleted  -> fold the same form back to the zero point
```

The form is the exchange-authored tuple `(channel, order identity, side, subtype)`. Price and amount
remain local presentations carried along its trajectory and never select the form.

## Real interaction data

Five independent live windows were captured on 2026-08-28 from the BTC/USD, ETH/USD, and ETH/BTC
Bitstamp channels:

| Quantity | Count |
|---|---:|
| Exchange-authored events | 39,733 |
| Natural forms unfolded | 19,774 |
| Forms folded back to zero | 18,621 |
| Translations within active forms | 138 |
| Forms open at capture boundaries | 1,153 |
| Events partial because their unfold preceded capture | 1,200 |
| Contradicted forms | 0 |
| Source-chain gaps | 0 |
| Profit assessments | 0 |

Every window returned `CONTINUAL_CLOSURE_WITH_OPEN_BOUNDARY`. Open and partial events are retained;
they are not converted into failure or closure.

The fully replayable canonical window is
`runs/nrrf810_exchange_authored_interactive_closure/bitstamp_live_20260828T155640Z`. It contains
9,809 source-authored events and 4,679 completed natural-form returns. Raw WebSocket messages,
the derived hash-chained ledger, summary, manifest, program hash, and source hashes are retained.
`verify` reconstructs every derived event and summary offline.

`multi_window_summary.json` records the counts and content hashes of all five windows while only
one complete raw ledger is retained in Git. This avoids turning repeated evidence into repository
packaging overhead.

## Boundary

The data establishes interaction-authored lifecycle closure. It does not establish predictive
advantage or profit. The system emitted no authenticated exchange order, used no account
credential, and made no settled-P&L claim.
