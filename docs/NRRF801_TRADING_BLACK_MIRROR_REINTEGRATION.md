# NRRF801 trading black-mirror reintegration

## What is unified

The active trading path now has a typed bridge to NRRF801:

```text
identified local quotes
  -> forward closed receipt
  -> price-translation natural form + derived cost + temporal P&L
  -> separately derived local ZMod-4 phase
  -> reciprocal PLUS/MINUS black-mirror test
```

`NRRFTradingBlackMirrorPhaseBridge.lean` maps long and short to the two hands and maps a reciprocal
phase reading by `(hand, phase) -> (inverse hand, -phase)`. The theorem
`PhaseReading.toLife_reciprocal` proves this is exactly `NRRF801.blackMirror`.

This does **not** reverse a `ClosedReceipt`. A receipt records source, venue, instrument, sequence,
and forward observed time. Its reciprocal phase is another reading of the same interface, not a
fictional time-reversed fill.

## What is not unified by assumption

The trading natural form and the NRRF801 phase are distinct layers. For any verified receipt and
any of the four phases, `every_phase_accompanies` constructs a valid combined presentation.
`receipt_does_not_select_phase` then exhibits two different phases carrying the exact same receipt,
cost, and P&L natural form. Profit and cost therefore cannot author the phase.

Similarly, `AdmittedPhaseEvolution` contains the actual evidence that an evolution is bijective
and commutes with `ballStep`; only then does `forced_translation` apply. The running system never
promotes a partial trace into a full one-to-one continuity.

## Runtime realization

The immutable adapter is `experiments/nrrf801_black_mirror_market_phase.py`. Its source is the
content-addressed NRRF780 overlay, itself bound to the locked NRRF767 Bitstamp public-book capture.
For each zero-fee local price ratio `r`, the chart is:

```text
r > 1  -> 1
r = 1  -> 0
r < 1  -> 3 = -1 mod 4
```

The chart reads only a local price relation to the unit origin. It does not read the cost-equality
factor, the cost-completed return, the P&L sign, or a round number. A PLUS/MINUS pair is
`MIRROR_COHERENT` exactly when `minus_phase = -plus_phase (mod 4)`.

The locked run contains 12 rounds and 36 paired readings:

| State | Count |
|---|---:|
| `MIRROR_COHERENT` | 5 |
| `CONTRADICTED` | 28 |
| `OPEN` | 3 |

Only phases 1 and 3 occur. Therefore the current data does not cover the full four-phase ball and
does not establish a total `Ball -> Ball` continuity commuting with `ballStep`. Prediction,
execution, authenticated fills, formal receipt admission, settlement, and profit claims remain
disabled. This is the exact present closure boundary.

## Reproduce

```bash
python3 experiments/nrrf801_black_mirror_market_phase.py verify \
  --source-overlay runs/nrrf780_local_price_global_cost_equality/bitstamp_public_20260826T0221Z \
  --source-run runs/nrrf767_live_paper_trading_bot/bitstamp_public_20260826T0221Z \
  --overlay-dir runs/nrrf801_black_mirror_market_phase/bitstamp_public_20260826T0221Z
python3 -m unittest tests.test_nrrf801_black_mirror_market_phase -v
lake build NRRFTradingBlackMirrorPhaseBridge
```
