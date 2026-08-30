# NRRF833 — Accurate Fees, Pricing, and Closure Trading Learning Loop

## Result

This module is a deterministic, execution-free simulator for the trading closure

\[
\text{market evidence}
\to \text{fee tier}
\to \text{admissible route}
\to \text{counterfactual fills}
\to \text{cash/inventory receipt}
\to \text{accounting closure}
\to \text{learner update}
\to \text{next admissible route}.
\]

It does **not** submit broker orders. It is designed to sit beneath the existing NRRF833 Alpaca paper-maker protocol so the paper loop no longer assumes a generic fee or a single quoted price.

The implementation is:

- `experiments/nrrf833_fee_pricing_closure_learning.py`
- `tests/test_nrrf833_fee_pricing_closure_learning.py`
- `benchmarks/nrrf833_fee_pricing_closure_learning/alpaca_btcusd_orderbook_20260830T171345Z.json`
- `reports/nrrf833_fee_pricing_closure_learning_validation.json`

## 1. The closure relation is an accounting identity, not a profit label

For a long round trip, the simulator proves numerically on every admitted receipt:

\[
\begin{aligned}
\text{midpoint directional P\&L}
={}&\text{realized cash P\&L}\\
&+\text{entry execution cost}\\
&+\text{exit execution cost}\\
&+\text{buy fee valued at the exit midpoint}\\
&+\text{sell fee}\\
&+\text{declared fixed costs}.
\end{aligned}
\]

It independently closes:

\[
\Delta \text{cash} = \sum \text{quote deltas} - \text{fixed costs},
\qquad
\Delta \text{inventory} = \sum \text{base deltas}.
\]

A receipt is admitted to learning only when:

1. cash conservation closes;
2. base-inventory conservation closes;
3. the cost decomposition closes at the declared decimal precision;
4. no unresolved inventory remains;
5. the receipt hash and enclosing event hash both close against their predecessors.

A missing maker fill closes neutrally as `CLOSED_NO_ENTRY_FILL` and may update only the fill-probability relation. Open inventory, stale fee evidence, crossed books, insufficient depth, post-only crossings, and tampered receipts fail closed.

## 2. Exact fee semantics

The built-in fee schedule is the official Alpaca crypto maker/taker schedule verified on 2026-08-30:

| Effective prior 30-day crypto volume | Maker | Taker |
|---:|---:|---:|
| $0–$100,000 | 15 bps | 25 bps |
| $100,000–$500,000 | 12 bps | 22 bps |
| $500,000–$1,000,000 | 10 bps | 20 bps |
| $1,000,000–$10,000,000 | 8 bps | 18 bps |
| $10,000,000–$25,000,000 | 5 bps | 15 bps |
| $25,000,000–$50,000,000 | 2 bps | 13 bps |
| $50,000,000–$100,000,000 | 2 bps | 12 bps |
| $100,000,000+ | 0 bps | 10 bps |

Source: `https://docs.alpaca.markets/us/docs/crypto-fees`.

Alpaca charges the fee on the asset credited by each trade. Therefore:

- a BTC/USD buy pays its fee in BTC and receives less BTC than the gross fill quantity;
- a BTC/USD sell pays its fee in USD and receives less USD than the gross sale proceeds.

The simulator therefore tracks cash and inventory separately. It does not merely subtract `fee_bps × starting cash` after the cycle.

The rolling-volume ledger also follows the published next-trading-day tier relation: volume traded today is recorded today but changes the effective tier beginning tomorrow. Fee schedules have a verification-age gate. A stale schedule is rejected unless a caller explicitly overrides the gate.

The public documentation does not specify every crypto fee-rounding detail. The simulator preserves the exact theoretical fee under the published rate and does not invent a venue rounding rule. Requested prices and quantities are constrained by the captured instrument increments. Quantities are reduced to a fee-compatible increment when necessary so a received-asset fee does not create untradeable simulated dust.

## 3. Pricing is derived from displayed depth

For a taker order, the simulator walks each displayed level until the requested base quantity is filled. It records:

- every price/quantity slice;
- gross quote notional;
- VWAP;
- half-spread cost relative to the arrival midpoint;
- incremental depth slippage relative to the same-side best price;
- unfilled quantity when partial filling is explicitly allowed.

A quote budget is a hard exposure cap. The base order quantity is solved from the full ask ladder and rounded down before execution, so the simulated gross entry notional cannot exceed the declared budget.

For a post-only maker order, the simulator requires a nonmarketable limit price. Queue-ahead quantity is depleted by ordered cancellation and aggressive-trade events. Only trade flow reaching the maker price can fill the order. After a maker-exit timeout, only the actually filled entry inventory is hedged, and the unfilled exit remainder is sold as a taker. Maker and taker portions retain separate fee rates and receipts.

## 4. The learning loop

The learner state contains:

- taker exit execution-cost estimate;
- positive model-error estimate;
- absolute model-error estimate;
- signal-optimism estimate;
- maker adverse-selection estimate;
- independent beta posteriors for maker entry and maker exit fills;
- a derived uncertainty buffer.

For each episode, it computes two full-cost candidates:

\[
\text{taker net edge}
= \text{calibrated signal}
- \text{multiplicative fee floor}
- \text{entry execution cost}
- \text{learned exit execution cost}
- \text{uncertainty buffer},
\]

and

\[
\text{maker net edge}
= \text{calibrated signal}
- \text{expected maker/fallback fee floor}
- \text{maker price relation}
- \text{fallback execution relation}
- \text{maker adverse selection}
- \text{uncertainty buffer}.
\]

The admitted action is the positive route with greatest expected utility; otherwise it is `HOLD`. Learning occurs only after the receipt returns through the accounting closure. A high apparent gross signal is therefore not enough to cause an action.

## 5. Captured Alpaca BTC/USD audit

Captured public order book:

- timestamp: `2026-08-30T17:13:45.858877Z`
- best bid: `$79,126.38`
- best ask: `$79,137.304`
- midpoint: `$79,131.842`
- displayed spread: `1.380480944699859... bps`
- account-volume assumption: Tier 1 (`$0` prior 30-day volume)

### Fee floors before spread, depth, latency, or adverse selection

| Route | Exact flat-price fee burden |
|---|---:|
| maker → maker | `29.9775 bps` |
| maker → taker | `39.9625 bps` |
| taker → taker | `49.9375 bps` |

These are multiplicative because the buy fee reduces the base inventory that can be sold, and the sell fee then reduces the credited quote proceeds. For example:

\[
1-(1-0.0015)^2=0.00299775=29.9775\text{ bps}.
\]

Therefore the earlier `0.14% target + 0.06% safety = 20 bps` threshold does **not** clear even the Tier-1 maker–maker fee floor. It cannot be an admissible NRRF833 round-trip threshold without a lower verified fee tier or a different execution relation.

### Immediate taker round-trip on the captured static book

This is a counterfactual audit, not an assertion that the book would remain unchanged during real execution.

| Quote cap | Gross entry notional | Entry VWAP | Exit VWAP | Flat round-trip loss | Loss |
|---:|---:|---:|---:|---:|---:|
| $20 | $19.9742555296 | $79,137.304 | $79,126.38 | $0.10248988729555 | `51.31099236398 bps` |
| $50 | $49.9831212064 | $79,137.304 | $79,126.38 | $0.25646835505495 | `51.31099236398 bps` |
| $100 | $99.9694028792 | $79,139.8059525… | $79,122.9750054… | $0.5203768865795 | `52.05361556559 bps` |
| $500 | $499.9731818564 | $79,159.7818012… | $79,099.2309881… | $2.877270207709625 | `57.54849084158 bps` |

The increasing loss at $100 and $500 is the depth relation: the order leaves the best level, raising the buy VWAP and lowering the sell VWAP.

Every audit row has a zero closure residual.

## 6. Deterministic learning validation

Configuration:

- 240 synthetic episodes;
- seed `833`;
- $20 quote cap;
- four regimes: calm, thin, adverse, recovery;
- exact official Tier-1 fees;
- deterministic displayed-depth and maker-queue traces.

The synthetic scenarios test the mechanism. They are **not evidence of expected live profitability**.

### Closure-aware policy

- decisions: 200 `HOLD`, 28 maker-with-taker-hedge, 12 taker–taker;
- receipts: 200 closed holds, 19 closed no-entry-fills, 21 closed returns;
- admitted learning observations: 40, including maker no-fill observations;
- completed-return wins/losses in this constructed dataset: 21 / 0;
- total synthetic realized P&L: `+$3.1434162847717986872615`;
- economically valued fees: `$1.8554522014790151577385`;
- maximum admitted closure residual: `0`;
- event and receipt chains: verified.

The uncertainty buffer rose from `6 bps` to approximately `98.20 bps`. This is not automatically desirable profit maximization; it shows the learner responding to model error and optimistic signals by refusing later marginal opportunities. The recovery regime produced no completed trades in this run, so the current update law may be too conservative after an adverse block. That is a visible calibration problem rather than a hidden success claim.

### Cost-blind comparison on the same constructed episodes

A naive rule that takes every positive raw signal as a taker–taker cycle produced:

- 177 completed cycles;
- 75 wins and 102 losses;
- total synthetic realized P&L: `-$2.6581158743908610997725`;
- mean modeled full cost: approximately `68.91 bps`.

Forcing taker–taker on all 240 episodes produced `-$16.52687503890563661768`.

The useful conclusion is not that the closure learner is proven profitable. It is that gross-signal admission and net-cost admission are materially different, and the simulator now exposes that difference through exact receipts.

## 7. Adversarial test coverage

The test suite contains 18 passing tests covering:

- fee-tier boundaries and next-day activation;
- exact multiplicative fee floors;
- credited-asset buy fees and quote-asset sell fees;
- depth walking, VWAP, and slippage;
- maker queue-ahead depletion and partial fills;
- post-only crossing rejection;
- stale fee-schedule rejection;
- crossed-book rejection;
- insufficient-depth rejection;
- hard quote exposure caps;
- fee-compatible quantity increments;
- cash, inventory, and cost-decomposition closure;
- refusal to learn from open inventory;
- refusal to learn from a tampered accounting residual;
- event-chain tamper detection;
- independently linked receipt-chain tamper detection;
- deterministic repeatability;
- hash-bound run-file verification.

## 8. Reproduction

From the repository root:

```bash
PYTHONPATH=. pytest -q tests/test_nrrf833_fee_pricing_closure_learning.py

python experiments/nrrf833_fee_pricing_closure_learning.py simulate \
  --episodes 240 \
  --seed 833 \
  --quote-budget 20 \
  --output runs/nrrf833_fee_pricing_closure_learning/validation

python experiments/nrrf833_fee_pricing_closure_learning.py verify \
  --run runs/nrrf833_fee_pricing_closure_learning/validation

python experiments/nrrf833_fee_pricing_closure_learning.py audit-live-snapshot \
  --fixture benchmarks/nrrf833_fee_pricing_closure_learning/alpaca_btcusd_orderbook_20260830T171345Z.json \
  --notionals 20,50,100,500 \
  --output runs/nrrf833_fee_pricing_closure_learning/live_snapshot_audit.json
```

## 9. Remaining empirical closure

The simulator closes the **model**. A live empirical claim requires additional authenticated relations:

1. the account’s actual effective 30-day volume tier;
2. submitted order acknowledgements;
3. partial-fill and cancellation receipts;
4. posted `CFEE`/`FEE` activities, which Alpaca may post at end of day;
5. actual inventory and cash deltas;
6. a replayable market-data interval spanning each order;
7. reconciliation of theoretical fees against posted fees before learning admits the episode.

Until those receipts are supplied, outputs remain deterministic counterfactual executions rather than settled profit.
