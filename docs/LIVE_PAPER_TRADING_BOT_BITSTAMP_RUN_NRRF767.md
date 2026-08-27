# NRRF767 — Bitstamp live public-book paper-bot run

## Result

The bounded live run returned **HOLD throughout**. It found no candidate above
zero or the additional 5 bp reserve after the declared 25 bp cost on each of
three legs.

| Returned layer | Exact result |
|---|---:|
| Public acquisition rounds | 12 |
| Identified public-book triangles | 11 |
| Open public-book triangles | 1 |
| Route/size evaluations returned | 72 |
| Complete-depth numeric evaluations | 66 |
| Paper signals | 0 |
| Orders submitted | 0 |
| Authenticated fills | 0 |
| Formal receipt admissions | 0 |
| No-order account delta | USD 0 |
| Authenticated settled P&L | undefined |

The best observed counterfactual was MINUS at USD 100:

```text
USD 100
→ ETH
→ BTC
→ USD 99.257632172355690925...

candidate delta  = −USD 0.742367827644309074...
candidate return = −74.236782764430907445... bp
decision         = HOLD
```

The worst observed counterfactual was PLUS at USD 10,000:

```text
candidate delta  = −USD 81.321071634589785484...
candidate return = −81.321071634589785484... bp
decision         = HOLD
```

These deltas are snapshot-model relations, not portfolio or settled P&L. The
six alternative route/size evaluations per round are not summed.

## Transaction equations

Every book price has unit quote asset per base asset, and every displayed
quantity has unit base asset. The two independent paths are:

```text
PLUS  : USD → BTC on BTC/USD asks
        BTC → ETH on ETH/BTC asks
        ETH → USD on ETH/USD bids

MINUS : USD → ETH on ETH/USD asks
        ETH → BTC on ETH/BTC bids
        BTC → USD on BTC/USD bids
```

For a buy, the depth walker accumulates

```text
base received = Σ(quote spent at level / ask price).
```

For a sale, it accumulates

```text
quote received = Σ(base sold at level × bid price).
```

The declared fee is then deducted from the received asset at each leg. A route
stops at its first depth deficiency. `PAPER_SIGNAL` requires all public-data
gates, complete depth on all three legs, and candidate return strictly greater
than the 5 bp safety reserve. All failures monotonically return witnessed
`HOLD`.

For top-of-book intuition only, before depth walking:

```text
R+ = bid(ETH/USD) / (ask(BTC/USD) × ask(ETH/BTC)) × (1 − f)^3
R− = bid(BTC/USD) × bid(ETH/BTC) / ask(ETH/USD) × (1 − f)^3
```

The implementation calculates both from their own bid/ask observations; it
does not define one as the reciprocal of the other.

## Exact acquisition and gates

The run used the Bitstamp public API order books for `btcusd`, `ethusd`, and
`ethbtc`, fetched in parallel with bodyless HTTPS GET requests. It ran from
2026-08-26 02:20:38.949698Z through 02:20:49.610513Z.

Configuration:

- notionals: USD 100, USD 1,000, USD 10,000;
- declared fee assumption: 25 bp per received leg;
- safety reserve: 5 bp;
- maximum book age: 5,000 ms;
- future-clock tolerance: 1,000 ms;
- maximum cross-book exchange-timestamp skew: 1,500 ms;
- maximum total acquisition span: 2,500 ms;
- maximum request-start skew: 250 ms.

One round was open because its 1,867.198 ms cross-book exchange timestamp skew
exceeded the 1,500 ms limit. Across all 12 rounds, skew ranged from 248.681 ms
to 1,867.198 ms (median 824.652 ms). Acquisition span ranged from 199.318 ms
to 976.406 ms (median 512.413 ms); request-start skew stayed between 0.136 ms
and 0.218 ms, and all three request windows overlapped.

For each identified round, every route and size had complete public depth but
was negative after declared costs. Medians in basis points, rounded to 10
decimal places, were:

| Orientation | USD 100 | USD 1,000 | USD 10,000 |
|---|---:|---:|---:|
| PLUS | −76.4138230641 | −76.4937647655 | −77.8465776093 |
| MINUS | −75.6053024946 | −75.6053024946 | −77.8886937063 |

## Replay and provenance

Run directory:

`runs/nrrf767_live_paper_trading_bot/bitstamp_public_20260826T0221Z`

All exact HTTP bodies are preserved by content hash. The 36 response
references reduced to 23 distinct raw blobs because identical responses are
deduplicated. The configuration-bound event chain was replayed from those raw
bytes and all gates, depth walks, decisions, and summary fields matched.

```text
configuration SHA-256 544070bca366ea0c0dbc0d48e4e085ab88cd7cf90a391760d0dffa3a00689b33
genesis hash          563c69a9bc0f5e4c312c2c73a2b6be703ec6094a9ea982f9465e34db5e26bcc6
final event hash      50755b3a49a0e40f33780792fd8c92456f298ca8b4d9eb689297e0d4e529a373
events SHA-256        0669ec688688a4810ee61b4f6b18b5dee720eaa0e1a6ac5f140cd51128e4ac81
summary SHA-256       eaa50d9faf5342f0ece04bd956fadf9a40e73dc2dc0ca1948130b66e14457026
program SHA-256       37ec7ab19010530fedeb41e6152cd936e73e667a292e6343b18e721ab8e9fd02
```

The chain is tamper-evident relative to its manifest and final head. A party
that rewrites the whole run and every commitment cannot be detected without
an external anchor.

Sources:

- Bitstamp public API documentation: <https://www.bitstamp.net/api/>
- Bitstamp fee-schedule reference: <https://www.bitstamp.net/fee-schedule/>

The 25 bp fee is a declared assumption, not an authenticated account tier.
Public REST books remain non-atomic. Account balances, actual
fee tier, trading status, venue precision, and minimum-order constraints were
not authenticated or modelled. For that reason even a future positive
`PAPER_SIGNAL` would remain non-executable and could not instantiate the
formal `ExactFillAdmission` or settled P&L.
