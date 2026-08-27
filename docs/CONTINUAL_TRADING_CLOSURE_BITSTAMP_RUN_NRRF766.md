# NRRF766 continual trading Closure — Bitstamp hourly run

## Result and boundary

This is a **same-bar observational relation audit**, not a forward-return or
trading-performance test. `experiments/nrrf766_continual_closure_trading.py`
returns one hash-chained runtime stage receipt for every declared hour. Missing,
inactive, invalid, and provisional observations remain as witnessed stages;
no rate is imputed and no stage is silently discarded.

The ledger is hash-chained and tamper-evident relative to its committed head.
That is not external immutability: someone can reauthor the manifest and the
entire chain. Runtime continuity is also not an instantiation or Lean proof of
`NRRF766.BoundaryMatches` or `NRRF766.LocalTradeWitness`. A verified
`NRRF766.ReceiptBridge` remains required before runtime rows inhabit that
formal boundary.

Aggregated OHLCV fails the executable-receipt gate. Every current-stage paper
action therefore returns no-order `HOLD`, defined ratio `1`, and defined paper
P&L `0`. This zero is not measured strategy performance. `HOLD` is an
identity/no-order runtime return, not a formal `NRRF764.Interaction` and not
process halting. With no authenticated fills, settled P&L remains undefined
rather than zero.

## Same-bar equations

For hourly close relations

```text
B = BTC/USD
E = ETH/USD
X = ETH/BTC
```

the runner computes both paths directly from the three observations:

```text
PLUS  : USD -> BTC -> ETH -> USD,  gross_plus  = E/(B*X)
MINUS : USD -> ETH -> BTC -> USD,  gross_minus = (B*X)/E
```

Their product check,

```text
gross_plus * gross_minus = 1,
```

is reciprocal-equation consistency over the same inputs, not independent
evidence from another market observation.

With declared per-leg cost `25 bp`, `f = 1 - 25/10000 = 0.9975`:

```text
net_plus  = gross_plus  * f^3
net_minus = gross_minus * f^3
net_plus * net_minus = f^6 = 0.985093438085351806640625
```

A candidate clears the separately declared safety reserve only when its net
ratio exceeds `1 + 5 bp = 1.0005`. Passing that numerical threshold cannot
make an OHLCV candle executable.

## Provenance

The files contain the provider banner `https://www.CryptoDataDownload.com`
and are labeled as Bitstamp markets.

| Relation | Rows | SHA-256 |
|---|---:|---|
| BTC/USD | 72,343 | `12d159598194aab1307909e29d92a1c5e3cbc41af4d567563dad559d2397fcbb` |
| ETH/USD | 72,363 | `ef35440148bee7fd1dcb3b436e4c56d8d3ca4672d65d9f9293e168d9c05d1f53` |
| ETH/BTC | 72,363 | `ae33e5751ca4243d59bf3d04373f6f3e36b8cc3a44ff055f0f6bfbe0dd5aeea3` |

The BTC/USD snapshot has a separately preserved download record of
`2026-08-24T10:41:41.981008Z`. No exact download timestamp was available for
the two ETH files, so none is invented. File hashes, provider banners, source
URLs, schemas, timestamp/date agreement, symbols, OHLC ordering, duplicates,
and gaps are recorded in the manifest.

The replay declares a bar labeled `t` available at `t+1 hour`. Static CSV has
no historical publication receipts, so this is a replay convention, not a
verified availability timestamp.

## Locked interval and stage counts

The locked ledger begins `2024-02-23T05:00:00Z` and ends with the conservatively
pending provider-tail row at `2026-08-24T00:00:00Z`. The preceding replay row
is `2026-08-23T23:00:00Z`.

| Stage state | Count |
|---|---:|
| `IDENTIFIED_ACTIVE` | 21,439 |
| `INACTIVE` | 264 |
| `OPEN_MISSING` | 204 |
| `PENDING_UNFINALIZED` | 1 |
| **All returned stages** | **21,908** |

## Full candidate distribution

The distribution makes the negative result visible; it does not report only
the rare positive tails.

| Orientation | Defined | Net negative | Net zero | Net positive | Clears 5 bp safety | Minimum net bp | Median net bp | Maximum net bp |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| PLUS | 21,439 | 21,437 | 0 | 2 | 2 | `-244.8502879369955524685814013239632842527451708152991170648668408040852747051009` | `-74.7662984983549237806411815596644853149697256806259783602983397826047775610454` | `38.695154113099035429979607011577744314202101437648788585551927031320948010384` |
| MINUS | 21,439 | 21,433 | 0 | 6 | 5 | `-187.0370305872380097267163073564383454836068769248762231491949631593310202331293` | `-74.8590137851221003158870179139169478248849341859381639643052789482037445666921` | `98.188824997804385933915045168064575566588504923180215403332264814342721997441` |

Every positive net candidate is listed below using the exact serialized replay
value. The 0.054 bp MINUS row is net-positive after the 25 bp-per-leg cost but
does not clear the additional 5 bp safety reserve.

| Orientation | Stage UTC | Net candidate ratio | Net candidate P&L (bp) | Clears safety |
|---|---|---|---|:---:|
| MINUS | `2025-02-02T18:00:00Z` | `1.0008758975195983078830982548410231890987329667702605785321539564905570164953382` | `8.758975195983078830982548410231890987329667702605785321539564905570164953382` | yes |
| MINUS | `2025-02-03T01:00:00Z` | `1.0042896526488395599927719551861221539573545355981207083483917600289121792555114` | `42.896526488395599927719551861221539573545355981207083483917600289121792555114` | yes |
| MINUS | `2025-03-10T11:00:00Z` | `1.0000054114920050585864046634072959759308010530274539300488905603610379842045882` | `0.054114920050585864046634072959759308010530274539300488905603610379842045882` | no |
| PLUS | `2025-08-19T00:00:00Z` | `1.0011900391697416584717431212625998301166974400906692391188913550754092968788044` | `11.900391697416584717431212625998301166974400906692391188913550754092968788044` | yes |
| MINUS | `2025-09-17T17:00:00Z` | `1.0078388309774357487222497410726347548070428243346692484351780969964425631557617` | `78.388309774357487222497410726347548070428243346692484351780969964425631557617` | yes |
| MINUS | `2025-10-10T21:00:00Z` | `1.0098188824997804385933915045168064575566588504923180215403332264814342721997441` | `98.188824997804385933915045168064575566588504923180215403332264814342721997441` | yes |
| MINUS | `2025-11-16T11:00:00Z` | `1.0010163701868692552556535579282445785529544399495987797599310299091451687777704` | `10.163701868692552556535579282445785529544399495987797599310299091451687777704` | yes |
| PLUS | `2025-11-16T17:00:00Z` | `1.0038695154113099035429979607011577744314202101437648788585551927031320948010384` | `38.695154113099035429979607011577744314202101437648788585551927031320948010384` | yes |

These are numerical same-bar candidates only. All 43,816 orientation returns
(two per stage) close to paper `HOLD`; aggregate defined paper-closed P&L is
`0`. Authenticated settled orientations: `0`; authenticated settled P&L:
undefined.

All 21,439 active rows pass reciprocal-equation consistency and cost-product
checks. All 21,908 stages pass hourly continuity, source-to-target adjacency,
declared-bar-lag-or-pending, and event hash-chain verification.

## Durable run artifacts

The locked output is in
`runs/nrrf766_continual_closure_trading/bitstamp_hourly_oos/`:

| File | SHA-256 |
|---|---|
| `manifest.json` | `3f46fbbe60aa119bdb2528367d3ee035e396b8546b6ce2679a234ea64cac1ebc` |
| `stage_ledger.csv` | `c039a66d3a2e8bb54755bc150bbf6f1e0b4c3a45ecc0acc66b670be8f0d3bce1` |
| `summary.json` | `d720b9f44cb57b047298e162ae67968433b1ad3867533df450690be35c853f1f` |

## Limits

- This run measures no forward return and makes no profitability estimate.
- Hourly candles are aggregated, not synchronized executable bid/ask quotes.
- They contain no depth, verified publication time, latency, account fee tier,
  balances, atomicity, or authenticated fills.
- A positive candidate is neither an order nor profit.
- Paper HOLD does not erase a negative candidate, manufacture settled P&L, or
  halt the continuing process.
- The runtime chain can detect alteration relative to its recorded head, but a
  fully reauthored chain needs an external commitment to be detected.
- A formal `ReceiptBridge` is still required; the runtime chain alone proves no
  Lean boundary witness.
