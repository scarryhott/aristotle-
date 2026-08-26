# NRRF768 — Bitstamp natural-form selector replay

This run applies the NRRF768 selector architecture to the immutable NRRF767
Bitstamp public-book evidence. It is an overlay: it does not edit or recapture
the bytes of the source run, and it does not submit an order.

## Source provenance

- Venue: Bitstamp public REST order books.
- Markets: BTC/USD, ETH/USD, and ETH/BTC.
- Endpoints: the exact public URLs recorded in the NRRF767 manifest.
- Capture interval: `2026-08-26T02:20:38.949698Z` through
  `2026-08-26T02:20:49.610513Z`.
- Source rounds: 12; 11 identified public triangles and 1 `OPEN` triangle.
- Declared costs: 25 bp per leg and a 5 bp safety reserve.
- Declared USD radii: 100, 1,000, and 10,000.
- Source configuration SHA-256:
  `544070bca366ea0c0dbc0d48e4e085ab88cd7cf90a391760d0dffa3a00689b33`.
- Source events SHA-256:
  `0669ec688688a4810ee61b4f6b18b5dee720eaa0e1a6ac5f140cd51128e4ac81`.
- Source final event:
  `50755b3a49a0e40f33780792fd8c92456f298ca8b4d9eb689297e0d4e529a373`.
- Pinned NRRF767 program:
  `37ec7ab19010530fedeb41e6152cd936e73e667a292e6343b18e721ab8e9fd02`.

The overlay verifier first replays NRRF767 from its raw content-addressed
responses and verifies all of those bindings.

## Runtime realization

The finite presentation is

```text
p = (orientation, start_usd)
orientation ∈ {PLUS, MINUS}.
```

For this explicit runtime bridge only, the return is declared to be the
starting radius:

```text
q(orientation, radius) = radius.
```

Therefore `PLUS` and `MINUS` at the same radius are the two declared polar
presentations of one finite identity fibre. USD 100 and USD 1,000 are not the
same fibre. This is a replayable realization map, not a theorem that capital,
market value, or economic profit is intrinsically identical to `start_usd`.

A natural form chooses exactly one orientation at every declared radius. The
committed trajectory uses one contextual rule:

```text
initial form: author PLUS at every radius

next form:
  preceding OPEN assessment       → retain the form
  preceding numeric HOLD          → polar reversal
  any other preceding assessment  → retain the form.
```

The next section is computed from the configuration and preceding overlay
event before the current source event is inspected by the selector. Current
return data therefore audits the already chosen form; it cannot choose itself.
No current or future `candidate_return_bps`, cross-radius comparison, or
`argmax` enters selection.

## Exact result

| Result | Count |
|---|---:|
| Natural-form sections | 12 |
| Selected form assessments | 36 |
| Numeric selected assessments | 33 |
| `OPEN` selected assessments | 3 |
| Negative numeric assessments | 33 |
| Positive numeric assessments | 0 |
| `PAPER_SIGNAL` assessments | 0 |
| Initial authored witnesses | 3 |
| Polar reversals | 30 |
| Identity translations after `OPEN` | 3 |
| PLUS / MINUS selected occurrences | 21 / 15 |
| Action or profit selections | 0 |
| Orders / authenticated fills / formal admissions | 0 / 0 / 0 |

Every numeric selected result was negative after the declared costs. The exact
selected ranges were:

| Radius | Numeric / OPEN | Best selected return (bp) | Worst selected return (bp) |
|---:|---:|---:|---:|
| USD 100 | 11 / 1 | `-74.236782764430907445819961815005890238453101515213064142665637567534630539871` | `-77.4057587576367316218552718589068751913084497773669063662558987521463385495592` |
| USD 1,000 | 11 / 1 | `-74.5796515079032751328817006084991876523151909017059301380991064175467099918765` | `-77.4057587576367316218552718589068751913084497773669063662558987521463385495592` |
| USD 10,000 | 11 / 1 | `-75.6953516184969097365654419509529922168240092293193376988447102026225565864514` | `-81.3210716345897854849919621241267246076056242088958622338653878296555759793897` |

These are public-book counterfactual route assessments, not realized P&L.
The no-order account delta remains exactly USD 0 and authenticated settled P&L
remains undefined.

## What changed and what did not

The selector now moves: negative assessments feed 30 witnessed polar reversals,
and the `OPEN` round feeds three identity translations. This fixes the earlier
architectural failure in which zero `PAPER_SIGNAL` rows meant there was no form
trajectory at all.

Profit did not become positive. That is not a failure of the new selector
equations. The selector preserves the declared identity `start_usd`; empirical
route return is a separate function

```text
V_t(orientation, radius) = candidate_return_bps.
```

The observed `V_t` differs between reciprocal presentations and is negative on
every selected numeric case. It therefore does not factor through the declared
return `q` and cannot be inferred from natural-form closure. A profitable
claim still needs later market data that passes the empirical bridge.

## Overlay hashes

- Selector configuration:
  `0507137e0b485ae69d535e40cd1b1ce4b98b004d43ec94c5df564210ef811d27`.
- Genesis:
  `d95cd6271b2f2549d203eee1e2a8716444a8aaaf83f62c7e4887af32fa4fb6b4`.
- Events:
  `7108fc22474b4549f217f42e58f4e8fd82426d782da94163723079458398e030`.
- Final event:
  `e2fa6ac0966142267873688682fd355c0b83c3dbacb9e2454f526a6019aad549`.
- Summary:
  `18e320f2481c97180309058ccc94bd1dd4fb1b6c7d8229bdd7325cba3c462be7`.
- Manifest:
  `73ca852b37bfd863de58b6f132d030a36263265c4721dbeed2bd954e05be52b6`.
- Overlay program:
  `311bbc55e9bdd0c889fef362a72abecbc047659fa724aad03616097997554511`.

The committed artifact is
`runs/nrrf768_relative_natural_form_selector/bitstamp_public_20260826T0221Z`.
