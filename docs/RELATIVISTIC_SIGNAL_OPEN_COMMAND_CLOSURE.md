# Relativistic signal integration and the command open to closure

The NRRF805 integration removes three supplied choices from the executable signal path:

- no `PLUS`/`MINUS` route labels are used;
- no fixed USD notionals are tested; and
- no price ratio is mapped into a hand-authored four-phase state.

For each identified public-book round, the validated books generate a directed asset graph. Every
rooted simple closed route is enumerated, including two-edge spread loops and both orientations of
the three-asset loop. Changing the starting asset is treated as a translation of one oriented route
class. The 12 rooted routes therefore form five relative route classes.

## Depth-derived natural partitions

Each directed order book is read as an exact piecewise-linear translation. Every observed depth
boundary is pulled backwards through the composed route, once with zero hair and once with the
declared fee translation. The route's natural partitions are those derived root boundaries. The
routine retains the maximizing equivalence class; it does not inject the old `$100`, `$1,000`, or
`$10,000` probes.

At each retained presentation:

```text
action potential return = zero-hair final / start - 1
global hair return      = (zero-hair final - cost-completed final) / start
completed return        = cost-completed final / start - 1

completed return = action potential return - global hair return
```

These readings are dimensionless. A common change of amount unit cancels. The Lean theorem
`Candidate.ofReturns_scale` proves that invariance, while `completedReturn_ofReturns` proves the
closure identity.

## Relative selection and open command

A route class signals only when its completed return is strictly positive and is the unique maximum
relative to every simultaneously derived class. Reciprocal closure additionally requires the
inverse route class to occur in the same field. `UniquePositiveLeader` and `SignalCloses` formalize
these conditions without an argmax choice.

The command has two independent fields:

1. public relational signal closure; and
2. authenticated presentation and execution authority.

`CommandStage.open_without_authority` proves the public command remains open. If authority later
arrives, `authorize_closes_iff` proves that it closes exactly when the relational signal had already
closed, and `authorize_candidates` proves authority cannot rewrite the public candidates. The
runtime has no order-submission operation.

## Locked result

The immutable replay covers 12 rounds. Eleven have identified three-book observations. They produce
143 maximizing depth presentations across the 12 rooted routes and five route classes per valid
round. All reciprocal topologies close and every numerical identity replays within the declared
decimal tolerance.

No candidate is positive. The best completed relation is the BTC→USD→BTC spread loop at
`-49.93876056045305905061517497` bps. All 12 commands remain `OPEN`; there are zero orders, zero
authenticated fills, and no settled P&L or profit claim.

This result does not say closure must lose. It says this public snapshot field contains no positive
closed relation after its declared fee hair. Observations, the fee translation, balances, venue
constraints, and private authority remain explicit interfaces rather than circularly derived facts.
