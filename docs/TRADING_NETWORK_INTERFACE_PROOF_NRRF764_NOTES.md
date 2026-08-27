# Trading network–interface–proof closure — NRRF764 companion

## Verified scope

`NRRF764TradingNetworkInterfaceProof.lean` implements the chain

```text
Network -> Interface -> Trading problem -> Proof -> Continued memory.
```

It imports both the NRRF764 super-network and the repository's established
NRRF627 translational frame. It is registered in `lakefile.toml`. The full
project and both NRRF764 modules build with warnings treated as errors.
`#print axioms NRRF764.nrrf764_trading_answer` reports
`[propext, Quot.sound]`; there is no declared `axiom` or `sorry` in either new
Lean source.

This is a formal integration, not a moving-average cycle, a price predictor,
or a performance result.

## One coherent interface

For a network `N` and polar carrier `R`, `TradingInterface N R` supplies:

```text
Quote
site          : Quote -> N.Site
perspective   : Quote -> Bool
orientation   : Quote -> NRRF627.Pole
radius        : Quote -> R
closureReturn : N.Reading -> ZeroInfClosure R
```

The quote's polar geometry is derived from `orientation` and `radius`; it is
not a free second label. `quote_coherent` requires the network reading and
that derived geometry to have exactly the same quotient return:

```text
closureReturn (N.read (site q))
  = quotient (polarPresentation (orientation q) (radius q)).
```

That law is the interface. A pricing realization may choose what a reading,
radius, site, and quote mean, but it must prove this equation rather than
asserting after the fact that two unrelated representations close.

## What closes a proposed trade

A `TradingProblem` is an oriented source/target quote pair. A `TradeProof`
contains an admissible NRRF764 `Interaction` and two laws:

1. `closure_natural`: the interaction preserves the interface's closure
   return for every network reading;
2. `frame_closes`: the interaction-translated source occurrence, routed by
   the actual NRRF627 `flipFrame.T`, is the target occurrence.

The second law uses the source and target perspectives and orientations. Its
first projection derives the network translation equation (`translates`). The
NRRF627 theorem `trade_translation_is_nrrf627_closure` then evaluates the
translated occurrence with the frame's real verification return `W`. It is
not the degenerate specialization `CEq id`.

Network translation, quotient equality, and polar closure therefore form one
derivation:

```text
frame_closes
  -> translated source reading = target reading
  -> closure_natural + quote_coherent
  -> equal ZeroInfClosure images
  -> PolarRel source geometry target geometry.
```

`geometry_quotient_iff` also proves the converse: quotient equality is exactly
`PolarRel`, not merely implied by it.

## Closed, OPEN, and CONTRADICTED

`IsClosed P` means that `TradeProof P` is inhabited. `IsOpen P` is stronger
than not having found a proof: it means `not IsClosed P` has itself been
proved. `IsContradicted P` means the derived reciprocal polar relation fails.
Because every trade proof derives that relation, `contradicted_is_open` proves
every contradicted proposal is open.

The formal result does not say that every quote pair closes. A supplied proof
is what distinguishes a closed proposal from an open one.

## Continued observations

`TradingRealization` does not accept a free-floating signal. Every observation
supplies one `TradingProblem` and a `TradeDecision` about that same problem:

```text
closed                 : carries TradeProof
contradicted           : carries IsContradicted
open_uncontradicted    : carries IsOpen and not IsContradicted.
```

These reported buckets are disjoint: a contradicted proposal cannot be placed
in `open_uncontradicted`. An observation for which none of these facts has
been established is unresolved and is not silently admitted to the classified
realization.

Only a closed decision contributes its proved interaction to
`realizedInteractions`. `realizedMemory_shared` proves that any resulting
memory remains in the shared field, and `realizedConnection_append` proves
that adjoining histories composes their connection records. This alone is
admissible memory, not yet a continuous closed route.

`RealizedHistoryComposable` adds the missing path law: the initial reading
must equal the first proved source, and every proved target must equal the next
proved source. Under exactly that hypothesis,
`realizedMemory_eq_finalTarget` proves that execution reaches the last proved
target. Thus continued closure is proved for composable histories and is not
assumed for arbitrary lists.

The concrete `polesClosedTrade` and `polar_trade_nonvacuous` show that the
Network–Interface–NRRF627–Proof chain is inhabited for the two-pole model.
That witness is a formal reciprocal example, not historical market evidence.

## Profit and costs remain falsifiable

`EmpiricalAssessment` is attached to one `TradingRealization`. It must supply:

```text
Outcome
gross    : Observation -> Outcome
costs    : Observation -> Outcome
netOf    : Outcome -> Outcome -> Outcome
positive : Outcome -> Prop.
```

The formal layer does not choose arithmetic, currency, return convention, or
cost model. `ValidatedPositiveBridge` is the explicit claim that every
formally closed observed problem is positive after that supplied net
assessment. `observed_failure_refutes_validated_bridge` proves that one closed
observation failing the positivity test refutes this bridge while leaving the
closure theorems intact.

This is the correct role of failure in the architecture: it can invalidate a
pricing realization or positive-return bridge. It cannot be relabelled away by
calling the trade closed.

## Requirements for an actual market test

The repository module deliberately does not fabricate live data. A real
realization must still freeze and report:

- timestamped executable observations and exact venue/source provenance;
- causal quote availability and chronological train/calibration/test splits;
- entry, exit, orientation, sizing, and exposure rules;
- spread, fees, slippage, latency, funding, and borrow assumptions;
- gross and net results for both reciprocal orientations;
- separate counts and forward outcomes for closed, OPEN, and CONTRADICTED
  observations;
- missing intervals, exclusions, turnover, and drawdown.

For an oriented numerical implementation, a conventional measurement may use

```text
net_return_t = orientation_t * gross_price_return_t - total_cost_t,
```

but that equation belongs to the empirical assessment, not to the closure
foundation. No theorem in this module guarantees profit or authorizes live
orders.

## Properties map

| Requirement | Formal object or result |
|---|---|
| network reading is real/shared | `sourceProblem`, `targetProblem`, `trade_*_shared` |
| geometry agrees with network return | `quote_coherent` |
| interaction preserves closure | `TradeProof.closure_natural` |
| existing frame translation participates | `TradeProof.frame_closes` |
| existing NRRF627 return participates | `trade_translation_is_nrrf627_closure` |
| quotient equality is derived | `TradeProof.geometry_quotient_eq` |
| polar relation is derived | `TradeProof.geometry_closes` |
| OPEN/CONTRADICTED are disjointly reported | `TradeDecision`, `contradicted_is_open` |
| arbitrary histories remain admissible | `realizedMemory_shared` |
| composable histories reach the final target | `realizedMemory_eq_finalTarget` |
| costs and positivity are explicit | `EmpiricalAssessment` |
| a loss refutes the positive bridge | `observed_failure_refutes_validated_bridge` |

`nrrf764_trading_answer` bundles the shared endpoints, translated memory,
NRRF627 closure equality, quotient equality, and polar relation. Ambient
`unity_terminal` remains a theorem of every NRRF764 network; this adapter does
not misstate it as a consequence of one successful trade.
