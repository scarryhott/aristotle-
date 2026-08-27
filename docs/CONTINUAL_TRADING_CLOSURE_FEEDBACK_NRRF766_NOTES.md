# Continual trading closure and feedback — NRRF766 companion

## Continual does not mean all future stages are assumed

`NRRF766ContinualTradingClosureFeedback.lean` reads continual closure as a finite append-only
history. A history begins with one problem and one local witness. It grows only when the caller
supplies one next problem, one witness for that problem, and the boundary joining the current
target to the next source.

The module does not contain a function `Nat -> problem` paired with witnesses at every natural
number. It does not prove that every history can extend. `CanExtend history` is the proposition
that an `Extension history` has actually been supplied.

```text
local stage
  -> finite witnessed history
  -> supplied next problem + witness + boundary
  -> extended finite history
```

Continuation is therefore an authored interaction, not a future already present in the type.

## Local closure

`LocalTradeWitness P` requires closure only at `P`'s presented source. It carries an admissible
network interaction, a source-local return equation, and the actual NRRF627 frame equation. The
module derives source-to-target translation, return equality, quotient equality, and polar closure.

`ClosesAt P` says such a witness is available at this stage. `ofTradeProof` and
`closesAt_of_tradeProof` embed the stronger NRRF764 global proof. There is deliberately no converse:
local observation does not prove a law about every possible network reading.

## Status is stage-relative

`StageStatus Contradicts P` has four cases:

```text
witnessed       — carries `LocalTradeWitness P`
continuing      — carries no negative proposition
polarObstructed — carries failure of the polar relation
contradicted    — carries evidence of the caller's `Contradicts P`
```

The semantic contradiction predicate is explicitly about the actual problem. Polar obstruction is
not silently renamed truth contradiction. A legacy NRRF764 geometric contradiction embeds as
`polarObstructed`; legacy `open_uncontradicted` embeds as `continuing`, discarding the terminal
interpretation of global nonexistence.

## The append-only history

`ClosureStage` pairs one problem with its local witness. `ClosureHistory I current` is an inductive,
nonempty finite history indexed by its actual current stage:

- `start stage` creates the history from one witnessed stage;
- `snoc history next boundary` appends exactly one supplied stage.

`ClosureHistory.Extension history` packages only `next` and its boundary. The next stage already
contains its own local witness. `ClosureHistory.extend` applies this data; it does not invent it.

The proved preservation laws are:

- `extend_retains_prefix` — the old stage list is an exact prefix of the new list;
- `memory_eq_current_target` — executing the finite interactions reaches the current target;
- `memory_shared` — executed memory remains in the shared network field;
- `closureReturn_initial_eq_current_target` — local return equalities compose from the initial
  source to the current target;
- the three `extend_*` results specialize these facts to the supplied next stage.

There is no `no_terminal_stage` theorem. A history can have another stage only when `Extension` is
inhabited.

## Runtime and receipt boundary

`RuntimeBridge` (also named `ReceiptBridge`) is an explicit obligation for external values. The
caller must provide:

- the external `Receipt` type;
- a map from each receipt to a `TradingProblem`;
- the stage-local semantic contradiction predicate;
- the status assigned to each mapped receipt.

The mapped status may itself carry a witness, but `toContinualRealization` performs only the
supplied mapping. It neither selects that witness nor admits the receipt into history, and it proves
nothing about prices or closure.

An actual receipt enters a closure history only through `ReceiptAdmission`, which requires a
`LocalTradeWitness` for that receipt's mapped problem and equality showing the receipt's recorded
status carries that exact witness. A later receipt requires `ReceiptExtension`: the receipt, its
exact status-coherent witness, and its boundary with the current history. These obligations prevent
a CSV row, API response, signed message, or exchange fill from being treated as formal closure
merely because it was parsed.

`BoundaryMatches` is deliberately reading-level so differently represented records can compose.
The discipline that timestamps, provenance, venue identity, causal availability, and signatures
actually refer to the intended receipt remains an external `RuntimeBridge` obligation; closure does
not infer or erase those distinctions.

No theorem in this module claims that the current experimental CSV or any live feed instantiates
`RuntimeBridge`, `ReceiptAdmission`, or `ReceiptExtension`.

## P&L is retained one stage at a time

`ContinualAssessment` keeps gross outcome, costs, netting, and positivity explicit.

There is no global feedback rule quantified over all future observations. A
`FeedbackExtension history assessment observation` is one actual proposed extension. It carries:

- evidence that the observation is the current problem and that its status carries the current
  stage's exact witness after transport along that equality;
- the assessed net outcome and its equality to `net(gross, costs)`;
- one next observation;
- the next problem's local witness and equality showing its status carries that exact witness;
- the boundary joining the current problem to that next problem.

`CanFeedbackExtend` merely says this data is available. `failed_net_retained` proves that if the
current net fails positivity, the same failure remains attached to the supplied extension and the
old history remains a prefix. It neither renames loss as profit nor proves that a future extension
exists.

## Profit is an empirical bridge, not closure

`ClosureImpliesProfit assessment` names the optional empirical claim that every locally witnessed
observation is positive after costs. `local_failure_refutes_closure_implies_profit` proves that one
locally witnessed failed outcome refutes this bridge without undoing the closure history.

No theorem guarantees profit, prevents loss, supplies future market data, or authorizes live
orders.

## Properties map

| Requirement | Formal object or theorem |
|---|---|
| closure only at the presented stage | `LocalTradeWitness`, `ClosesAt` |
| strong legacy proof embeds locally | `ofTradeProof`, `closesAt_of_tradeProof` |
| reading-level composable boundary | `BoundaryMatches` |
| semantic contradiction belongs to the problem | `StageStatus Contradicts P` |
| polar obstruction remains geometric | `StageStatus.polarObstructed` |
| finite append-only closure | `ClosureStage`, `ClosureHistory` |
| one supplied continuation | `Extension`, `CanExtend`, `extend` |
| old history retained exactly | `extend_retains_prefix` |
| memory reaches current target | `memory_eq_current_target` |
| shared field preserved | `memory_shared`, `extend_memory_shared` |
| return preserved initial-to-current | `closureReturn_initial_eq_current_target` |
| external receipts require a mapping | `RuntimeBridge`, `ReceiptBridge` |
| each admitted receipt requires an exact status-coherent witness | `ReceiptAdmission`, `ReceiptExtension` |
| one assessed feedback extension | `FeedbackExtension`, `CanFeedbackExtend` |
| loss retained without assuming a future | `failed_net_retained` |
| positivity bridge remains refutable | `ClosureImpliesProfit`, `local_failure_refutes_closure_implies_profit` |

`nrrf766_answer` bundles the exact-prefix, executed-memory, sharedness, and return-preservation laws
for one supplied extension.
