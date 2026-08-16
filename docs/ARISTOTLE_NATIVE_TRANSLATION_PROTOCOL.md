# Aristotle native-translation frontier protocol

This is the repository's primary frontier protocol. Its scientific causal order
is frozen independently of the current Aristotle SDK implementation.

```text
neutral objective O_i
  → independently generated F_A and F_B
  → frozen native translation T_AB
  → identity-independent translation validation and recovery
  → candidate relational equality
  → independent return generation
  → translational completion, IVI, topology, receipts, transfer
```

## Non-negotiable requirements

1. `F_A` and `F_B` are generated in isolated sessions from the same neutral
   packet. Neither generator sees the other frame, an intended correspondence,
   a closure class, or target reverse edges.
2. `T_AB` is a separately frozen native translation with local evidence and
   explicit `UNMAPPED`/`AMBIGUOUS` entries. The translator cannot receive an
   identity/equivalence relation, quotient, closure verdict, reverse-edge
   target, or evaluation score.
3. Translation validation precedes candidate equality. It checks preservation
   of independently declared primitive relations/operations and held-out local
   consequences; recovery is evaluated only against the admitted translation
   interface.
4. Candidate equality is a result, not an axiom. Its acceptance or rejection
   cannot trigger source-frame or translation repair.
5. Return generation is independent. It receives only the frozen admitted
   forward interface, never target reverse edges, equality outcome, or metric.
6. Report `LocalIVI_A`, `LocalIVI_B`, and `CrossFrameIVI_AB` separately.
   Cross-frame IVI requires a returned relational identification valid through
   the frozen translation and its validation; it is not inferred from local
   IVI alone.

## Preregistered abstention rule

Emit `UNMAPPED` if no type-compatible correspondence has enough declared local
evidence to preserve every primitive relation/operation in scope. Emit
`AMBIGUOUS` if multiple correspondences remain after the same fixed evidence
tests. Do not use identity, closure, recovery, or aggregate scores to break a
tie. Retain these outcomes in coverage and final reporting.

## Executed initial stage

Two Aristotle formalization jobs completed from the identical neutral packet.
They are evidence for Phase A only: each produces a single finite labelled
frame with independently supplied topology and forward reachability. The
artefacts deliberately contain no cross-frame translation, equality, closure,
or return claim. Their identifiers and content hashes are committed in
[`../runs/aristotle_native_translation/initial_isolated_generation/manifest.json`](../runs/aristotle_native_translation/initial_isolated_generation/manifest.json).

The current implementation profile is Harmonic's `aristotlelib` SDK. Record
SDK version, project/task identifiers, request hash, result hash, and emitted
model metadata in every future manifest. A later SDK change cannot relax any
scientific requirement above.
