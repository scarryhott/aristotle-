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

## Executed stages

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

Phase B also completed in a third isolated Aristotle project against the two
frozen archives. `T_AB v0.1.0` records 66 declaration-role entries: 36
`MAPPED`, 10 `AMBIGUOUS`, and 20 `UNMAPPED`. Its local Lean evidence and
machine-checked table hygiene do not introduce a cross-frame map, equality,
completion, return, IVI, or topology claim. A material interface boundary was
preserved: both frames declare the same fully qualified `NeutralFrame` names,
so they cannot be co-imported without changing a frozen source. Phase B
provenance is committed in
[`../runs/aristotle_native_translation/phase_b_native_translation/manifest.json`](../runs/aristotle_native_translation/phase_b_native_translation/manifest.json).

Phase B2 validation completed in a fourth isolated project. It preserves the
frozen table and reports 34 `PASS`, one `FAIL` (`frame-structure`), and one
`OUTSIDE_INTERFACE` (`main-preamble`) verdict across the 36 mapped entries.
The failure is an identity-independent signature obstruction: A requires a
nonempty node type while B admits an empty one, and B requires finite labels
and observables while A admits infinite ones. The validator leaves all 10
ambiguous and 20 unmapped entries unchanged and makes no equality or return
claim. Its provenance is in
[`../runs/aristotle_native_translation/phase_b2_validation/manifest.json`](../runs/aristotle_native_translation/phase_b2_validation/manifest.json).

Phase B3 completed in a fifth isolated project. It accepts a candidate
relational equality only at the declaration-role level of a neutral 34-role
subinterface, with a realization in each frame's own module. Machine-checked
non-promotion witnesses show that this scope admits a B-legal empty-node frame
and an A-legal infinite-label/observable frame, so it cannot be promoted to
whole-frame equality or `GeomEquiv`. The frozen structural failure, ambiguity,
and unmapped records remain excluded and unchanged. Provenance is in
[`../runs/aristotle_native_translation/phase_b3_candidate_equality/manifest.json`](../runs/aristotle_native_translation/phase_b3_candidate_equality/manifest.json).
