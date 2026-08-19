# Aristotle Phase C2: assembled completion / recoverability

Run **only** Phase C2 over the frozen Phase-B2 admitted interface and frozen
Phase-C1 local-return receipts. This is an assembly/recoverability test, not a
translation rewrite, equality search, or downstream IVI/topology/transfer run.

## Frozen input boundary

Retain without change:

- exactly the 34 roles admitted by Phase B2/B3;
- the `frame-structure` `FAIL`, which blocks whole-frame equality and
  `GeomEquiv` promotion;
- `main-preamble` as `OUTSIDE_INTERFACE`;
- all 10 `AMBIGUOUS` and 20 `UNMAPPED` entries;
- C1's 20 determined returns, five unique data returns, one round-trip return,
  eight bare-identity/non-single-valued receipts, and every global abstention.

Do not supply or infer a target reverse edge, candidate equality outcome,
CrossFrameIVI target, topology, receipt, question-transfer, held-out transfer,
or performance score.

## Required evaluation

Evaluate whether C1's local return receipts **assemble** into recoverability or
completion over the admitted 34-role interface. Preserve local versus global
scope: a local return does not become an assembled cross-frame return unless
the registered interface witnesses the assembly.

For each proposed assembly, report:

1. the exact admitted roles used;
2. forward translation and C1 return lineage;
3. preservation/recovery/reflective property actually established;
4. all non-single-valued or missing components;
5. any explicit obstruction witness.

## Only permitted terminal classifications

- `ASSEMBLED_COMPLETION` — only if the admitted interface supports an explicit
  cross-frame recoverability/completion witness;
- `ASSEMBLY_OBSTRUCTION` — with explicit witness and affected roles;
- `OPEN_INTERFACE_BOUNDARY` — evidence insufficient or components outside the
  registered interface;
- `INVALID_LEAKAGE_OR_PROTOCOL_VIOLATION` — if forbidden downstream targets or
  repair/promotion are used.

None of these classifications permits a whole-frame `GeomEquiv`, CrossFrameIVI,
topology naturality, receipt, question transport, held-out transfer, successor
frame, or successor verifier claim. Those are later phases.

## Provenance deliverables

Produce a machine-readable C2 manifest and a human-readable report. Record
input archive hashes, request/task IDs, SDK/model metadata, result hash,
classification, role coverage, abstentions, and explicit scope boundary.
