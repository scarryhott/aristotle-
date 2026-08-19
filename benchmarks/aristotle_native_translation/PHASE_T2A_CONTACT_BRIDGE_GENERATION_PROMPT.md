# Aristotle Phase T2A: blind contact-bridge generation

Generate a candidate **ContactBridge** for the frozen Aristotle frames. This
is a bridge-generation task only. It runs without access to the T1 truth
question table or its terminal result, and it does not evaluate truth
completion, equality, IVI, topology, transfer, or succession.

## Exclusive input packet

Use only the frozen B2 and C1 archives:

- B2: `c3c05eae85fa0357501f177cbbcebbe103a9f29c90926d9ee9b5e08ac4dd5da8`;
- C1: `0cd2d7b56e38d99f3aa9b20af0c87b752e4985dabec22bed9d85d2e98670f56e`.

Do not use B3, C2, T1, NRRF661–668, whole-frame equality, `GeomEquiv`, IVI,
topology, receipts, transport, transfer, successor targets, scores, unlisted
project context, or a desired truth verdict. Retain all B2 exclusions and C1
local-return limitations unchanged.

## Required object

Attempt exactly one finite object:

```text
ContactBridge = (Qcap, embA, embB, rhoCap, GammaCap, DeltaCap)
```

- `Qcap`: minimal shared answer carrier/question interface derived only from
  frozen declaration signatures and B2/C1 provenance, never matching answers;
- `embA`, `embB`: explicitly stated maps from local question/answer shapes to
  `Qcap`;
- `rhoCap`: a non-local return/challenge over `Qcap`, not paired local receipts;
- `GammaCap`: pre-verdict provenance independent of the bridge conclusion;
- `DeltaCap`: all excluded roles, non-single-valued returns, and asymmetries.

Matching names, `YES` markers, role counts, or a postulated common carrier do
not constitute a bridge. A comparison must state how both carrier-dependent
propositions become propositions over the same `Qcap`.

## Independence controls

`ContactBridge/BridgeGeneration.lean` and its manifest must be written before
any answer-agreement evaluation. The module must not import or mention
`TruthAssembly`, C2, B3, `truthAgreement`, a target verdict, IVI, or
downstream targets. It must read B2/C1 provenance directly.

## Terminal classifications

- `BRIDGE_GENERATED`: only with explicit `Qcap`, both embeddings, non-local
  `rhoCap`, independent `GammaCap`, retained `DeltaCap`, and compatibility
  witnesses. This does not assert truth completion.
- `BRIDGE_OBSTRUCTION`: only with an explicit B2/C1 witness contradicting a
  required bridge condition.
- `OPEN_BRIDGE_BOUNDARY`: the frozen B2/C1 evidence cannot generate an
  admissible shared carrier, embedding, non-local return, or confirmation
  without postulate or retrospective choice.
- `INVALID_LEAKAGE_OR_SELF_CERTIFICATION`: prohibited input, target, repair,
  self-issued confirmation, or postulated comparison.

## Deliverables

Produce `ContactBridgeGeneration.md`,
`ContactBridge/BridgeGeneration.lean`, `ContactBridge/t2a-manifest.json`, and
frozen-integrity, scope, witness-name, and result-hash scripts. No later
evaluator may be run here; a separate T2B can assess a generated bridge
against T1 only after this result is frozen.
