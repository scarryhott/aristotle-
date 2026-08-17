# Generative Axiom-Geometry Isolation — Executed Bounded Run

Status: **EXECUTED BOUNDED GENERATIVE PROXY**.

This run tests the causal order

```text
F_A, F_B, Q_A, Q_B
  < disclose
  < candidate (T,phi,pi)
  < GeomEquiv
  < W/E/J/C and operation naturality
  < question and held-out transfer.
```

It contains two deliberately separate evidence lanes. The reproducible reference lane uses
deterministic generator subprocesses. The raw assay preserves artifacts provided as separately
generated without rewriting them into the reference schema. The committed evidence proves their
bytes and assay order, not the provenance or non-observation of the upstream generation sessions.
Neither lane is an ASI or
Aristotle execution, and the subprocess boundary is not a security sandbox.

## Reproducible three-process lane

Generator A searches a local permutation construction and generator B searches a local affine
construction. Both receive the same order-six objective, but receive different private contexts,
labels, construction families, and curvature conventions. They emit their own operation tables,
occurrence carriers, admitted equality matrices, `W/E/J/C`, total questions, and solution
artifacts. Both processes exit before the disclosure manifest is created.

The verifier then exhaustively evaluates every basis bijection and both pole maps:

| Check | Result |
|---|---:|
| Basis bijections | 720 |
| Explicit `(T,phi,pi)` candidates | 1,440 |
| Ordinary operation-preserving `phi` maps | 6 |
| Fully natural closure translations | 6 |
| Naturality obstructions | 1,434 |

All six admitted forms preserve and reflect frame equality and pass return, extension, reversal,
curvature, multiplication, separately frozen local question-result, held-out word, and solution-set
transport. Their pole map is reversed because B's locally selected curvature representative is
its second pole while A's is its first. Thus `pi` is determined by commuting structure rather than
preselected as a common orientation.

The six forms are retained as an existential family. The runtime chooses no canonical translator,
claims no unique form, and issues no token.

## The three isolation readings

1. **Classical well-defined/free-choice isolation.** Both local group and frame replays pass. The
   strong classical post-disclosure baseline retains all six ordinary group isomorphisms, but
   local acceptance alone asserts no cross-frame identity.
2. **Translational-open isolation.** The literal-pole question is `OpenIn` each frozen frame only
   because a named equal pair has unequal question values. Resolved questions include quotient
   factors. Missing, rejected, partial, and obstructed comparisons emit no `OpenIn` label.
3. **Conditional natural-existential isolation.** Six explicit post-freeze witnesses exist for
   this pair. This is conditional evidence from the supplied frames and verifier contract, not an
   unconditional theorem that arbitrary axiom-geometries translate.

## Fresh raw generation assay

Two artifacts reported as separately generated under the same broader finite-frame objective were
provided to the runtime. Their bytes were frozen and hashed before the assay:

- A produced a locally valid eight-element D4 reference frame with sixteen occurrences.
- B produced a locally valid six-element S3 reference frame with twelve occurrences.

Both finite equality geometries pass the registered `ReferenceFrame` interface, but their
occurrence carrier cardinalities differ. The assay therefore returns
`CARDINALITY_GEOM_EQUIV_OBSTRUCTION` before candidate enumeration. It does not alter either frame,
claim global nonexistence, or call the obstruction `OpenIn`. A's locally supplied `E` indices do
not satisfy the narrower registered `TransFrame` interface, while B's do; naturality search is
therefore independently blocked as well.

An additional raw generator chose a valid C6 group but declared occurrences to be all finite words
over its tokens. That local group is verified in its own table, while its explicitly non-finite
word geometry remains outside this finite verifier. The result is
`TRANSLATOR_SEARCH_NOT_RUN_INTERFACE_BOUNDARY`, not false mathematics and not openness.

These raw assays are informative obstructions, but the repository bundle does not prove their
prompt/session provenance, non-observation, external administration, or cryptographic blinding.
They are not evidence of independent ASI capability.

## Adversarial controls

- equality collapse: preservation can pass while reflection fails;
- operation twist: `GeomEquiv` can pass while multiplication naturality fails;
- missing `pi` and mismatched `T/phi`: no complete translational form is admitted;
- partial proposal: remains `PENDING_COMPARISON`;
- artifact/question mutation: rejected by content hashes;
- D4 versus Q8: 80,640 two-pole equality-fibre forms are structurally available, but exhaustive
  operation checking finds zero natural translations and retains an explicit failed
  `(T,phi,pi)` form with its counterexample.

## Formal boundary

`GeomEquiv.independently_supplied_questions_agree_after_admission` proves that separately supplied
questions have matching `ResolvedIn` and `OpenIn` status after an admitted `GeomEquiv` and an
explicit pointwise correspondence are supplied. Those hypotheses intentionally preload the formal
success condition. Lean does not prove generation independence, freeze order, translator search,
or witness existence; those remain runtime evidence.

## Reproduction and receipts

```bash
python3 experiments/generative_axiom_geometry_isolation.py --assert-reference
python3 -m unittest tests.test_generative_axiom_geometry_isolation -v
```

- Result SHA-256: `d06902a14c55c06651f3c607f4ce22fc02e30da2349c5fd174cdf62f9431b8d3`
- Verifier SHA-256: `9b430e9f3035605b53f6272e60ea723d0471777c6f4d773a615be86d2299dd01`
- Receipt head: `b9637680304eb8421fcefb4502b8b610a3cf060404cf4ddb8dc6908dbab21512`
- Receipt count: 8
- Tokens issued: 0

Deterministic replay is byte-identical, and post-verifier hashing confirms that both frozen
generator artifacts and the disclosure manifest remain unchanged.
