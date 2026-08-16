# Experimental Program

## Submission status

This repository contains a **self-contained executed verification programme**, not only a proposal.

The completed bounded evidence establishes a reproducible progression:

```text
local axiom-geometries
  → internal equality audit
  → immutable freeze
  → post-freeze candidate (T,phi,pi)
  → GeomEquiv preservation + reflection
  → W/E/J/C and operation naturality
  → quotient ResolvedIn / explicit OpenIn witness
  → held-out transfer / next basis
```

The primary next experiment is now singular: **run the already-frozen translational protocol on independently generated Aristotle mathematical frames**. The secondary research directions listed at the end are not prerequisites for that experiment.

## Completed verification suite

### E0.5 — Independent full-stack classical mathematical agents

Status: **EXECUTED**.

Two separate subprocesses learn and execute different D4 presentations. Their artifacts freeze before a third process searches for cross-frame translations. The verifier checks frame equality, `GeomEquiv`, `W/E/J/C`, operation naturality, frame-qualified resolution/openness, and next-basis transfer.

The runtime retains all coherent translations, including orientation reversal, rather than selecting one canonical coordinate identification. Non-natural deformation and self-certification controls preserve explicit negative boundaries.

See [`FULL_STACK_RUN.md`](FULL_STACK_RUN.md) and [`../benchmarks/full_stack_d4/RUNBOOK.md`](../benchmarks/full_stack_d4/RUNBOOK.md).

### E0.75 — Strong classical baseline versus translational verification

Status: **EXECUTED BOUNDED COMPARISON**.

Both verifier arms receive the same content-addressed frozen artifacts. The classical arm performs local kernel checks and a strong ordinary isomorphism analysis; the translational arm additionally records preservation/reflection of each frame's own equality, quotient factors, naturality, explicit `OpenIn` witnesses, lineage, and held-out transfer.

The controls separate distinct failure levels:

- `equality_collapse` can preserve equality forward while failing reflection;
- `operation_twist` can pass `GeomEquiv` while failing downstream operation naturality;
- pending or unselected comparisons are never relabeled `OpenIn`.

This is an architectural/informational differential, not a claim that classical mathematics cannot express the same structures.

See [`CLASSICAL_VS_CLOSURE_RUN.md`](CLASSICAL_VS_CLOSURE_RUN.md).

### E0.9 — External axiom-geometry interaction

Status: **EXECUTED BOUNDED PROXY**.

A separately committed external axiom-geometry is frozen before candidate translation disclosure. Preservation is traced through typed edges rather than hidden normalization. `GeomEquiv` is reserved for bijective equality-preserving-and-reflecting comparisons; split extensions and closure quotients are typed separately when they are not equivalences.

The run retains literal-equality, reflection, operation-naturality, and pending-comparison controls and preserves complete relational lineage through the external interaction.

See [`THREE_PART_EXTERNAL_ASSUMPTION_RUN.md`](THREE_PART_EXTERNAL_ASSUMPTION_RUN.md).

### E1 — Generative axiom-geometry isolation

Status: **EXECUTED BOUNDED GENERATIVE PROXY**.

Two generator subprocesses receive matched task/kernel/tool/budget contracts but construct distinct registered local mathematical presentations. Each frame and its total questions are frozen and hashed before either is disclosed to the post-freeze verifier.

The enforced order is:

```text
F_A, F_B, Q_A, Q_B
  ≺ disclose
  ≺ candidate (T,phi,pi)
  ≺ GeomEquiv
  ≺ W/E/J/C + operation + question naturality
  ≺ held-out transfer.
```

The reference implementation enumerates 1,440 post-freeze candidate forms and admits six. The strong classical baseline independently retains the corresponding six ordinary isomorphisms. Rejected candidates retain explicit obstructions rather than disappearing from the evidence bundle.

Independent-interface controls include:

- raw D4/S3: cardinality `GeomEquiv` obstruction without normalization;
- D4/Q8: exhaustive absence of operation-natural maps despite structurally available equality-fibre forms;
- free-word occurrence artifact: explicit interface boundary rather than mathematical rejection;
- preservation-vs-reflection, `GeomEquiv`-vs-naturality, missing-`pi`, and pending-comparison controls.

This is causal generative isolation inside a deterministic bounded proxy. It does not establish autonomous ASI provenance or an Aristotle run.

See [`GENERATIVE_AXIOM_GEOMETRY_ISOLATION_PROTOCOL.md`](GENERATIVE_AXIOM_GEOMETRY_ISOLATION_PROTOCOL.md), [`GENERATIVE_AXIOM_GEOMETRY_ISOLATION_RUN.md`](GENERATIVE_AXIOM_GEOMETRY_ISOLATION_RUN.md), and [`../benchmarks/generative_axiom_geometry_isolation/RUNBOOK.md`](../benchmarks/generative_axiom_geometry_isolation/RUNBOOK.md).

### E1.1 — Translational-completion maze topology

Status: **EXECUTED BOUNDED DESIGNED PROXY**.

This standalone run does not retrofit topology onto the older receipt-lineage
experiments. It freezes each local axiom-geometry/equality before a single
directed learning-line set, derives raw reach, and withholds the six declared
return lines for a pre-return control. Before return, reach has 168 missing
reverse pairs and fails to realize 552 frozen-equality pairs. After return, all
48 generating lines have explicit 15-line reverse paths; the 768 reach pairs
form an equivalence and exactly realize three previously frozen classes of 16.

Only then does the runtime derive the saturation topology on occurrences: 8
open sets, three return-connected (strongly/mutually reachable) fibres, and a non-discrete occurrence space.
The whole space is not connected in the standard topological sense, which is
reported separately from completion. One learning episode has pole-swap return
monodromy while preserving returned identity; two episodes return
literally. Proof-relevant homotopy classification remains pending.

The run executes the four completion/`LocalIVI_W` combinations, explicit
`UNDERCOMPLETE` and `OVERREACH` controls, SCC-loss and manufactured-return
controls for incomplete relations, quotient factorization, witnessed
`OpenIn`, a 96-form post-freeze translation family with 12 fully natural forms
and 1,728 passing registered-question transport cases,
and a before/after receipt-gate recomputation. A strong classical Floyd-Warshall/SCC baseline
reproduces the finite relations and topology counts exactly.

NRRF639 is a separately reported result whose source is not in this checkout;
this experiment tests a finite analogue whose conditions can be compared with
the reported boundary; it does not re-audit or replace it. See
[`TRANSLATIONAL_COMPLETION_MAZE_TOPOLOGY_RUN.md`](TRANSLATIONAL_COMPLETION_MAZE_TOPOLOGY_RUN.md).

## Reproduction

A reviewer can reproduce the principal verification suite directly:

```bash
python3 experiments/full_stack_math_asi.py --assert-reference
python3 experiments/classical_vs_closure_asi.py --assert-reference
python3 experiments/three_part_assumption_interaction_asi.py --assert-reference
python3 experiments/generative_axiom_geometry_isolation.py --assert-reference
python3 experiments/translational_completion_maze.py --assert-reference
python3 -m unittest discover -s tests -v
lake build
```

Committed evidence must replay byte-identically. CI reruns the experimental and Lean kernels.

## Primary frontier experiment — Aristotle-generated frames

Status: **ACTIVE; isolated local generation executed, all cross-frame stages remain open.** This native-translation-first protocol is the sole primary frontier experiment. It replaces the earlier generic instruction to begin with `GeomEquiv`.

The next experiment should not redesign the verifier. It should replace the bounded frame generators with genuinely independent frontier mathematical-agent sessions while preserving the published protocol.

### Phase A — independent local generation (executed initial pair)

Two isolated Aristotle sessions receive the same abstract mathematical objective but no access to each other's construction, terminology, equality, or eventual translator. Each session may choose its own primitives, axioms, geometry, representation, and proof decomposition.

Each output is evaluated first in its own unified axiom-geometry and then frozen:

```text
Aristotle A → F_A, Q_A → internal audit → hash/freeze
Aristotle B → F_B, Q_B → internal audit → hash/freeze
```

No older frame is silently substituted as a normal form. The initial pair was created as two separate Aristotle jobs from the same neutral packet and each formalizes a single frame only. Each reports no `sorry` and deliberately omits identity quotients, cross-frame equivalence, translations, completion, and reverse-path targets. See [`ARISTOTLE_NATIVE_TRANSLATION_PROTOCOL.md`](ARISTOTLE_NATIVE_TRANSLATION_PROTOCOL.md).

### Phase B — native translation (executed); identity-independent validation (open)

Only after both frames freeze are they disclosed to the translation process:

```text
F_A, F_B
  → frozen native translation T_AB
  → primitive-relation/operation preservation
  → held-out local consequences + recovery
  → candidate relational equality / GeomEquiv?
```

The Phase B translator completed `T_AB v0.1.0`: 66 declaration-role entries, comprising 36 `MAPPED`, 10 `AMBIGUOUS`, and 20 `UNMAPPED` entries. It preserves a typed evidence table, every unresolved item, and local Lean evidence without making any cross-frame equality or `GeomEquiv` claim. The result discovered a concrete interface boundary: the two frozen artifacts declare the same fully qualified `NeutralFrame` names and cannot be co-imported without editing frozen sources. This prevents a cross-frame Lean map at this stage and is retained as evidence, not repaired by renaming.

The next open step is identity-independent validation: primitive-relation/operation preservation, held-out local consequences, and recovery against the admitted translation interface. The validator must apply its preregistered `UNMAPPED`/`AMBIGUOUS` rule rather than use a later equality or completion result to repair a translation. Neither source frame may be repaired after candidate disclosure. See the committed Phase B manifest for project/task identifiers and content hashes.

### Phase C — independent return and downstream evaluation

Only after candidate equality is recorded does a return generator receive the admitted frozen forward interface. It may not receive target reverse edges, identity outcome, or downstream scores.

```text
candidate equality
  → independent return generation
  → translational completion
  → LocalIVI_A, LocalIVI_B, CrossFrameIVI_AB
  → topology naturality, receipts, question transport, held-out transfer
```

### Phase D — outcomes

All outcomes are informative and must retain lineage:

- **natural translation:** equality preservation/reflection plus downstream commuting structure succeeds;
- **equality obstruction:** no `GeomEquiv` exists under the registered interface;
- **downstream obstruction:** `GeomEquiv` exists but a declared operation/naturality square fails;
- **frame-relative openness:** a precommitted total question has an explicit frame-equal separating witness;
- **pending/interface boundary:** evidence is insufficient or the artifact lies outside the registered comparison interface; this is not `OpenIn`.

The strongest positive result would be substantially different independently generated Aristotle frames connected by the frozen protocol, with successful held-out mathematical transfer and no canonical normalization. `LocalIVI_A` and `LocalIVI_B` are not cross-frame evidence by themselves; `CrossFrameIVI_AB` requires a returned relational identification that survives the admitted native translation and its identity-independent validation.

## Submission claim boundary

The repository currently supports these statements:

- the translational axiometry has machine-checked conditional formal results;
- the verification architecture is executable and reproducible on bounded mathematical systems;
- strong classical baselines recover ordinary isomorphisms rather than being artificially weakened;
- the translational arm adds explicit frame-equality, naturality, quotient-question, obstruction, and lineage certificates;
- positive, negative, pending, and frame-relative-open outcomes are kept distinct;
- the bounded programme includes generative isolation and external axiom-geometry interaction.

It does **not** currently establish:

- a completed cross-frame Aristotle result (the isolated local-generation stage is complete, but translation and downstream stages are not);
- general mathematical-ASI verification;
- that every pair of axiom-geometries admits translation;
- that classical foundations cannot express translational closure;
- that the metaphysical interpretation is an unconditional theorem.

The grant asks for the frontier experiment needed to cross exactly that remaining evidentiary boundary.

## Secondary research directions

The following remain worthwhile but are **not prerequisites for submission or for the Aristotle experiment**:

- richer axiom/geometry migration across formal foundations;
- open-ended learning beyond enumerated hypothesis families;
- independently generated evolutionary histories and path-independence tests;
- adversarial closure breaks beyond the current finite fixtures;
- classification of richer fibres beyond the established reversal/parity results;
- stronger representation/necessity theorems under explicitly stated additional premises.

These directions should be pursued when frontier experiments expose a concrete need for them, rather than being read as missing pieces of the current bounded verification system.

## Evidence rule

Every run preserves exact inputs/outputs, hashes, environment versions, proof-kernel output, candidate lineage, counterexamples, and frame-qualified open questions. An undocumented retry selected only because it closes is invalid evidence. A counterexample or precise interface boundary counts as a successful research outcome.

## Programme-level falsification

The architecture is challenged if increasing representational freedom causes the frozen protocol to lose its ability to distinguish natural cross-frame equality from equality collapse, downstream non-naturality, frame-relative openness, pending evidence, or self-certified identity—or if successful comparison requires secretly replacing independent frames with one privileged canonical representation.
