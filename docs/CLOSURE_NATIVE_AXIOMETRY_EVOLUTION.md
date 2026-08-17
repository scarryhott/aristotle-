# Closure-native axiometry evolution

## Why this experiment is needed

The current locally audited Lean kernel is intentionally conditional: `TransFrame` begins with already constituted local languages/frames and proves what follows when pairwise translations, return, reversal, curvature, and coherence satisfy the declared laws. That is useful for verification, but it can be read too strongly as if closure itself required a fixed family of already completed axiom-geometries.

That is **not** the metaphysical thesis of this project.

The stronger closure claim is:

> **Translation does not merely transport identity between already-final frames. A completed translation and independent return may participate in forming the next relative axiom-geometry.**

Accordingly, the project distinguishes two uses of freezing:

```text
experimental freeze
    = preserve the evidence produced by one episode so it cannot be repaired post hoc

axiometry
    = allowed to evolve between episodes through auditable translation, return, and completion
```

Historical evidence is immutable. Axiometry is not.

## Current formal boundary

The present `TransFrame` layer has the form

```text
{F_l}_l + {T_lm}_lm
```

where each `F_l` already carries its local occurrence space, returned basis/equality, presentation, reversal, curvature representative, and related structure before cross-frame translation is evaluated.

This establishes conditional originlessness: no member of the family must be privileged as the absolute language. It does **not by itself establish closure-native axiometric evolution**, because the family of admissible frame structures is supplied before the translation theorem is applied.

The distinction is:

```text
origin-free comparison of supplied frames
    !=
frames generated/evolved by completed translation itself
```

This limitation is now an explicit research boundary rather than being hidden inside the word `closure`.

## Closure-native state

The proposed next abstraction begins from an evolving relational state rather than a globally fixed frame family.

At episode `t`:

```text
S_t = (F_t, H_t)
```

where:

- `F_t` is the current relative axiom-geometry/perspective;
- `H_t` is immutable provenance for completed prior episodes.

An interaction produces a candidate translational extension:

```text
S_t -> Proposal_t
```

A separately generated return supplies return evidence:

```text
(F_t, Proposal_t) -> ReturnEvidence_t
```

Completion is evaluated only afterward. When the episode is admitted, the next frame is **derived from the completed relational state**:

```text
CompletedEpisode_t
    -> nextFrame
    -> F_(t+1)
```

The target is therefore not a theorem that `F_(t+1) = F_t`. The target is an auditable relation showing that `F_(t+1)` may change carrier, primitive relations, admitted equality, topology, operations, questions, or orientation while retaining the completed relational lineage from `F_t`.

## Closure-native hypothesis

The experiment tests:

```text
F_t
  -> independently produced translation/proposal T_t
  -> independently produced return rho_t
  -> completion audit
  -> completed relational state
  -> F_(t+1)
  -> new admissible translations/questions
```

The hypothesis is that completed relational return can generate a new local frame without requiring a permanent origin language or silently normalizing the new frame back into the old one.

This is the operational reading of **interactive continual completion**.

## Static-frame control versus closure-native arm

The experiment should use identical initial evidence and interaction packets for two arms.

### Control: supplied/static axiometry

```text
F_0 -> T_0 -> evaluate in F_0
F_0 -> T_1 -> evaluate in F_0
F_0 -> T_2 -> evaluate in F_0
```

The reference axiometry remains fixed. New evidence may be represented only insofar as the original frame can already express it.

### Closure-native arm

```text
F_0
  -> (T_0, rho_0) -> completion -> F_1
  -> (T_1, rho_1) -> completion -> F_2
  -> ...
```

Each admitted completion may alter the equality level and axiom-geometry available to the next episode.

The decisive task should contain a later distinction or relation that cannot be represented faithfully in `F_0` without either collapsing information or adding structure. The question is whether the closure-native arm can form an adequate `F_1`/`F_2` from completed lineage while the static arm exposes the corresponding representational obstruction.

## Non-negotiable causal rules

1. **Do not alter the current preregistered Aristotle native-translation experiment.** Its frozen frames are required to test leakage-free cross-frame comparison.
2. Freeze every episode's inputs, outputs, candidate translation, return evidence, evaluation, and hashes before the next frame is constructed.
3. Do not freeze one axiometry as the evaluator for all future episodes.
4. `nextFrame` must be downstream of independently recorded translation and return evidence; it cannot be supplied as the target that those stages are asked to reproduce.
5. A failed or incomplete episode may not be promoted into a new frame merely because doing so makes a later task solvable.
6. Preserve all `UNMAPPED`, `AMBIGUOUS`, obstruction, and outside-interface records in history.
7. A later successful frame may not rewrite the evidentiary status of an earlier failed comparison.

## Proposed formal targets

A closure-native Lean layer should be developed **above or beside**, not by silently changing the meaning of, the existing `TransFrame` results.

Candidate structures:

```text
ClosureState
EpisodeProposal
ReturnEvidence
CompletedEpisode
nextFrame
```

Desired theorem classes include:

### Historical preservation

```text
history(step s e) extends history(s)
```

No admitted event erases earlier translation, return, ambiguity, or obstruction evidence.

### No frame without completion

A frame transition labelled as closure-derived requires the declared completed episode; an attempt or forward translation alone cannot manufacture the next admitted basis.

### Axiometry may genuinely change

Exhibit a model in which

```text
Equality(F_(t+1)) != Equality(F_t)
```

or another registered structural component changes, while the transition retains a verified relational lineage to the previous state.

### No hidden origin

The construction of `F_(t+1)` must not require selecting one prior language as a globally privileged normal form beyond the local episode data being related.

### Regeneration / Slearn bridge

The next closure state should remain sufficient to regenerate the perspective/interface projections required by the Slearn runtime contract, while the rendered interface remains a lossy projection rather than the persisted source of truth.

## Relation to the current Aristotle experiment

The two experiments answer different questions.

### Aristotle Experiment I — frozen-frame native translation

```text
independent F_A, F_B
  -> blind native translation
  -> identity-independent validation
  -> candidate equality
  -> independent return
  -> completion / IVI / topology / transfer
```

Question: **Can independently generated frames be related without assuming their identity in advance?**

This experiment remains frozen and preregistered exactly because changing its frames would destroy the causal test.

### Aristotle Experiment II — closure-native axiometry evolution

```text
F_t
  -> interaction / translation
  -> independent return
  -> completion
  -> derived F_(t+1)
  -> next interaction
```

Question: **Can completed relational translation participate in generating the axiometry of the next frame?**

Experiment II begins only after its own protocol is preregistered. Results from Experiment I may motivate the design but may not be retrospectively reinterpreted as having already executed Experiment II.

## Relation to Slearn

The Slearn closure thesis is longitudinal:

```text
perspective_t
  -> WHY / attempt / interaction
  -> return
  -> experience / completion
  -> perspective_(t+1)
```

If the formal substrate permanently fixes the equality geometry, the interface can appear to change perspective while the semantics remain static. The closure-native experiment tests the stronger requirement that completed learning may change the equality level and relational basis from which later WHY paths are generated.

Thus the intended common loop is:

```text
experience
  -> independent return
  -> translational completion
  -> new relative frame/equality level
  -> new possible questions and translations
```

## Claim boundary

This document **does not claim that closure-native axiometry evolution has already been proved or executed**.

Current locally audited Lean results establish conditional properties of supplied translational frames. Current Aristotle evidence tests frozen-frame native translation and its downstream stages. The closure-native evolutionary construction described here is a newly explicit next experiment and formalization target.

A positive result would require an executed longitudinal run plus an explicit formal bridge showing that the next frame is derived from completed relational evidence rather than selected in advance. A negative result or representational obstruction is equally admissible evidence.
