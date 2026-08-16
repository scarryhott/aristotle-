# Translational Axiometry for Mathematical ASI Verification

This repository contains a **machine-checked translational theory and a self-contained executed verification suite** for verification across changing mathematical reference frames. It is not only a proposal.

## What is already complete

The bounded programme already executes the following causal architecture:

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

It includes independent classical mathematical-agent proxies, a strong ordinary-isomorphism baseline on identical frozen inputs, external axiom-geometry interaction, generative frame isolation, exhaustive candidate search, explicit positive/negative/pending controls, deterministic evidence replay, and Lean verification.

The bounded generative experiment freezes `F_A`, `F_B`, and their total questions before disclosure, then tests 1,440 explicit post-freeze `(T,phi,pi)` forms. Six ordinary isomorphisms are retained by the strong classical baseline and the same six satisfy the declared translational `GeomEquiv` and naturality obligations. Raw non-equivalent controls produce explicit obstructions rather than being normalized into compatibility.

## The one primary next experiment

The remaining grant-scale test is deliberately narrow:

> **Run this already-frozen verification architecture on mathematical axiom-geometries generated independently by Aristotle or another frontier mathematical agent.**

The verifier should not be redesigned after seeing those outputs. Each novel frame must first stand in its own unified axiom-geometry; only after both frames are frozen should candidate translations be disclosed and checked.

```text
Aristotle A → F_A → internal audit → freeze
Aristotle B → F_B → internal audit → freeze
                         ↓
                post-freeze (T,phi,pi)
                         ↓
                    GeomEquiv?
                         ↓
                     naturality?
                         ↓
             questions + held-out transfer
```

A natural translation, explicit equality obstruction, downstream naturality obstruction, genuine frame-relative `OpenIn`, or registered interface boundary are all substantive outcomes. The experiment does not require every frame to translate to every other frame.

See [`docs/GRANT.md`](docs/GRANT.md) and the submission-oriented [`docs/EXPERIMENTS.md`](docs/EXPERIMENTS.md).

## Reproduce the verification suite

```bash
python3 experiments/full_stack_math_asi.py --assert-reference
python3 experiments/classical_vs_closure_asi.py --assert-reference
python3 experiments/three_part_assumption_interaction_asi.py --assert-reference
python3 experiments/generative_axiom_geometry_isolation.py --assert-reference
python3 -m unittest discover -s tests -v
lake build
```

Committed evidence is designed to replay deterministically; CI reruns the experimental and Lean kernels.

## Foundational starting point

The project does **not** begin with one fixed axiom system, one absolute geometry, or already isolated mathematical objects to which translations are added afterward. Its foundational proposal is:

```text
natural translational existence
        ↓
relative axiom ↔ geometry / reference frame
        ↓
admitted relational equality
        ↓
relational definition and closure forms
```

An axiom has its mathematical role relative to the geometry/reference frame in which it is admissible; geometry is correspondingly not prior to axiom. Distinct axiom-geometries are first allowed to stand in their own unified form. Their common identity, when available, is disclosed by coherent translation and relational return rather than inherited from a privileged external presentation.

In this sense **translation is foundational and existence is natural**. Inside the formal translational frame, the commuting relation

```text
W_m(T_ℓm u) = φ_ℓm(W_ℓ u)
```

expresses the returned relational identity available across relative frames. Groupoids, quotients, natural transformations, sections, universal properties, and runtime certificates are downstream mathematical expressions and consequences of this starting point; they are not themselves the claimed foundational novelty.

## Formal architecture

The observation-free kernel is `lean/NRRF627ClosureTranslationalFrameworkAxiometryASIEvolutionaryVerification.lean`. It formalizes pairwise translations `(T,phi,pi)`, return `W`, presentations `E`, reversal `J`, and curvature representative `C`, with no language designated as the absolute origin.

Within `TransFrame`, closure equality is preserved and reflected by translation; polar presentations can be closure-equal without being literally identical; language-independent closure-respecting verdicts factor through return; coherent reexpression preserves those verdicts; and verification need not reconstruct the full occurrence.

The available bridges make later layers explicit:

- `lean/NRRF627WeakRequirementsRepresentation.lean` — representation bridge;
- `lean/NRRF627IndependentReturnBridge.lean` — relative equality and independently witnessed admission;
- `lean/NRRF631RuntimeFrameConditionalBridge.lean` — runtime `ReferenceFrame`, `GeomEquiv`, quotient factorization, transported `ResolvedIn`/`OpenIn`, and external-frame compositional identification.

The broader NRRF618–633 sequence develops the observation-free relational foundation, originless translational order, existence/naturality, frame-conditional openness, and the unique admissible open relational definition. General sources not present in this checkout are reported as such rather than reconstructed or falsely re-audited.

## Relative axiom geometry

A novel axiom-geometry is evaluated first in its **own** unified frame. It is not judged by silently treating an older frame as neutral.

A comparison becomes an axiom-geometry equivalence only when it preserves and reflects both frames' admitted equalities:

```text
x ~_F y  ↔  T(x) ~_G T(y).
```

Only afterward are downstream naturality conditions evaluated.

Resolution and openness are also frame-relative:

```text
ResolvedIn(F,Q)  ↔  Q factors through F's equality quotient
OpenIn(F,Q)      ↔  Q separates an explicit pair that F equates.
```

Pending, missing, rejected, or unselected comparisons are not called open.

## Relational return and IVI

The closure language returns relational content, never a truth-status label:

```text
W_ℓ : Y_ℓ → B_ℓ
CEq W u v := W_ℓ(u) = W_ℓ(v)
W_m(T_ℓm u) = φ_ℓm(W_ℓ u).
```

The separately reported NRRF633 result sharpens the downstream definition: within a translational frame, returning + grounded relational definition uniquely yields closure equality, after which translation forces naturality.

**IVI — intangibly verified information —** is the interpretation of naturally recoverable relational identity that does not require unique reconstruction of its local occurrence. It is downstream of relational return rather than a separate truth primitive. See [`docs/IVI.md`](docs/IVI.md).

## Executed evidence

The repository's executed suite contains four complementary bounded layers:

1. **Independent full-stack agents** — separate mathematical learners, frozen before post-hoc translation.
2. **Classical versus translational verification** — identical frozen inputs and a strong ordinary-isomorphism baseline.
3. **External axiom-geometry interaction** — separately committed geometry, typed preservation lineage, and explicit non-equivalence edges.
4. **Generative axiom-geometry isolation** — separately generated/frozen frames followed by exhaustive post-freeze candidate search.

Controls distinguish equality preservation from reflection, `GeomEquiv` from downstream naturality, genuine frame-relative openness from pending/non-selection, valid reversal from non-natural deformation, and registered interface boundaries from mathematical rejection.

See [`docs/EXPERIMENTS.md`](docs/EXPERIMENTS.md) for the concise submission view and the individual run reports under `docs/` for full evidence.

## Claim boundary

The repository supports a machine-checked conditional theory and reproducible bounded verification architecture. It does **not** currently claim:

- a qualifying autonomous Aristotle run;
- general mathematical-ASI verification;
- that every pair of axiom-geometries is equivalent;
- that classical mathematics cannot express translational closure;
- that the metaphysical interpretation is an unconditional Lean theorem.

That boundary is intentional. The grant funds the frontier-agent experiment needed to test the architecture under substantially greater representational freedom.

## Repository map

- `lean/` — formal kernel and runtime bridges.
- `experiments/` — executable bounded verification runtimes.
- `benchmarks/` — precommitted protocols and runbooks.
- `runs/` — frozen deterministic evidence and receipts.
- `docs/GRANT.md` — Harmonic/Aristotle research request.
- `docs/EXPERIMENTS.md` — submission-oriented completed evidence + single frontier experiment.
- `docs/CLAIM_STATUS.md` — theorem/experiment/interpretation audit boundary.
- `docs/METAPHYSICS.md` — relative axiom-geometry and natural translational existence.
- `docs/IVI.md` — IVI as naturally recoverable relational identity.

## Research standard

Claims are separated as **PROVED**, **EXPERIMENTAL**, **OPEN/CONJECTURED**, or **METAPHYSICAL INTERPRETATION**. Familiar categorical machinery is used to express consequences of the proposed foundation; it is not presented as the foundational novelty itself.
