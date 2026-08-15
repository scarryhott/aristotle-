# Translational Axiometry for Mathematical ASI Verification

This repository develops a machine-checkable and falsifiable research program for verification
under mathematical self-reexpression.

The operational problem is not only whether a proof checks in a fixed kernel. A mathematical
agent may replace its definitions, representation, axiomatization, proof strategy, or language.
The question is what permits a verifier to identify invariant content across that change without
requiring the agent to retain the verifier's starting representation.

## Claim labels

Every major claim in this repository is marked as one of:

- **PROVED** — identified by a Lean theorem or finite exhaustive test;
- **CONJECTURED** — a precise mathematical target not yet established;
- **EXPERIMENTAL** — a protocol, observation, or pending run;
- **METAPHYSICAL INTERPRETATION** — motivation not asserted as a theorem.

The complete audit table is in [`docs/CLAIM_STATUS.md`](docs/CLAIM_STATUS.md).

## Fixed proof checking and translational verification

**PROVED:** Lean checks a claim in a selected formal frame, schematically

`Γ ⊢_L P`.

**CONJECTURED / EXPERIMENTAL PROGRAM:** translational axiometry asks what must commute when the
frame itself changes:

`(L, Γ, P) --(T, φ, π)--> (L′, Γ′, P′)`.

This is complementary to Lean, not a replacement for its trusted kernel. Lean checks the local
proofs and theorems about the cross-frame bridge.

## Formal core

[`lean/NRRF627ClosureTranslationalFrameworkAxiometryASIEvolutionaryVerification.lean`](lean/NRRF627ClosureTranslationalFrameworkAxiometryASIEvolutionaryVerification.lean)
contains the exact NRRF627 kernel.

**PROVED within `TransFrame`:**

- translation is invertible from identity and composition coherence;
- closure equality is preserved and reflected;
- `(Invariant Q ∧ RespectsClosure Q) ↔ MeasuredByReturn Q`;
- the analogous evolutionary characterization is equivalent to return measurement;
- return-preserving restructuring preserves admissible verdicts;
- return may be non-faithful, and the specific reversal walk has a translation-compatible parity.

These are conditional results. They do not establish that arbitrary AI evolution satisfies
`TransFrame`, that arbitrary capability growth is gauge, or that every return fibre contains only
a `Z/2` residue.

[`lean/NRRF627WeakRequirementsRepresentation.lean`](lean/NRRF627WeakRequirementsRepresentation.lean)
adds the first representation bridge.

**PROVED by that module:** a common relational carrier plus reversible language-specific codecs
constructs the pairwise translations, inverses, orientation relabellings, identity/composition
coherence, extension law, and commuting return square. Adding explicit carrier-level `J` and `C`
operations constructs a full `TransFrame`.

**CONJECTURED:** origin independence, recoverability, and coherent comparison alone force the
existence of enough common carrier/codec structure. The present bridge narrows the missing theorem;
it does not claim to finish it.

## First falsifiable Aristotle benchmark

The D4 benchmark asks for three isolated Aristotle runs:

1. formalize square symmetries as vertex permutations;
2. independently formalize them as `Z/4 ⋊ Z/2` normal forms;
3. only after both artifacts are frozen, discover and prove a translation.

The return `W`—the full induced action on four vertices—is committed before any run. The gate then
returns:

- `TRUE` only if all 8 elements and all 64 ordered products close;
- `FALSE` when a concrete disagreement is witnessed;
- `OPEN` when no contradiction is found but a required bridge remains unresolved.

**EXPERIMENTAL STATUS:** the protocol and scorer are implemented; the actual isolated Aristotle run
remains OPEN. The built-in correct, wrong-sign, and partial translators are gate-validation
fixtures, not Aristotle evidence.

Run the local reference checks:

```bash
python3 -m unittest discover -s tests -v
python3 experiments/aristotle_d4_closure.py --assert-reference
```

Build the Lean modules with the pinned Lean/Mathlib release:

```bash
lake update
lake build
```

See [`benchmarks/d4/RUNBOOK.md`](benchmarks/d4/RUNBOOK.md) for the preregistered protocol.

## Operational mathematical ASI

For this project, a **mathematical ASI** is an agent whose future representational transformations
cannot reasonably be enumerated and fixed in advance by its verifier. This definition makes no
claim about consciousness or general superhuman ability. It isolates the verification problem:
the proof kernel may remain fixed while the mathematical frame presented to it changes.

## Repository map

- `lean/` — exact NRRF627 kernel and the weaker-requirements representation bridge;
- `benchmarks/d4/` — frozen return protocol, blind prompts, and runbook;
- `experiments/` — dependency-free exhaustive closure gate;
- `tests/` — gate and algebra tests;
- `docs/GRANT.md` — Harmonic/Aristotle research proposal and milestones;
- `docs/EXPERIMENTS.md` — benchmark status and broader experimental program;
- `docs/CLASSICAL_VS_CLOSURE.md` — fixed-frame versus cross-frame verification;
- `docs/IVI.md` — exact return-fibre definition of IVI;
- `docs/METAPHYSICS.md` — explicitly labeled philosophical motivation.

A counterexample is a successful research result when it identifies the boundary of closure more
sharply than the current axioms do.
