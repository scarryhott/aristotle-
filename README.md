# Translational Axiometry for Mathematical ASI Verification

This repository develops a machine-checkable research program for **verification under mathematical self-reexpression**.

The motivating problem is not only whether an AI can produce a proof that a fixed kernel accepts. A mathematical superintelligence may change representations, invent mathematical languages, alter internal proof strategies, reorganize axiomatizations, and pass through intermediate reasoning systems that are not naturally identified with the verifier's starting language.

The research question is therefore:

> **What can remain verifiable when mathematical intelligence is allowed to change the language and representation in which it reasons?**

The current formal kernel is `lean/NRRF627ClosureTranslationalFrameworkAxiometryASIEvolutionaryVerification.lean`. It defines a self-contained `TransFrame` and proves closure, axiometry, ASI-gauge, evolutionary-verification, and non-vacuity results using Lean/Mathlib.

## Closure relation

The conceptual progression is

```text
relation / closure
      ↓
orientation ↔ extension
      ↓
relative axiom ↔ geometry
      ↓
closure language
      ↓
translation between languages
      ↓
verification return W
      ↓
axiometric verdict
```

No closure language is declared the absolute origin. Languages are compared pairwise through coherent translations. Distinct presentations may therefore remain distinct as occurrences while being closure-equal through their verification return.

## What NRRF627 establishes

Within `TransFrame`:

- closure equality is preserved and reflected by translation;
- polar presentations can be closure-equal without being identical occurrences;
- language-independent, closure-respecting verdicts are exactly measurements of the verification return;
- return-invisible restructuring preserves such verdicts;
- reexpression through another language preserves verification;
- coherent evolutionary routes depend only on endpoints;
- evolutionary verification is exactly return measurement;
- verification need not reconstruct the full occurrence;
- a reversal walk retains a translation-compatible parity residue;
- explicit models witness non-vacuity.

These are conditional mathematical results. The repository does **not** claim that arbitrary AI self-modification automatically satisfies `TransFrame`.

## The grant program

The proposed Harmonic/Aristotle research project asks whether the closure structure can be **derived, tested, or falsified on independently specified mathematical-agent dynamics**.

The grant would fund the missing bridge:

```text
independently specified mathematical agent
              ↓
representation / language changes
              ↓
recoverable translations and returns?
              ↓
derive TransFrame  OR  produce obstruction
              ↓
machine-checked verification boundary
```

A successful project is not required to confirm the framework. Admissible outcomes are `PROVED`, `FALSE_WITH_COUNTEREXAMPLE`, or `OPEN_WITH_MINIMAL_OBSTRUCTION`.

See [`docs/GRANT.md`](docs/GRANT.md) and [`docs/EXPERIMENTS.md`](docs/EXPERIMENTS.md).

## Metaphysical motivation

The metaphysical thesis is **relation prior to isolated selection**. A pole such as `0` or `∞` is not treated as an absolute object whose identity is fixed before comparison. Its identity is disclosed by relative translational order inside closure. Thus `0` and `∞` may be distinct presentations while closure-equal, with orientation recording their relative distinction.

Axiometry, in this usage, is therefore not simply another fixed axiom system. It asks for the relation between axiom, geometry, language, translation, and recoverable return when no one language is privileged as the global origin.

See [`docs/METAPHYSICS.md`](docs/METAPHYSICS.md).

## IVI

**IVI — intangibly verified information —** is the proposed interpretation of information whose identity is given by recoverable closure rather than by identity of its local presentation. In the verification program, IVI is treated as a *potential gate*: a candidate invariant must survive admissible return, while claims that cannot yet be returned remain OPEN rather than being promoted to verified content.

See [`docs/IVI.md`](docs/IVI.md).

## Classical mathematical ASI vs closure runtimes

A classical mathematical ASI can be idealized as becoming increasingly capable inside a sufficiently fixed formal substrate:

```text
statement → proof search → proof term → trusted kernel
```

A closure runtime studies the higher-order case in which the agent can also change the representational language:

```text
L₀ → L₁ → ... → Lₙ
 |              |
 W₀            Wₙ
  \____________/
   recoverable return
```

The two are complementary. Closure verification does not replace Lean's trusted kernel. Lean checks each formal theorem; translational axiometry asks what relation should be checked **between changing formal perspectives**.

See [`docs/CLASSICAL_VS_CLOSURE.md`](docs/CLASSICAL_VS_CLOSURE.md).

## Repository map

- `lean/NRRF627ClosureTranslationalFrameworkAxiometryASIEvolutionaryVerification.lean` — formal kernel.
- `docs/GRANT.md` — Harmonic/Aristotle research proposal.
- `docs/METAPHYSICS.md` — relational and translational foundations.
- `docs/IVI.md` — IVI and the potential gate.
- `docs/CLASSICAL_VS_CLOSURE.md` — classical mathematical ASI versus closure runtimes.
- `docs/EXPERIMENTS.md` — falsifiable experimental program.

## Research standard

The project separates three levels explicitly: **machine-checked theorem**, **interpretation**, and **open research claim**. The purpose of the grant is to reduce the third category without conflating it with the first.