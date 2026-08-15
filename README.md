# Translational Axiometry for Mathematical ASI Verification

This repository develops a machine-checkable research program for **verification under mathematical self-reexpression**.

The motivating problem is not only whether an AI can produce a proof that a fixed kernel accepts. A mathematical superintelligence may change representations, invent mathematical languages, alter internal proof strategies, reorganize axiomatizations, and pass through intermediate reasoning systems that are not naturally identified with the verifier's starting language.

The research question is therefore:

> **What can remain verifiable when mathematical intelligence is allowed to change the language and representation in which it reasons?**

The current formal kernel is `lean/NRRF627ClosureTranslationalFrameworkAxiometryASIEvolutionaryVerification.lean`. It defines a self-contained `TransFrame` and proves closure, axiometry, ASI-gauge, evolutionary-verification, and non-vacuity results using Lean/Mathlib.

`lean/NRRF627WeakRequirementsRepresentation.lean` supplies the first representation bridge: a
common relational carrier plus reversible language codecs constructs translation, inverse
translation, identity/composition coherence, and the commuting return square. The stronger claim
that origin independence and recoverability alone force those codecs remains open.

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

The closure language returns relational content, never a truth-status label:

```text
W_ℓ : Y_ℓ → B_ℓ
CEq W u v  :=  W_ℓ(u) = W_ℓ(v)
W_m(T_ℓm u) = φ_ℓm(W_ℓ u)
```

`RETURNED`, `CONTRADICTED`, and `UNRESOLVED` are external audit records about whether a proposed
translation established that commuting relation. They are not values produced by `W` and are not
part of the foundational axiometry.

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

## Executed independent full-stack run

The repository now contains an executed classical mathematical-agent proxy, not only a proposed
protocol. Two isolated processes independently learned and executed different D4 presentations;
their states were frozen before a third process searched for a translation. The translator could
not inspect the complete precommitted return `W`. An external auditor then recorded:

| Branch | Return | Evidence |
|---|---:|---|
| relative contact | `RETURNED` | 8/8 element returns and 64/64 ordered products |
| abstract structure only | `UNRESOLVED` | eight isomorphisms remain; no arbitrary origin selected |
| reversed contact | `CONTRADICTED` | four explicit return contradictions |
| self-certification only | `UNRESOLVED` | no independent bridge evidence |

Exactly one token was issued after the relation was independently returned, and the returned bridge successfully became
the next execution basis. This closes the bounded classical-proxy milestone; it does **not** claim
an Aristotle run or an actual open-ended mathematical ASI.

The experiment's decisive control is causal rather than numerical:

```text
W_precommit ≺ (A,B)_learn+execute ≺ freeze ≺ T_posthoc ≺ ReturnAudit_W(T_posthoc)
```

It therefore tests returned translational identity separately from abstract isomorphism,
contradictory re-expression, and self-certification.

Reproduce it with:

```bash
python3 experiments/full_stack_math_asi.py --assert-reference
python3 -m unittest discover -s tests -v
lake build
```

See [`docs/FULL_STACK_RUN.md`](docs/FULL_STACK_RUN.md).

## Metaphysical motivation

The metaphysical thesis is **relation prior to isolated selection**. A pole such as `0` or `∞` is not treated as an absolute object whose identity is fixed before comparison. Its identity is disclosed by relative translational order inside closure. Thus `0` and `∞` may be distinct presentations while closure-equal, with orientation recording their relative distinction.

Axiometry, in this usage, is therefore not simply another fixed axiom system. It asks for the relation between axiom, geometry, language, translation, and recoverable return when no one language is privileged as the global origin.

See [`docs/METAPHYSICS.md`](docs/METAPHYSICS.md).

## IVI

**IVI — intangibly verified information —** is the proposed interpretation of information whose identity is given by recoverable closure rather than by identity of its local presentation. In the verification program, IVI is treated as *relational potential*: a candidate invariant must survive admissible return, while claims that cannot yet be returned remain UNRESOLVED rather than being promoted to verified content.

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
- `lean/NRRF627WeakRequirementsRepresentation.lean` — derived translation/return representation bridge.
- `lean/NRRF627IndependentReturnBridge.lean` — relational-return audit, token bound, and independent-return construction.
- `benchmarks/full_stack_d4/` — precommitted independent-learning and translator protocols.
- `experiments/full_stack_math_asi.py` — isolated learning, execution, translation, and return runtime.
- `runs/full_stack_d4/latest/` — frozen deterministic evidence bundle.
- `docs/FULL_STACK_RUN.md` — exact executed result and claim boundary.
- `docs/GRANT.md` — Harmonic/Aristotle research proposal.
- `docs/METAPHYSICS.md` — relational and translational foundations.
- `docs/IVI.md` — IVI and unresolved relational potential.
- `docs/CLASSICAL_VS_CLOSURE.md` — classical mathematical ASI versus closure runtimes.
- `docs/EXPERIMENTS.md` — falsifiable experimental program.

## Research standard

The project labels claims as **PROVED**, **CONJECTURED**, **EXPERIMENTAL**, or **METAPHYSICAL
INTERPRETATION**. The complete audit boundary is [`docs/CLAIM_STATUS.md`](docs/CLAIM_STATUS.md).
