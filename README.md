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

The mathematical runtime begins with the equality admitted by the axiom geometry:

```text
axiom–geometry equality → ReferenceFrame
                        → GeomEquiv translation
                        → return / operation naturality
                        → ResolvedIn(frame, question) or OpenIn(frame, question)
```

No closure language is declared the absolute origin. Languages are compared pairwise through coherent translations. Distinct presentations may therefore remain distinct as occurrences while being closure-equal through their verification return.

The closure language returns relational content, never a truth-status label:

```text
W_ℓ : Y_ℓ → B_ℓ
CEq W u v  :=  W_ℓ(u) = W_ℓ(v)
W_m(T_ℓm u) = φ_ℓm(W_ℓ u)
```

The runtime does not attach a three-valued verdict to closure. It records whether a `GeomEquiv` has
an independent witness and whether a candidate has a concrete counterexample. Resolution and
openness occur only in records that name both a frame and a total question. They are not values
produced by `W` and are never inferred from mere non-selection of a comparison.

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
their states were frozen before a third process constructed axiom-geometry comparisons. The verifier then
executed the whole `(W,E,T,phi,pi,J,C)` relation:

| Branch | Axiom-geometry result | Admission |
|---|---|---:|
| relative contact | one preserving `GeomEquiv` independently selected | 1 |
| relative reversal | another valid `GeomEquiv` with nontrivial `pi` | control |
| structural family | all eight `GeomEquiv` forms cohere; none is selected | 0 |
| non-natural deformation | bijectivity and operation naturality fail explicitly | 0 |
| self-certification only | no independent contact selects a `GeomEquiv` | 0 |

Exactly one token was issued after the relation was independently returned, and the returned bridge successfully became
the next execution basis. This closes the bounded classical-proxy milestone; it does **not** claim
an Aristotle run or an actual open-ended mathematical ASI.

After the presentations are frozen, the experiment's mathematical order is:

```text
closure equality ≺ ReferenceFrame ≺ GeomEquiv(T,phi,pi)
                 ≺ return/naturality ≺ ResolvedIn/OpenIn ≺ next basis
```

It therefore tests whether learned operation forms extend to natural translational equality. Eight
coherent comparisons are retained as `GeomEquiv` forms rather than called an internal ambiguity;
only a transformation that fails the operations is rejected.

Reproduce it with:

```bash
python3 experiments/full_stack_math_asi.py --assert-reference
python3 experiments/classical_vs_closure_asi.py --assert-reference
python3 -m unittest discover -s tests -v
lake build
```

See [`docs/FULL_STACK_RUN.md`](docs/FULL_STACK_RUN.md).
The exact NRRF630-to-runtime correspondence is
[`docs/RUNTIME_RELATIVE_EQUALITY.md`](docs/RUNTIME_RELATIVE_EQUALITY.md).

## Metaphysical motivation

The metaphysical thesis is **relation prior to isolated selection**. A pole such as `0` or `∞` is not treated as an absolute object whose identity is fixed before comparison. Its identity is disclosed by relative translational order inside closure. Thus `0` and `∞` may be distinct presentations while closure-equal, with orientation recording their relative distinction.

Axiometry, in this usage, is therefore not simply another fixed axiom system. It asks for the relation between axiom, geometry, language, translation, and recoverable return when no one language is privileged as the global origin.

See [`docs/METAPHYSICS.md`](docs/METAPHYSICS.md).

## IVI

**IVI — intangibly verified information —** is the proposed interpretation of information whose identity is given by recoverable closure rather than by identity of its local presentation. In the verification program, IVI is treated as *relational potential*: resolution or openness is meaningful only relative to the equality of a named frame.

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

### Executed paired verification runtime

The repository also executes a controlled fixed-frame-versus-closure comparison over identical
frozen D4 learner artifacts. Before any candidate map is constructed, each language independently
freezes a primitive operational equality table: the distinct local programs `x` and `x·e` are
equated exactly when their complete right-action signatures agree. The quotient return is derived
only after a candidate preserves and reflects that equality.

The fixed-frame arm is a strong baseline: it accepts all eight ordinary isomorphisms, including
reversal, and rejects adversarial maps conventionally. The closure arm retains the same eight maps
while additionally recording `GeomEquiv`, downstream naturality, quotient factors, explicit
frame-equal openness witnesses, and next-basis transfer. Its bounded differential is executed; the
corresponding frontier-agent/Aristotle comparison remains open and falsifiable.

See [`docs/CLASSICAL_VS_CLOSURE_RUN.md`](docs/CLASSICAL_VS_CLOSURE_RUN.md).

## Repository map

- `lean/NRRF627ClosureTranslationalFrameworkAxiometryASIEvolutionaryVerification.lean` — formal kernel.
- `lean/NRRF627WeakRequirementsRepresentation.lean` — derived translation/return representation bridge.
- `lean/NRRF627IndependentReturnBridge.lean` — frame-relative equality, witness-based token bound, and independent-return construction.
- `lean/NRRF631RuntimeFrameConditionalBridge.lean` — runtime `ReferenceFrame`, `GeomEquiv`, quotient factorization, and transported `ResolvedIn`/`OpenIn`.
- `benchmarks/full_stack_d4/` — precommitted independent-learning and translator protocols.
- `experiments/full_stack_math_asi.py` — isolated learning, execution, translation, and return runtime.
- `runs/full_stack_d4/latest/` — frozen deterministic evidence bundle.
- `benchmarks/classical_vs_closure/` — paired architecture precommit, primitive-frame protocols, questions, and runbook.
- `experiments/classical_vs_closure_asi.py` — isolated equality-frame derivation and fixed-frame/closure comparison.
- `runs/classical_vs_closure/latest/` — deterministic paired evidence bundle.
- `docs/CLASSICAL_VS_CLOSURE_RUN.md` — exact comparative result and frontier-study boundary.
- `docs/FULL_STACK_RUN.md` — exact executed result and claim boundary.
- `docs/RUNTIME_RELATIVE_EQUALITY.md` — naturality/existence theorem-to-runtime map.
- `docs/FRAME_CONDITIONAL_OPENNESS.md` — frame equality, `GeomEquiv`, and qualified `ResolvedIn`/`OpenIn` integration.
- `docs/GRANT.md` — Harmonic/Aristotle research proposal.
- `docs/METAPHYSICS.md` — relational and translational foundations.
- `docs/IVI.md` — IVI and open relational potential.
- `docs/CLASSICAL_VS_CLOSURE.md` — classical mathematical ASI versus closure runtimes.
- `docs/EXPERIMENTS.md` — falsifiable experimental program.

## Research standard

The project labels claims as **PROVED**, **CONJECTURED**, **EXPERIMENTAL**, or **METAPHYSICAL
INTERPRETATION**. The complete audit boundary is [`docs/CLAIM_STATUS.md`](docs/CLAIM_STATUS.md).
