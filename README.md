# Translational Axiometry for Mathematical ASI Verification

This repository develops a machine-checkable research program for **verification under mathematical self-reexpression**.

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

In this sense **translation is foundational and existence is natural**: the commuting relation

```text
W_m(T_ℓm u) = φ_ℓm(W_ℓ u)
```

expresses what persists between relative frames. Groupoids, quotients, natural transformations, sections, universal properties, and runtime certificates are downstream mathematical expressions and consequences of this starting point; they are not themselves the claimed foundational novelty.

The mathematical-ASI question is therefore:

> **Can independently generated axiom-geometric reference frames remain verifiable through naturally recoverable translational equality without declaring any one frame the absolute definition of the others?**

## Formal architecture

The observation-free translational kernel is `lean/NRRF627ClosureTranslationalFrameworkAxiometryASIEvolutionaryVerification.lean`. It formalizes pairwise translations `(T,phi,pi)`, return `W`, presentations `E`, reversal `J`, and curvature representative `C`, with no language designated as the absolute origin.

Within `TransFrame`:

- closure equality is preserved and reflected by translation;
- polar presentations can be closure-equal without being literally identical;
- language-independent, closure-respecting verdicts are exactly measurements of return;
- return-invisible restructuring and coherent reexpression preserve those verdicts;
- coherent evolutionary routes depend only on endpoints;
- verification need not reconstruct the full occurrence.

The representation and runtime bridges make later layers explicit without replacing the foundational order:

- `lean/NRRF627WeakRequirementsRepresentation.lean` derives the translation/return layer from a common relational carrier and reversible presentation codecs;
- `lean/NRRF627IndependentReturnBridge.lean` formalizes relative equality and independently witnessed admission;
- `lean/NRRF631RuntimeFrameConditionalBridge.lean` formalizes a runtime `ReferenceFrame` as admitted equality, `GeomEquiv` as preservation and reflection of that equality, quotient factorization, and transported `ResolvedIn`/`OpenIn`.

The broader project sequence NRRF618–633 develops the observation-free relational foundation, originless translational order, existence/naturality, frame-conditional openness, and the unique admissible open relational definition. Where those general sources are not present in this checkout, this repository does not reconstruct them and does not falsely claim to audit them.

## Relative axiom geometry and equality

A novel axiom-geometry must first be evaluated in its **own** unified frame. It is not judged by silently treating an older frame as neutral.

For a frame `F`, its admitted equality determines which distinctions are meaningful in that frame. A comparison `T : F → G` becomes an axiom-geometry equivalence only when it preserves and reflects the respective equalities:

```text
x ~_F y  ↔  T(x) ~_G T(y).
```

Only after that comparison is established are downstream naturality conditions evaluated. Resolution and openness are likewise frame-relative:

```text
ResolvedIn(F,Q)  ↔  Q factors through F's equality quotient
OpenIn(F,Q)      ↔  Q separates an explicit pair that F equates.
```

Pending, unselected, or unavailable comparisons are not called open. Openness is a relation between a total question and a named equality geometry.

## Relational return

The closure language returns relational content, never a truth-status label:

```text
W_ℓ : Y_ℓ → B_ℓ
CEq W u v := W_ℓ(u) = W_ℓ(v)
W_m(T_ℓm u) = φ_ℓm(W_ℓ u).
```

The deeper interpretation is not that `W` creates existence from a canonical coordinate system. Rather, within the formal `TransFrame`, `W` expresses the returned relational identity whose naturality makes cross-frame persistence explicit.

The later NRRF633 theorem, supplied separately in the larger project, sharpens the downstream definitional consequence: conditional on the translational frame, a relational definition that is returning and grounded is uniquely closure equality; its naturality is then forced by translation. Thus the unique admissible relational definition is a consequence of the foundational translational structure, not the place where that structure originates.

## Executed bounded realizations

The repository contains finite operational realizations, not claims of general ASI verification.

### Full-stack D4 runtime

Two isolated symbolic learners independently learn and execute different D4 presentations. Their artifacts are frozen before cross-frame comparison. The operational order is:

```text
primitive frame equality
    ≺ raw candidate T
    ≺ GeomEquiv
    ≺ admitted translation
    ≺ W/E/J/C and operation naturality
    ≺ ResolvedIn/OpenIn
    ≺ next basis
```

All eight ordinary D4 isomorphisms are retained as coherent relative frame forms, including orientation reversal. A valid reversal is not treated as failure when its induced translation data travel naturally with it. Adversarial controls separate the layers: `equality_collapse` can preserve equality while failing reflection; `operation_twist` can pass `GeomEquiv` while failing downstream operation naturality.

### Paired classical-versus-closure runtime

`experiments/classical_vs_closure_asi.py` runs a strong ordinary isomorphism baseline and the translational arm on identical content-addressed frozen inputs. The baseline accepts all eight D4 isomorphisms, including reversal. The translational arm agrees on those ordinary equivalences while additionally producing equality-transport, quotient, naturality, witnessed-openness, and next-basis certificates.

This establishes a bounded architectural differential. It does **not** establish that translational verification is superior to all classical verification or that the proxy is an ASI.

Reproduce the current runtime with:

```bash
python3 experiments/full_stack_math_asi.py --assert-reference
python3 experiments/classical_vs_closure_asi.py --assert-reference
python3 -m unittest discover -s tests -v
lake build
```

## Grant program

The Harmonic/Aristotle proposal does not ask a novel mathematical frame to remain inside today's axiom geometry. The proposed experiment instead preserves the foundational order:

```text
independent frame A        independent frame B
       ↓                           ↓
its own axiom-geometry       its own axiom-geometry
       ↓                           ↓
its admitted equality        its admitted equality
        \                         /
         \--- post-hoc T --------/
                ↓
             GeomEquiv?
                ↓
        natural translational return?
                ↓
   transported resolution / openness
                ↓
             next basis
```

The grant asks whether increasingly capable mathematical agents, ultimately Aristotle, generate independently coherent axiom-geometries for which nontrivial natural translational relations can be discovered after the artifacts are frozen.

A successful experiment need not make every frame equivalent to every other frame. A new frame is first admitted conditionally in its own geometry. The research question is whether and how it relates translationally to another frame. Explicit obstruction and frame-relative openness are substantive outcomes rather than failures to force an absolute comparison.

See [`docs/GRANT.md`](docs/GRANT.md), [`docs/EXPERIMENTS.md`](docs/EXPERIMENTS.md), and [`docs/CLAIM_STATUS.md`](docs/CLAIM_STATUS.md).

## Metaphysical interpretation

The metaphysical thesis is **relation prior to isolated selection**, sharpened as **relative axiom-geometry with natural translational existence**.

The project does not claim that a static language first defines objects absolutely and that translation merely transports those definitions. Instead, relative frames disclose local axiom-geometric identity, while persistence between frames is constituted by admissible translation and relational return. A pole such as `0` or `∞` can therefore remain a distinct relative presentation while sharing returned relational identity; distinction survives inside closure without requiring an absolute origin.

This metaphysical interpretation motivates the formal architecture but is not silently promoted to a Lean theorem. The Lean results are conditional on their stated frame hypotheses.

See [`docs/METAPHYSICS.md`](docs/METAPHYSICS.md).

## IVI

**IVI — intangibly verified information —** is the proposed interpretation of information whose identity is recoverable relationally without requiring unique reconstruction of its local occurrence. In the translational programme, IVI belongs downstream of natural relational return: it does not supply a privileged external frame.

See [`docs/IVI.md`](docs/IVI.md).

## Repository map

- `lean/NRRF627ClosureTranslationalFrameworkAxiometryASIEvolutionaryVerification.lean` — observation-free translational kernel.
- `lean/NRRF627WeakRequirementsRepresentation.lean` — representation bridge.
- `lean/NRRF627IndependentReturnBridge.lean` — relative equality and independent-return bridge.
- `lean/NRRF631RuntimeFrameConditionalBridge.lean` — runtime frame equality, `GeomEquiv`, quotient resolution, and witnessed openness.
- `benchmarks/full_stack_d4/` — independent-learning and translation protocols.
- `experiments/full_stack_math_asi.py` — full-stack bounded translational runtime.
- `benchmarks/classical_vs_closure/` — paired comparison protocols.
- `experiments/classical_vs_closure_asi.py` — strong classical baseline versus translational arm.
- `runs/` — frozen deterministic evidence bundles and receipts.
- `docs/GRANT.md` — Harmonic/Aristotle proposal.
- `docs/METAPHYSICS.md` — foundational interpretation.
- `docs/FRAME_CONDITIONAL_OPENNESS.md` — equality geometry and conditional openness.
- `docs/RUNTIME_RELATIVE_EQUALITY.md` — formal-to-runtime naturality map.
- `docs/CLASSICAL_VS_CLOSURE.md` and `docs/CLASSICAL_VS_CLOSURE_RUN.md` — comparative architecture and executed result.
- `docs/CLAIM_STATUS.md` — formal/experimental/interpretive audit boundary.

## Research standard

The project separates **PROVED**, **EXPERIMENTAL**, **OPEN/CONJECTURED**, and **METAPHYSICAL INTERPRETATION** claims. Familiar categorical machinery is used to express consequences of the proposed foundation; it is not presented as the foundational novelty itself.
