# IVI: Intangibly Verified Information

IVI is the informational interpretation of the translational axiometry. It does **not** supply closure, a privileged verifier, or an external truth frame. It belongs downstream of the project's foundational order:

```text
natural translational existence
    → relative axiom ↔ geometry / reference frame
    → relational return
    → admitted equality
    → IVI
```

## Core idea

A mathematical identity need not be verified by uniquely reconstructing the occurrence or presentation that generated it. In the translational framework, what is recoverable across relative frames is returned relational identity.

The exact formal equality used by the available kernel is

```text
CEq W u v := W u = W v.
```

Thus two occurrences can remain distinct as presentations while sharing the same returned identity.

IVI is the proposed informational form of that distinction:

> **naturally recoverable relational identity without a requirement of unique presentation identity.**

The word *intangible* does not mean mysterious, unmeasurable, or non-mathematical. It means that verification can attach to the returned relation even when the verifier does not possess a unique reconstruction of the local occurrence.

## From translational existence to IVI

The project does not begin by defining an isolated occurrence and then asking whether another language reproduces it. A novel axiom-geometry first stands conditionally in its own reference frame. Cross-frame persistence is then expressed through translation and relational return:

```text
W_m(T_ℓm u) = φ_ℓm(W_ℓ u).
```

The metaphysical interpretation is that natural translation expresses the relational existence available between the frames. IVI is therefore not information extracted from a canonical coordinate system; it is information whose identity is recoverable through the naturally commuting relation between relative frames.

## Unique admitted relational equality

The separately reported NRRF633 development strengthens this interpretation. Conditional on the existing translational frame, a candidate relational definition is **returning** when every occurrence is admitted equal to a presentation of what it returns, and **grounded** when presentations of distinct returned identities are never identified.

NRRF633 proves that any returning, grounded relational definition is uniquely closure equality:

```text
u ~ v  ↔  W(u) = W(v).
```

Translation naturality then follows from the translational frame. Thus IVI is not interpreted relative to an arbitrarily selected equality once the frame's return/presentation structure is fixed: the returning and grounded equality is uniquely determined.

This repository does not reconstruct the unavailable general NRRF631 dependency of NRRF633; it records NRRF633 as a stronger separately supplied/reported result and audits only the sources present in this checkout.

## Why the identity can be intangible

The formal kernel deliberately permits non-faithful return. Under the relevant separation hypothesis, distinct occurrences can have the same return:

```text
u ≠ v
W(u) = W(v).
```

So verification of the returned relational identity does not imply unique reconstruction of the occurrence.

The polar form gives the simplest picture. Two relative presentations of one identity may satisfy

```text
E(0,b) ≠ E(∞,b)
W(E(0,b)) = b = W(E(∞,b)).
```

The occurrence-level orientation remains different while the returned identity is shared. IVI therefore preserves the project's central distinction:

```text
relative difference ≠ failure of relational identity.
```

## Resolution and openness

IVI is not equivalent to omniscience about an occurrence. The frame-conditional layer separates questions that depend only on relational identity from questions that demand a distinction the frame does not admit.

A question is resolved in a frame when it factors through the frame equality:

```text
ResolvedIn(F,Q)
  ↔ Q is constant on every F-equality class
  ↔ Q factors through the quotient by F's equality.
```

A question is open only when there is an explicit frame-equal separating pair:

```text
OpenIn(F,Q)
  ↔ ∃ x y, x ~_F y ∧ Q(x) ≠ Q(y).
```

This gives IVI a precise information boundary.

Questions about returned identity can resolve:

```text
Q_b(u) := (W(u) = b).
```

A static presentation question may remain open:

```text
Q_p(u) := (u = E(p,b)).
```

The frame can therefore verify relational identity while remaining open to a demand for isolated presentation identity. `OpenIn` is not a truth value, uncertainty flag, timeout, or missing translator. Pending, rejected, and unselected comparisons remain separate states in the runtime lineage.

## IVI across axiom-geometries

A novel axiom-geometry is first assumed locally and evaluated in its own equality. It is not normalized into an older frame before verification.

For two frames `F` and `G`, a candidate translation becomes an admitted axiom-geometry equivalence only when it preserves and reflects both equalities:

```text
x ~_F y  ↔  T(x) ~_G T(y).
```

Only after this `GeomEquiv` relation is established are return, orientation, reversal, curvature, learned-operation naturality, quotient resolution/openness, and next-basis transfer checked.

IVI across frames therefore means that relational identity survives this typed translational lineage. It does not mean that either frame's literal presentation is declared canonical.

## Runtime interpretation

### IVI and translational completion

The project currently uses the executed closure-translational runtime as its
operational specification and cites the NRRF599/639 Lean development as an
external formal reference. The external report guides comparison and future
bridging, but its unavailable definitions are not silently imported into the
runtime vocabulary.

The bounded maze uses a deliberately weaker local predicate:

```text
LocalIVI_W(F,b) := exists u v, u != v and W_F(u)=b and W_F(v)=b
LocalIVI_W(F)   := exists b, LocalIVI_W(F,b).
```

`LocalIVI_W` says only that a frozen return has a non-singleton fibre. It is a
local non-faithfulness witness; it does not by itself establish the stronger
cross-frame, naturally recoverable translational IVI defined above.

The separately reported NRRF639 result supplies a condition that the earlier
archive did not state: the closure thesis holds exactly when translational
completion and IVI are both present. Completion means that every raw directed
reach chain has an actual return chain, so raw reach itself is an equivalence
relation. IVI supplies the non-injective relational content: distinct
occurrences resolve together without becoming literally identical.

For the bounded runtime, the roles of completion and `LocalIVI_W` are
independent. Completion without `LocalIVI_W` yields a discrete resolved
presentation space; `LocalIVI_W` in a frozen equality without completed return
does not yet disclose a faithful reach quotient. A mutual-reach quotient can lose
one-way chains, while a manufactured equivalence closure can invent missing
returns. Neither substitutes for completion of the original relation.

NRRF639 and its NRRF599 dependency are not present in this checkout, so these
theorems remain marked as reported outside the checkout and not locally
audited. The bounded maze runtime instead executes six fixtures for a distinct
three-premise proxy: completion, `LocalIVI_W`, and exact realization of the
equality frozen before the maze was evaluated. It does not identify that proxy
with the unavailable NRRF639 `ClosureThesis`.

The exact finite topology used by that runtime is the saturation topology on
occurrences: open sets are unions of completed-reach classes. It is
non-discrete when a `LocalIVI_W` fibre has multiple occurrences. This does not imply
that the resolved quotient space itself is non-discrete or that completion
implies standard topological connectedness.

The current bounded runtimes operationalize IVI through explicit evidence lineage rather than a static verdict.

The relevant order is:

```text
assumed local axiom-geometry
    → frozen frame equality
    → raw (T,φ,π)
    → GeomEquiv
    → W/E/J/C and operation naturality
    → quotient ResolvedIn/OpenIn
    → independently witnessed admission
    → next basis.
```

A receipt or token is therefore **not payment for a proposition being declared true**. It records an actual episode in which a relational identity was independently witnessed through the admitted translational structure and was allowed to become part of the next basis.

A mathematically coherent frame form may exist without receiving an episode receipt. Self-certification alone does not create one. Counterfactual coherent forms remain controls. Rejected, partial, pending, and unselected candidates retain their lineage and are not collapsed into `OpenIn`.

## What the bounded runtime establishes

The finite experiments show that the IVI architecture can be represented operationally while retaining distinctions between:

- literal occurrence and returned identity;
- equality preservation and equality reflection;
- `GeomEquiv` and downstream naturality;
- resolved relational questions and witnessed frame-relative openness;
- mathematical admissibility and actual episode admission;
- current basis and returned next basis.

The paired classical-versus-translational runtime also uses a strong ordinary isomorphism baseline on the same frozen inputs. The translational arm does not claim novelty merely because it recognizes isomorphism or reversal. Its bounded differential is the additional relational lineage: frame equality, equality transport, naturality, quotient factorization, explicit openness witnesses, and next-basis transfer.

## What remains genuinely intangible at ASI scale

The bounded simulations are fully enumerable, so an external experimenter can still inspect essentially every state. They therefore realize the **formal structure** of IVI more strongly than its practical asymmetry.

The consequential mathematical-ASI case is stronger:

```text
the verifier cannot feasibly reconstruct the agent's full occurrence
        ∧
the verifier can still certify returned relational identity through translation.
```

A frontier mathematical agent may generate an axiom-geometry and internal representation that a weaker verifier cannot practically reconstruct. Translational IVI asks whether the relevant identity can nevertheless be recovered naturally across frames without forcing the stronger system back into the weaker system's presentation.

## Formal status

The repository should therefore distinguish the following layers:

```text
FOUNDATIONAL INTERPRETATION
relative axiom-geometry + natural translational existence

FORMAL TRANSLATIONAL THEORY
return W, relative equality, translation, GeomEquiv, naturality,
quotient resolution, frame-relative openness

STRONGER SEPARATELY REPORTED RESULT
returning + grounded relational definition is uniquely W-equality
and its naturality is forced by the translational frame

BOUNDED EXPERIMENT
independently frozen frames and explicit translational lineage

IVI INTERPRETATION
naturally recoverable relational identity without required
unique presentation reconstruction
```

IVI is therefore not a parallel metaphysical object added to translational axiometry. It is the informational interpretation of what the translational framework makes possible: **identity can be verified through natural relational return while presentation-level identity remains relative, multiple, or unreconstructed.**
