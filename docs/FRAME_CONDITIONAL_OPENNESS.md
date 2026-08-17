# Frame-Conditional Openness in the Runtime

This note integrates the NRRF631 frame-conditional mathematics into the executable D4 runtime. It
is not a copy of the general NRRF631 development, whose source is maintained outside this
repository. The local machine-checked interface is
`lean/NRRF631RuntimeFrameConditionalBridge.lean`.

## Foundation

A reference frame on occurrences is exactly its admitted equality. For a frame `F` and total
question `Q`:

```text
ResolvedIn(F,Q) := every pair equated by F receives the same Q-value
OpenIn(F,Q)     := not ResolvedIn(F,Q).
```

Resolution is equivalent to factorization through the quotient by the frame equality, with a
unique factor. `openIn_iff_exists_separating_pair` also proves that openness is equivalent to the
existence of two frame-equal occurrences separated by `Q`. Openness is therefore never a property
of `Q` alone. Its runtime witness consists of `frame_id`, `question_id`, and that separating pair.

A local question can be classified inside its own frozen frame before any
comparison exists. Cross-frame agreement for independently supplied questions
is checked only after a comparison is accepted as `GeomEquiv`:

```text
GeomEquiv(F,G,T) := T is reversible and
                    G.equal(Tx,Ty) ↔ F.equal(x,y).
```

These comparisons compose, invert, and transport both `ResolvedIn` and `OpenIn`. The existing
NRRF627 `TransFrame.ceq_iff` supplies exactly this preservation-and-reflection law.

## Executable instance

Each D4 language uses `Y_l = Pole × B_l` and `W_l(p,b)=b`. Its closure frame therefore equates the
two pole presentations over one returned identity. The runtime checks every one of 256 ordered
occurrence pairs in both directions for every comparison.

It then classifies three concrete frame-question relations:

| Question | Admitted equality | Classification |
|---|---|---|
| returned identity | closure equality | resolved; unique quotient factor |
| literal pole | closure equality | open; equal polar pair is separated |
| literal pole | discrete equality | resolved |

All eight coherent D4 comparisons transport these classifications. The sign-erasing deformation
fails equality reflection and is not a `GeomEquiv`. Branches lacking independent contact are simply
unselected; they do not produce an openness claim.

## Equality-first comparative instance

`experiments/classical_vs_closure_asi.py` implements a stricter upstream test. It does not introduce
frame equality through `W`. Each language precommits a local axiom-geometry assumption, then an
isolated stage instantiates and audits that relation in its own terms before candidate construction:
the distinct programs `x` and `x·e` are equal exactly when their complete right-action signatures
agree. Only after a raw `T` preserves and reflects these frozen tables does the verifier derive the
quotient return and check naturality.

The resulting sequence is:

```text
assumed local equality → internal audit → raw T → GeomEquiv → explicit (T,phi,pi)
                       → quotient return/naturality → ResolvedIn/OpenIn.
```

An equality-collapse control fails reflection. A separate bijective operation twist passes
`GeomEquiv` and then fails multiplication naturality. This makes equality equivalence and
downstream translational closure observably distinct gates.

## Not the same as a topologically open set

The maze-completion experiment now defines a finite topology whose open subsets are unions of
completed-reach classes. Those `TopoOpen(U)` subsets are not the project predicate `OpenIn(F,Q)`.
A question is `OpenIn` when it varies inside one such class; its inverse images therefore fail to
be saturated. The runtime keeps both notions in separate fields and still requires an explicit
frame-equal separating witness for every `OpenIn` classification.

## Scope

The Lean bridge proves the definitions, quotient characterization and uniqueness, groupoid
operations, explicit separating-witness characterization, translation invariance, closure-return resolution, and the closure/discrete pole
example. The Python runtime exhausts the finite D4 instance. Neither layer claims that arbitrary
systems satisfy the NRRF627 frame laws or that the finite experiment establishes the full general
NRRF631 theorem independently.
