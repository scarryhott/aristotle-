# Runtime Reunification: Axiom Geometry Before Verdict

The full-stack runtime is a finite operational realization of the translational consequences
described by NRRF630 and the frame-conditional reading described by NRRF631. It does not define
closure from one canonical D4 coordinate system. The general NRRF631 source is not copied into
this repository; `NRRF631RuntimeFrameConditionalBridge.lean` proves the interface used here from
the existing NRRF627 `TransFrame`.

## Mathematical runtime order

The mathematics begins at the equality admitted by each axiom geometry:

```text
closure equality
    → ReferenceFrame
    → GeomEquiv (preserve and reflect equality)
    → return and operation naturality
    → ResolvedIn(frame, question) or OpenIn(frame, question)
    → next basis.
```

After the learners freeze their bases, the occurrence carrier and frame equality are

```text
Y_l = Pole × B_l
W_l(p,b)=b
(p,b) ≈_l (q,c)  iff  W_l(p,b)=W_l(q,c)  iff  b=c.
```

A coherent comparison supplies

```text
phi : B_B ≃ B_A
pi  : Pole ≃ Pole
T   : Pole × B_B ≃ Pole × B_A
T(p,b) = (pi(p),phi(b)).
```

It is accepted first as `GeomEquiv` only if

```text
x ≈_B y  ↔  T(x) ≈_A T(y).
```

The runtime checks preservation and reflection separately over all 256 pairs. Return, extension,
reversal, curvature, and multiplication naturality are downstream obligations, not the source of
the frame definition.

## Frame-conditional questions

A total question `Q : Y_l → Ω` is resolved in a frame exactly when it cannot separate occurrences
that frame equates. In the finite runtime this is checked by constructing the unique factor through
the equality quotient. `OpenIn` is its negation and is witnessed by two frame-equal occurrences
with different question values.

No output contains an unqualified `reference_question_open` flag. Each question relation contains:

- the frame ID and admitted equality;
- the question ID;
- `resolved_in_frame` and `open_in_frame` as complementary relational results;
- either a unique quotient-factorization certificate or a concrete separating pair.

The executed controls make the relativity explicit:

| Question | Frame | Result |
|---|---|---|
| returned identity | closure frame | resolved; unique factor through `W` |
| literal pole presentation | closure frame | open; `(zero,b)` and `(infinity,b)` are frame-equal but separated |
| literal pole presentation | discrete frame | resolved |

Every one of the eight D4 `GeomEquiv` comparisons transports these classifications. Four preserve
orientation and four reverse it. Reversal is therefore another axiom-geometry equivalence, not a
contradiction measured against privileged coordinates.

## NRRF630/631-to-runtime map

| Formal result | Executable realization |
|---|---|
| `retNat` | 16 exhaustive instances of `W_A(Ty)=phi(W_B y)` per comparison |
| `revNat`, `curvNat` | 16 reversal and curvature naturality instances each |
| `quotBasisEquiv` | 16 polar occurrences quotient to eight returned basis classes |
| `quotBasisEquiv_natural` | equality preservation and reflection across all 256 pairs |
| universal factorization | all 256 Bool-valued closure-respecting evaluations factor uniquely through `W` |
| `GeomEquiv` | reversible `T` plus explicit preservation and reflection of frame equality |
| `resolvedIn_iff_factors` | finite question factor and uniqueness certificate |
| `openIn_iff_exists_separating_pair` | every runtime `OpenIn` record contains an explicit equal-pair witness |
| `resolvedIn_transport`, `openIn_transport` | all coherent comparisons preserve question classification |
| `openness_is_frame_relative` | one literal-pole question is open in closure equality and resolved in discrete equality |

The Bool enumeration is the complete finite instance for `Ω = Bool`. The general
codomain-independent universal property remains a Lean theorem, not a claim inferred from that
enumeration.

## Selection is not openness

The `structural_family` and `self_certification_only` branches select no comparison by independent
contact. That is recorded as non-selection, not as `OpenIn`: there is no total occurrence question
being classified there. The sign-erasing deformation is rejected because it fails equality
reflection, bijectivity, and multiplication naturality, with concrete counterexamples.

A basis receipt exists only when the actual episode contains an independently selected `GeomEquiv`
whose downstream operations commute. A self-claim is not such a witness, and counterfactual valid
comparisons issue no additional token.

## Further equality-first comparison

The first full-stack run uses the NRRF627 return fibre as its closure equality. The paired runtime
in `classical_vs_closure_asi.py` tests the stronger architectural order directly: it freezes each
language's operational equality matrix without `W` or a candidate comparison, then derives the
quotient return after `GeomEquiv`. Its fixed-frame arm recognizes all ordinary isomorphisms; the
closure differential is the additional frame transport, factorization, witness, and next-basis
evidence. See [`CLASSICAL_VS_CLOSURE_RUN.md`](CLASSICAL_VS_CLOSURE_RUN.md).
