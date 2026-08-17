# Executed Axiom-Geometry Full-Stack Run

Status: **EXPERIMENTAL RESULT — EXECUTED**.

Two separate classical mathematical-agent processes learn and execute different D4 presentations
before any cross-language comparison is constructed. This is a bounded symbolic proxy, not a claim
that a general mathematical ASI has been created.

## Process boundary and mathematical order

```text
precommitted translational operations
        ↓
isolated learner A                isolated learner B
        ↓                                ↓
frozen operation A                frozen operation B
                 \              /
              post-hoc frame comparisons (T, phi, pi)
                         ↓
          ReferenceFrame and GeomEquiv checks
                         ↓
             W, E, J, C naturality checks
                         ↓
              independently returned next basis
```

Once the presentations are frozen, the enforced mathematical ordering is

```text
closure equality ≺ ReferenceFrame ≺ GeomEquiv(T,phi,pi)
                 ≺ return/naturality ≺ ResolvedIn/OpenIn ≺ next basis.
```

The learners cannot train toward the later comparison because their artifacts are frozen and
hashed first.

## Independent learners

| Runtime | Local presentation | Training | Learned program | Held-out execution | Associativity |
|---|---|---:|---|---:|---:|
| A | square symmetries as permutations | 20 observations | `left_after_right` | 44/44 | 512/512 |
| B | local forms in `Z/4 × Z/2` | 20 observations | `direct_first_sign` | 44/44 | 512/512 |

## Axiom-geometry equivalence instead of fixed-frame ambiguity

The post-hoc constructor finds eight D4 isomorphisms. The earlier runtime treated them as eight
ambiguous candidates for one fixed coordinate identity. That was not the unified axiometry.

The corrected runtime first constructs each closure reference frame, then tests every comparison as
an axiom-geometry equivalence

```text
phi : B_B ≃ B_A
pi  : Pole ≃ Pole
T(p,b) = (pi(p), phi(b))
W_l(p,b) = b.
```

It first checks:

```text
CEq_B(x,y) ↔ CEq_A(Tx,Ty).
```

Preservation and reflection are recorded separately. Only then does it check:

```text
W_A(T y) = phi(W_B y)
T(E_B(p,b)) = E_A(pi(p),phi(b))
T(J_B y) = J_A(T y)
T(C_B y) = C_A(T y)
```

All eight structural comparisons satisfy these laws. Four preserve orientation and four reverse
it. A reversal is therefore another valid axiom-geometry equivalence, not a contradiction measured
against privileged vertex coordinates.

For each form the executable certificate checks:

- 16/16 polar occurrence return squares;
- 16/16 extension, reversal, and curvature naturality cases;
- 64/64 learned operation cases through `phi`;
- 256/256 preservation checks and 256/256 reflection checks for closure equality;
- the 16-occurrence quotient has exactly eight identity classes, each with two polar forms;
- all 256 Bool-valued closure-respecting evaluations factor uniquely through `W` in each language.

## Frame-conditional questions

The returned-identity question resolves in the closure frame and factors uniquely through the
eight-class quotient. The literal-pole question is open in that same frame: `(zero,b0)` and
`(infinity,b0)` are frame-equal but receive different question values. The identical question is
resolved in the discrete frame. All eight `GeomEquiv` comparisons transport these classifications.

This is the only use of openness in the runtime schema. A relation record always contains the frame
ID, admitted equality, question ID, and either its quotient factor or separating witness.

## Five comparison branches

| Branch | Axiom-geometry result | Basis admission |
|---|---|---:|
| `relational_contact` | one orientation-preserving `GeomEquiv` is independently selected | 1 |
| `relative_reversal` | one orientation-reversing `GeomEquiv` is independently selected | control only |
| `structural_family` | all eight coherent `GeomEquiv` forms remain; none is selected | 0 |
| `non_natural_deformation` | sign-erasing map fails bijectivity and operation naturality | 0 |
| `self_certification_only` | no independent relative contact selects a frame form | 0 |

The structural family is not an unresolved defect in fixed axioms. Each coherent comparison is
already a `GeomEquiv`; absence of independent selection is recorded as non-selection, not
`OpenIn`. Conversely, the non-natural deformation supplies an actual reflection and
operation-level counterexample.

Only the actual independently returned branch enters the next basis. Its five-step translated
execution recovers the expected result exactly. Counterfactual controls cannot issue additional
receipts, so the one-token episode bound is preserved.

The regenerated 15-record deterministic receipt chain closes at
`ad41c19059e5716e650974bdf9303cd9836bf5f4bb490bd53c8d2be7da62b415`.

## Reproduce

```bash
python3 experiments/full_stack_math_asi.py --assert-reference
python3 experiments/aristotle_d4_closure.py --assert-reference
python3 -m unittest discover -s tests -v
lake build
```

The generated evidence is under `runs/full_stack_d4/latest/`. Static audit enums and bare openness
flags are absent. Evidence records instead contain explicit `GeomEquiv` witnesses,
frame-and-question-qualified resolution/openness, or concrete counterexamples.

## Boundary

Established here: a finite learned algebra can be lifted after freeze into explicit reference
frames and `GeomEquiv` comparisons; coherent reversal remains admissible; a non-natural map is
rejected by equality-reflection and operation witnesses; and a selected equivalence can become the
next execution basis.

Not established: that arbitrary mathematical agents satisfy `TransFrame`, that these enumerative
learners approximate Aristotle's open-ended representational freedom, or that the D4 result
generalizes automatically. Those remain research questions relative to richer axiom–geometry
frames.
