# Executed Relative-Equality Full-Stack Run

Status: **EXPERIMENTAL RESULT — EXECUTED**.

Two separate classical mathematical-agent processes learn and execute different D4 presentations
before any cross-language comparison is constructed. This is a bounded symbolic proxy, not a claim
that a general mathematical ASI has been created.

## Causal closure

```text
precommitted translational operations
        ↓
isolated learner A                isolated learner B
        ↓                                ↓
frozen operation A                frozen operation B
                 \              /
              post-hoc frame forms (T, phi, pi)
                         ↓
          W, E, J, C and relative-equality checks
                         ↓
              independently returned next basis
```

The enforced ordering is

```text
(W,E,J,C)_precommit ≺ (A,B)_learn+execute ≺ freeze
                    ≺ (T,phi,pi)_posthoc ≺ relative equality ≺ next basis.
```

The learners cannot train toward the later comparison because their artifacts are frozen and
hashed first.

## Independent learners

| Runtime | Local presentation | Training | Learned program | Held-out execution | Associativity |
|---|---|---:|---|---:|---:|
| A | square symmetries as permutations | 20 observations | `left_after_right` | 44/44 | 512/512 |
| B | local forms in `Z/4 × Z/2` | 20 observations | `direct_first_sign` | 44/44 | 512/512 |

## Relative equality instead of fixed-frame ambiguity

The post-hoc constructor finds eight D4 isomorphisms. The earlier runtime treated them as eight
ambiguous candidates for one fixed coordinate identity. That was not the unified axiometry.

The corrected runtime constructs, for every comparison, the whole relative frame form

```text
phi : B_B ≃ B_A
pi  : Pole ≃ Pole
T(p,b) = (pi(p), phi(b))
W_l(p,b) = b.
```

It then checks:

```text
W_A(T y) = phi(W_B y)
T(E_B(p,b)) = E_A(pi(p),phi(b))
T(J_B y) = J_A(T y)
T(C_B y) = C_A(T y)
CEq_B(x,y) ↔ CEq_A(Tx,Ty).
```

All eight structural comparisons satisfy these laws. Four preserve orientation and four reverse
it. A reversal is therefore another valid relative equality form, not a contradiction measured
against privileged vertex coordinates.

For each form the executable certificate checks:

- 16/16 polar occurrence return squares;
- 16/16 extension, reversal, and curvature naturality cases;
- 64/64 learned operation cases through `phi`;
- 256/256 preservation-and-reflection comparisons for closure equality;
- the 16-occurrence quotient has exactly eight identity classes, each with two polar forms;
- all 256 Bool-valued closure-respecting evaluations factor uniquely through `W` in each language.

## Five frame-relative branches

| Branch | Relative result | Basis admission |
|---|---|---:|
| `relational_contact` | one orientation-preserving frame form is independently returned | 1 |
| `relative_reversal` | one orientation-reversing frame form is independently returned | control only |
| `structural_family` | all eight coherent frame forms remain relative; reference selection stays open | 0 |
| `non_natural_deformation` | sign-erasing map fails bijectivity and operation naturality | 0 |
| `self_certification_only` | no independent relative contact selects a frame form | 0 |

The structural family is not an unresolved defect in fixed axioms. Relative equality is already
realized by each coherent form; only the question of which form is selected by this contact remains
open relative to the frame. Conversely, the non-natural deformation supplies an actual
outside-closure witness.

Only the actual independently returned branch enters the next basis. Its five-step translated
execution recovers the expected result exactly. Counterfactual controls cannot issue additional
receipts, so the one-token episode bound is preserved.

The regenerated 15-record deterministic receipt chain closes at
`6c4d3c9da08779423ce8576387cc083f3aed68e14b3036bb591a517e4703a6e8`.

## Reproduce

```bash
python3 experiments/full_stack_math_asi.py --assert-reference
python3 experiments/aristotle_d4_closure.py --assert-reference
python3 -m unittest discover -s tests -v
lake build
```

The generated evidence is under `runs/full_stack_d4/latest/`. Static audit enums are absent from
the schema. Evidence records instead contain explicit relative-equality witnesses, open
frame-relative questions, or concrete counterexamples.

## Boundary

Established here: a finite learned algebra can be lifted after freeze into explicit translational
closure operations; coherent reversal remains relative equality; a non-natural map is rejected by
operation-level witnesses; and a returned equality form can become the next execution basis.

Not established: that arbitrary mathematical agents satisfy `TransFrame`, that these enumerative
learners approximate Aristotle's open-ended representational freedom, or that the D4 result
generalizes automatically. Those remain research questions relative to richer axiom–geometry
frames.
