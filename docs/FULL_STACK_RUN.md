# Executed Independent Full-Stack Mathematical-Agent Run

Status: **EXPERIMENTAL RESULT — EXECUTED**.

This is the first run in this repository in which two separate classical mathematical-agent
processes each learn and execute their own representation before any translation is selected.
It is a bounded symbolic proxy for the mathematical-ASI verification problem, not evidence that a
general or superintelligent agent has been created.

## Returned closure relation

```text
precommitted return W
        ↓
isolated learning A              isolated learning B
        ↓                               ↓
64-product execution             64-product execution
        ↓                               ↓
frozen A artifact                frozen B artifact
                \               /
             post-hoc translator
                      ↓
               external return
                      ↓
        TRUE / FALSE / OPEN → next basis
```

The enforced causal order is:

```text
W_precommit ≺ (A,B)_learn+execute ≺ freeze ≺ T_posthoc ≺ δ_C
```

This ordering is the central experimental control. Neither learner receives the future bridge, and
the bridge is searched only after both learned executions have been frozen and hashed.

The precommitted return protocol has SHA-256
`911277acb381448314a58c0c1cb23f6745befc34fad5b5c1a7fc60308eb876da`.
The translator process was not given the complete return definition.

## Independent learners

| Runtime | Local presentation | Training | Selected learned program | Held-out execution | Finite proof |
|---|---|---:|---|---:|---:|
| A | square symmetries as permutations | 20 observations | `left_after_right` uniquely selected from 5 programs | 44/44 products | 512/512 associativity cases |
| B | local forms in `Z/4 × Z/2` | 20 observations | `direct_first_sign` uniquely selected from 10 programs | 44/44 products | 512/512 associativity cases |

Both agents built all eight local occurrences, selected with zero training error, executed every
unseen product with zero error, and produced identities, inverses, element orders, and exhaustive
associativity certificates. They used different data, seeds, hypothesis languages, state, and
subprocesses.

## Post-hoc translation and external return

The structural translator found eight group isomorphisms between the frozen learned algebras.
That ambiguity is preserved rather than resolved by an arbitrary origin choice. A precommitted
relative contact on two generators selected one candidate without exposing the complete `W`.
The external gate then tested the withheld relation.

Consequently the run distinguishes abstract equivalence `A ≅ B` from a bridge whose relation has
actually returned. It also distinguishes a claimed identity from a returned identity.

| Case | `δ_C` | Element returns | Product returns | Token |
|---|---:|---:|---:|---:|
| `relational_contact` | `TRUE` | 8/8 | 64/64 | 1 |
| `structural_only` | `OPEN` | 0/8 | 0/64 | 0 |
| `adversarial_reverse_contact` | `FALSE` | 8/8 checked; 4 contradictions | 64/64 | 0 |
| `self_certification_only` | `OPEN` | 0/8 | 0/64 | 0 |

The first negative witness is the learned source occurrence `b2`: its expected return is
`[1,2,3,0]`, while the reversed-contact bridge returns `[3,0,1,2]`.

Only after `TRUE` did the runtime disclose the returned identity, the common product homotopy, and
the translation-route count interpreted as holonomy data. The selected bridge then became the next
basis for a new five-step execution; its translated result was exactly recovered. The two
unresolved branches remain explicitly `OPEN`.

Exactly one experimental token was issued. The 13-record hash chain closes at
`677531103e3397a9abec950b3b0a6573973a3e4ab911dd40a34ec1d640763e0b`.

## Reproduce

```bash
python3 experiments/full_stack_math_asi.py --assert-reference
python3 -m unittest discover -s tests -v
lake build
```

The first command writes the complete deterministic evidence bundle under
`runs/full_stack_d4/latest/`. The formal build succeeds with Lean 4.33.0 and Mathlib 4.33.0 for all
three roots: the original `TransFrame` kernel, the weaker-requirements representation, and the
independent-return bridge. Their `#print axioms` audit exposes only standard Lean/Mathlib logical
foundations (`propext`, `Classical.choice`, and/or `Quot.sound` where used), with no admitted proof.

## Exact boundary

**Established by this run:** independent local learning and execution can precede translation;
frozen artifacts can be connected afterward; a precommitted external return can distinguish a
closing bridge, a concrete failure, and unresolved origin ambiguity; the accepted relation can be
used as a subsequent execution basis.

**Not established:** that arbitrary mathematical ASI evolution satisfies `TransFrame`; that the
small enumerative learners approximate Aristotle's open-ended representational power; that the
two-generator contact is necessary or sufficient on other mathematics; or that D4 closure
generalizes beyond this finite benchmark.

The next experimental closure is therefore:

```text
this executed classical proxy
        → isolated Aristotle generation
        → frozen Lean artifacts
        → translator discovered afterward
       → the same external TRUE / FALSE / OPEN gate.
```

The architecture is falsified if this separation collapses as the agents gain representational
freedom—specifically, if post-hoc translation can no longer distinguish returned equivalence from
structural ambiguity, contradiction, or self-certification.
