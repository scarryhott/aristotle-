# Independent Full-Stack Mathematical-Agent Run

Status: **EXECUTABLE EXPERIMENT**. This is a classical symbolic mathematical-agent proxy, not a
claim that a generally superintelligent system has been instantiated.

## Causal closure relation

```text
precommitted W
      ↓
isolated learner A        isolated learner B
      ↓                         ↓
learn → execute           learn → execute
      ↓                         ↓
frozen artifact A         frozen artifact B
             \             /
          post-hoc structural translator
                       ↓
        compare the withheld W-square
                       ↓
       external ReturnAudit record → next basis
```

The two learners run in fresh subprocesses and receive different protocol files. Each selects a
program from a local hypothesis family using its own observations, executes every learned product,
and exhaustively checks the finite group laws. Their artifacts are hashed before the translator
starts. Process separation is an experimental visibility boundary, not a security sandbox.

The translator receives the two frozen artifacts and `translator_protocol.json`; it does not
receive `precommit_return.json`. It first enumerates every structural isomorphism. D4 has multiple
automorphisms, so structure alone remains `UNRESOLVED`. A separately precommitted two-generator contact
can select one bridge. Only afterward does the external auditor disclose the complete return `W`
and test all eight elements and all 64 ordered products. `W` returns the relational basis;
`ReturnAudit` only records the evidence state of the proposed bridge.

## Run

```bash
python3 experiments/full_stack_math_asi.py --assert-reference
python3 -m unittest discover -s tests -v
```

The deterministic evidence bundle is written to `runs/full_stack_d4/latest/`.

## Required outcomes

| Case | Expected return | Reason |
|---|---|---|
| `relational_contact` | `RETURNED` | A unique post-hoc bridge closes every withheld return |
| `structural_only` | `UNRESOLVED` | Multiple isomorphisms survive; no arbitrary origin is selected |
| `adversarial_reverse_contact` | `CONTRADICTED` | A concrete return disagreement is exposed |
| `self_certification_only` | `UNRESOLVED` | An agent claim is not independent return evidence |

Exactly one experimental token is issued only when the relation is independently returned. The
accepted bridge becomes the next basis for a new cross-presentation execution; unresolved branches
remain recorded as `UNRESOLVED`.
