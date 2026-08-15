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
             external δ_C return
                       ↓
       TRUE / FALSE / OPEN → next basis
```

The two learners run in fresh subprocesses and receive different protocol files. Each selects a
program from a local hypothesis family using its own observations, executes every learned product,
and exhaustively checks the finite group laws. Their artifacts are hashed before the translator
starts. Process separation is an experimental visibility boundary, not a security sandbox.

The translator receives the two frozen artifacts and `translator_protocol.json`; it does not
receive `precommit_return.json`. It first enumerates every structural isomorphism. D4 has multiple
automorphisms, so structure alone remains `OPEN`. A separately precommitted two-generator contact
can select one bridge. Only afterward does the external gate disclose the complete return `W` and
test all eight elements and all 64 ordered products.

## Run

```bash
python3 experiments/full_stack_math_asi.py --assert-reference
python3 -m unittest discover -s tests -v
```

The deterministic evidence bundle is written to `runs/full_stack_d4/latest/`.

## Required outcomes

| Case | Expected return | Reason |
|---|---|---|
| `relational_contact` | `TRUE` | A unique post-hoc bridge closes every withheld return |
| `structural_only` | `OPEN` | Multiple isomorphisms survive; no arbitrary origin is selected |
| `adversarial_reverse_contact` | `FALSE` | A concrete return disagreement is exposed |
| `self_certification_only` | `OPEN` | An agent claim is not independent return evidence |

Exactly one experimental token is issued, only for the independently returned `TRUE` case. The
accepted bridge becomes the next basis for a new cross-presentation execution; unresolved branches
remain recorded as `OPEN`.
