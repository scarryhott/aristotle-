# Full-Stack D4 Relative-Equality Runbook

## Causal protocol

```text
(W,E,J,C) precommitted
       → two isolated learn-and-execute processes
       → frozen artifacts and hashes
       → post-hoc frame forms (T,phi,pi)
       → exhaustive relative-equality operations
       → one independently returned next basis.
```

The translator receives the two frozen learned algebras and the contact protocol. It does not
receive the verifier's completed frame certificates. The verifier then constructs the occurrence
fibres `Pole × B_l` and checks every operation.

## Frame forms

D4 has eight operation-preserving comparisons between the learned presentations. They are not
treated as eight mistaken candidates for a fixed identity. Each becomes an admissible relative
frame form when equipped with its induced identity translation `phi` and orientation translation
`pi`:

```text
W_l(p,b)=b
T(p,b)=(pi(p),phi(b)).
```

Every coherent form must satisfy the return, extension, reversal, curvature, operation, and
closure-equality naturality relations. The quotient of the 16 polar occurrences by relative
equality must recover the eight-element learned basis.

## Branches

| Branch | Required relation |
|---|---|
| `relational_contact` | selects one preserving form; actual basis-admission branch |
| `relative_reversal` | selects one reversing form; must still satisfy closure |
| `structural_family` | retains all eight forms and leaves only the reference selection open |
| `non_natural_deformation` | sign-erasing map must expose an operation-level counterexample |
| `self_certification_only` | supplies no independent contact and cannot admit a basis |

Only the actual branch can issue the episode receipt. Controls are counterfactual and therefore do
not multiply tokens even when, as with relative reversal, they exhibit a valid equality form.

## Commands

```bash
python3 experiments/full_stack_math_asi.py --assert-reference
python3 -m unittest discover -s tests -v
```

The command regenerates `runs/full_stack_d4/latest/`. The expected schema contains no global
three-valued audit. It records relational witnesses, frame-relative openness, and concrete
counterexamples as separate predicates with their operation-level evidence.
