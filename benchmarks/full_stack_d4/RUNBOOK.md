# Full-Stack D4 Axiom-Geometry Runbook

## Causal protocol

The execution processes first learn and freeze their local presentations. The mathematical runtime
then begins in this order:

```text
closure equality → ReferenceFrame → GeomEquiv(T,phi,pi)
                 → return/naturality → ResolvedIn/OpenIn → next basis.
```

The translator receives the two frozen learned algebras and the contact protocol. It does not
receive the verifier's completed frame certificates. The verifier then constructs the occurrence
fibres `Pole × B_l` and checks every operation.

## Axiom-geometry equivalences

D4 has eight operation-preserving comparisons between the learned presentations. They are not
treated as eight mistaken candidates for a fixed identity. Each becomes an admissible
axiom-geometry equivalence when equipped with its induced identity translation `phi` and orientation translation
`pi`:

```text
W_l(p,b)=b
T(p,b)=(pi(p),phi(b)).
```

Before those operations are inspected, every coherent comparison must preserve and reflect the
closure equality over all 256 occurrence pairs. The return, extension, reversal, curvature, and
operation relations are checked only after `GeomEquiv`. The quotient of the 16 polar occurrences
by the frame equality must recover the eight-element learned basis.

The runtime then evaluates total questions. `returned_identity` resolves in the closure frame and
factors uniquely through its quotient. `literal_pole_presentation` is open in that same frame with
an explicit equal-occurrence separating pair, yet resolves in the discrete frame. Thus openness is
always recorded with both a frame ID and a question ID.

## Branches

| Branch | Required relation |
|---|---|
| `relational_contact` | selects one preserving form; actual basis-admission branch |
| `relative_reversal` | selects one reversing form; must still satisfy closure |
| `structural_family` | retains all eight GeomEquiv forms; no independent contact selects one |
| `non_natural_deformation` | sign-erasing map must expose an operation-level counterexample |
| `self_certification_only` | supplies no independent contact and cannot admit a basis |

Only the actual branch can issue the episode receipt. Controls are counterfactual and therefore do
not multiply tokens even when, as with relative reversal, they exhibit a valid equality form.

## Commands

```bash
python3 experiments/full_stack_math_asi.py --assert-reference
python3 -m unittest discover -s tests -v
```

The command regenerates `runs/full_stack_d4/latest/`. The expected schema contains neither a global
audit nor a bare openness flag. Every `open_in_frame` value occurs inside a record containing the
corresponding `frame_id`, `frame_equality`, `question_id`, and separating witness.
