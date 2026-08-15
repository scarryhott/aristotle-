# Blind D4 Contact-Form Fixture

This smaller fixture precommits one contact form between two D4 presentations. It is a scorer for a
future blind Aristotle run, not an Aristotle result and not the universal definition of closure.

## Causal order

1. Freeze `precommit_return.json`.
2. Generate representation A without B.
3. Generate representation B without A.
4. Freeze both artifacts.
5. Generate a translator without changing the contact form.
6. Evaluate all eight elements and all 64 ordered products.

The result records three independent predicates:

- `relative_equality_witnessed`: every required comparison commutes;
- `candidate_counterexample_witnessed`: at least one explicit incompatibility is returned;
- `reference_question_open`: at least one required comparison form is absent.

These predicates may coexist where appropriate. They are not values issued by closure and are not
collapsed into a static verdict enum.

## Reference controls

```bash
python3 experiments/aristotle_d4_closure.py --assert-reference
```

- `candidate_correct` witnesses the precommitted contact form;
- `adversarial_wrong_sign` produces a counterexample;
- `adversarial_partial` leaves the reference question open without a counterexample.

The full-stack experiment in `../full_stack_d4/` is the stronger runtime: it lifts all eight
operation-preserving comparisons into complete `(T,phi,pi)` relative frame forms rather than
treating noncanonical orientations as failures.
