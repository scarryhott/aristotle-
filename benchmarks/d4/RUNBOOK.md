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

The result records three independent comparison predicates:

- `geom_equiv_candidate_holds`: the comparison is total and every required comparison commutes;
- `candidate_counterexample_witnessed`: at least one explicit incompatibility is returned;
- `comparison_total`: every required comparison value exists.

An undefined comparison is retained as pending verification. It is not called open: `OpenIn` is
reserved for a total question that separates two occurrences equated by one named frame.

## Reference controls

```bash
python3 experiments/aristotle_d4_closure.py --assert-reference
```

- `candidate_correct` witnesses the precommitted contact form;
- `adversarial_wrong_sign` produces a counterexample;
- `adversarial_partial` is explicitly not a total frame comparison and has no counterexample.

The full-stack experiment in `../full_stack_d4/` is the stronger runtime: it lifts all eight
operation-preserving comparisons into complete `(T,phi,pi)` axiom-geometry equivalences rather than
treating noncanonical orientations as failures.
