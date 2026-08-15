# Contributing

Contributions should preserve the distinction between theorem, model assumption, runtime observation, and metaphysical interpretation.

Every formal claim should identify its Lean theorem or be labeled OPEN. Runtime claims should include a reproducible receipt. Stronger interpretations must not be presented as consequences of Lean unless the theorem actually establishes them.

Before submitting a change, run:

```bash
python3 -m unittest discover -s tests -v
python3 experiments/full_stack_math_asi.py --assert-reference
lake build
```

Generated evidence must preserve `FALSE` and `OPEN` branches; do not keep only a run that returns
`TRUE`. Any change to a precommitted return protocol creates a new benchmark version.
