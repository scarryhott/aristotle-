# Contributing

Contributions should preserve the distinction between theorem, model assumption, runtime observation, and metaphysical interpretation.

Every formal claim should identify its Lean theorem or be marked as an open research question. Runtime claims should include a reproducible receipt. Stronger interpretations must not be presented as consequences of Lean unless the theorem actually establishes them.

Before submitting a change, run:

```bash
python3 -m unittest discover -s tests -v
python3 experiments/full_stack_math_asi.py --assert-reference
python3 experiments/classical_vs_closure_asi.py --assert-reference
lake build
```

Generated evidence must preserve coherent `GeomEquiv` families, explicitly frame-qualified open
questions, non-selection controls, and concrete counterexamples; do not retain only the admitted actual branch. Any change to a
precommitted relational protocol creates a new benchmark version.

Comparative changes must keep both verifier arms on the same content-addressed inputs. Freeze each
local equality geometry and every total question before constructing cross-frame candidates. The
fixed-frame arm must remain a strong ordinary isomorphism baseline; the discrete frame is only a
frame-relativity control. Never optimize the number of `OpenIn` results or convert pending data,
structural non-selection, or self-certification into openness.
