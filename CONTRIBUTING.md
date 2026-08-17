# Contributing

Contributions should preserve the distinction between theorem, model assumption, runtime observation, and metaphysical interpretation.

Every formal claim should identify its Lean theorem or be marked as an open research question. Runtime claims should include a reproducible receipt. Stronger interpretations must not be presented as consequences of Lean unless the theorem actually establishes them.

Before submitting a change, run:

```bash
python3 -m unittest discover -s tests -v
python3 experiments/full_stack_math_asi.py --assert-reference
python3 experiments/classical_vs_closure_asi.py --assert-reference
python3 experiments/three_part_assumption_interaction_asi.py --assert-reference
python3 experiments/generative_axiom_geometry_isolation.py --assert-reference
python3 experiments/translational_completion_maze.py --assert-reference
lake build
```

Generated evidence must preserve coherent `GeomEquiv` families, explicitly frame-qualified open
questions, non-selection controls, and concrete counterexamples; do not retain only the admitted actual branch. Any change to a
precommitted relational protocol creates a new benchmark version.

Comparative changes must keep both verifier arms on the same content-addressed inputs. Precommit
each local axiom-geometry assumption and every total question before learning or constructing
cross-frame candidates. A local evaluator may audit or reject the declared geometry but may not
replace it after seeing another frame. Every closure candidate, question relation, and next-basis
record must preserve explicit assumption and `(T,phi,pi)` lineage. The fixed-frame arm must remain
a strong ordinary isomorphism baseline; the discrete frame is only a frame-relativity control.
Never optimize the number of `OpenIn` results or convert pending data, structural non-selection, or
self-certification into openness.

External-interaction changes must register separate geometry and candidate packets before Parts 1
and 2 freeze, give the local evaluator only its geometry declaration, and retain every isolation ID. Call a
transition `GeomEquiv` only when it is a bijection preserving and reflecting equality. Type split
extensions and quotients separately, require total relational coverage and composite agreement,
and never silently discard an external residue. “Continuous” means finite compositional lineage
unless a topology and continuity law are explicitly added.

Maze-completion changes must freeze local equality before the line set, derive raw reach without
symmetrizing it, retain an explicit reverse path or missing-return witness, and check exact
agreement between completed reach and the frozen equality before constructing the intended
quotient. `TopoOpen(U)` and project `OpenIn(F,Q)` are different notions. The topology currently
registered by the maze assay is specifically the finite saturation topology on occurrences; new
topologies require a new versioned protocol and controls.
