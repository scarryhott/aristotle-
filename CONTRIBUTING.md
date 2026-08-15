# Contributing

Preserve the distinction between theorem, assumption, runtime observation, and interpretation.

Use exactly one primary label for every major claim:

- **PROVED** — cite a checked Lean theorem or an exhaustive finite test;
- **CONJECTURED** — state a precise unproved mathematical target;
- **EXPERIMENTAL** — link the frozen protocol, complete receipt, and outcome;
- **METAPHYSICAL INTERPRETATION** — do not present it as a Lean consequence.

For formal contributions, include the theorem name, pinned toolchain, successful build output, and
`#print axioms` where relevant. `sorry`, `admit`, new axioms, and unreported source edits invalidate
a PROVED label.

For experiments, preserve exact prompts, inputs, outputs, hashes, model/tool versions, retries,
counterexamples, and OPEN cases. A self-certifying model statement is not independent evidence.
Never redefine the return after inspecting a failed transformation without creating a new,
explicitly versioned experiment.

Update `docs/CLAIM_STATUS.md` whenever a contribution changes a claim's status or boundary.
