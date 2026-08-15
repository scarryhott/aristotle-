# IVI: Intangibly Verified Information

IVI is the proposed bridge between closure metaphysics and operational verification.

## Core idea

Information is not made verified merely by being asserted, measured once, or reproduced syntactically. Verification is an **admissibility boundary on relations**: some transformations return coherently to the maintained basis and others do not.

IVI is therefore information whose identity is recoverable through the closure relation even when its presentation changes.

In the current formal kernel, the closest exact object is the verification return `W` together with closure equality:

`CEq W u v := W u = W v`.

A verdict that is language-independent and closure-respecting is characterized as a measurement of this return.

## Potential gate

The broader IVI program treats verification as a potential gate rather than a claim of omniscience. A runtime should admit three outcomes:

- `PROVED`: the return closes under the stated admissibility conditions;
- `FALSE_WITH_COUNTEREXAMPLE`: an explicit transformation breaks the proposed closure;
- `OPEN_WITH_MINIMAL_OBSTRUCTION`: the available relation does not yet close and the obstruction is identified.

This prevents `OPEN` from being silently converted into either truth or falsity.

## Why IVI matters to ASI

A mathematical ASI may produce an occurrence humans cannot reconstruct while still preserving a verifiable relational identity. `return_not_faithful` deliberately permits this separation. Verification therefore need not mean complete recovery of the ASI's internal occurrence.

The research challenge is to determine which returns are genuinely independent constraints rather than definitions engineered to survive the transformations being tested.