# IVI: Intangibly Verified Information

## Mathematical definition

Let `W : X → B` be a verification return and define its fibre at `b : B` by

`Fibre_W(b) := {u : X | W(u) = b}`.

Define the non-faithful IVI condition

`IVI_W(b) :≡ ∃ u v, u ≠ v ∧ W(u) = b ∧ W(v) = b`.

Equivalently, the verifier can certify the returned relation `b` while `W` does not uniquely
reconstruct which occurrence generated it.

**PROVED (conditional):** NRRF627's `return_not_faithful` supplies distinct closure-equal
occurrences under its `Separated` condition, and its witness models show consistency. The
axiometric characterization proves that every invariant, closure-respecting verdict factors
through the return.

**NOT PROVED:** every return is non-faithful, every real ASI state has IVI, or all information lost
inside a fibre is parity. The parity theorem classifies one reversal-generated walk, not arbitrary
fibres.

## Why “intangible” has a technical role

The intangible component is not an unmeasured mystical object. It is the distinction between:

- possession of a certified return `b`; and
- faithful reconstruction of a unique generating occurrence `u`.

When `IVI_W(b)` holds, the first is possible while the second is mathematically underdetermined.
This gives IVI a verification role without making it an extra physical or metaphysical theorem.

## Three-valued potential gate

**EXPERIMENTAL PROTOCOL:** a candidate relation is evaluated as:

- `TRUE` when every required independent return closes;
- `FALSE` when an explicit counterexample breaks closure;
- `OPEN` when no contradiction is known but the return is incomplete or unavailable.

Contradiction takes precedence over incompleteness. `OPEN` is not silently promoted to truth, and a
model's self-certification produces no token.

## Interpretation boundary

**METAPHYSICAL INTERPRETATION:** IVI may be read as identity grounded in recoverable relation rather
than in a privileged local presentation. The Lean theorems support the non-faithful return
structure; they do not prove that this interpretation exhausts mathematical or physical reality.
