# Closure-native Level-2 external bridge run

This bounded test separates an internal gate decision from a held-out external
consequence. The consequence fixture does not receive the decision.

```text
choice / receipt
  -> Level-1 calibration
  -> held-out external consequence
  -> Level-2 audit
  -> truthful continuation | counterexample | OPEN.
```

The purpose is not to preserve a closed truth label. It is to test whether an
admitted choice remains related to an independently generated **further
relation**. A successful Level-2 result therefore supports the truth of the
relational continuation under this bounded fixture; it does not make the local
presentation, quantity, or gate verdict absolutely true.

The controls classify a perfect held-out match as `EXTERNALLY_CALIBRATED`, a
mismatch as `EXTERNAL_COUNTEREXAMPLE`, missing outcomes as
`OPEN_NO_EXTERNAL_CONSEQUENCE`, and any outcome generated from the gate verdict
as `INVALID_OUTCOME_LEAKAGE`.

This anti-leakage boundary matters to the foundational claim that true admission
must itself be related to its natural choice. The consequence cannot be created
from the admission verdict whose truth it is supposed to test.

This is an architectural test only. Its fixture does not establish real-world
genuineness, learning transfer, repayment, delivery, or proof behaviour; those
are the domains in which a future externally administered Level-2 bridge must
be specified.
