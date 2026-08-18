# Closure-native Level-2 external bridge run

This bounded test separates an internal gate decision from a held-out external
consequence. The consequence fixture does not receive the decision.

```text
receipt -> Level-1 audit -> held-out external consequence -> Level-2 audit
```

The controls classify a perfect held-out match as `EXTERNALLY_CALIBRATED`, a
mismatch as `EXTERNAL_COUNTEREXAMPLE`, missing outcomes as
`OPEN_NO_EXTERNAL_CONSEQUENCE`, and any outcome generated from the gate verdict
as `INVALID_OUTCOME_LEAKAGE`.

This is an architectural test only. Its fixture does not establish real-world
genuineness, learning transfer, repayment, delivery, or proof behaviour; those
are the domains in which a future externally administered Level-2 bridge must
be specified.
