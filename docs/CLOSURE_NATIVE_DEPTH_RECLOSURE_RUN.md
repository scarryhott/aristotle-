# Closure-native depth reclosure

This bounded control re-closes verification around a frozen ordered question
stream.  A result at one depth is not promoted to a result at a later depth:

```text
TruthEq at Q_0..Q_n  does not imply  TruthEq at Q_0..Q_(n+1).
```

The control registers aggregate and magnitude questions before evaluation, then
adds a phase question in a distinct, frozen stream.  Two forms agree through
the invariant stream but separate only when phase is in scope.  A translation
control remains equal through its invariant stream.  Missing contact bridge is
`OPEN_BRIDGE_BOUNDARY`, and a post-hoc question extension is invalid.

Run with:

```sh
python3 -m experiments.closure_native_depth_reclosure
python3 -m unittest tests.test_closure_native_depth_reclosure -v
```

This is a native finite control, not a local rebuild of NRRF668 or evidence
about physics, quantum gravity, Chaitin/Kakeya, Kolmogorov complexity, or the
frontier Aristotle bridge.
