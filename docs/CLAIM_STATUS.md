# Claim Status Ledger

This ledger is the audit boundary between formal result, experiment, open theorem, and
interpretation. “PROVED” never means “suggested by the prose.” It points to a theorem or exhaustive
finite check.

| Claim | Status | Evidence or boundary |
|---|---|---|
| Translations in `TransFrame` are invertible from coherence | **PROVED** | `TransFrame.transEquiv`, `T_T`, and `phiEquiv` in the NRRF627 Lean module |
| Closure equality is preserved and reflected by translation | **PROVED** | `ceq_iff` in NRRF627 |
| `Invariant(Q) ∧ RespectsClosure(Q) ↔ MeasuredByReturn(Q)` | **PROVED** | `axiometric_verdict_characterisation` |
| Conservation through every evolutionary sequence plus closure respect is equivalent to return measurement | **PROVED** | `evolutionary_verification_is_exactly_return_measurement` |
| Return-preserving restructuring preserves admissible verdicts | **PROVED** | `capability_is_gauge`; the premise is a `Restructuring` already constrained to preserve return |
| Arbitrary real-world capability growth is gauge | **CONJECTURED / NOT ESTABLISHED** | Stronger than `capability_is_gauge`; requires an independent model of capability change |
| Coherent NRRF627 routes are endpoint-dependent | **PROVED** | `route_eq_direct`; path coherence is a `TransFrame` premise/consequence, not an empirical discovery |
| Every real learning history is path-independent | **CONJECTURED / NOT ESTABLISHED** | Must be tested on independently specified dynamics |
| A common relational carrier plus reversible presentation codecs derives the translation-and-return layer | **PROVED** | `deriveTranslationClosure`, `return_square_is_derived`, `translation_inverse_is_derived`, and `route_coherence_is_derived` |
| Adding carrier-level polar and curvature operations constructs a full `TransFrame` | **PROVED** | `deriveTransFrame` in the weaker-requirements module |
| Origin independence, recoverability, and coherent comparison force the common carrier/codecs | **CONJECTURED** | Target necessity/representation theorem; not assumed to follow from the current bridge |
| The reversal walk is classified by even/odd displacement and translates compatibly | **PROVED** | `residue_is_parity` and supporting alternating-path theorems |
| Parity is the only possible invariant in every fibre of `W` | **CONJECTURED / NOT ESTABLISHED** | NRRF627 does not classify arbitrary fibres |
| Verification return can be non-faithful | **PROVED** | `return_not_faithful` under `Separated`, with witness models |
| The D4 gate distinguishes correct, sign-erasing, and partial reference bridges | **PROVED BY EXHAUSTIVE FINITE TEST** | 8 element returns, 64 products, and `tests/test_aristotle_d4_closure.py` |
| Aristotle independently generates both D4 systems and discovers a closing bridge afterward | **EXPERIMENTAL — OPEN** | Protocol is committed; no qualifying evidence bundle exists yet |
| `IVI_W(b)` means a return is certifiable while its generating occurrence is not uniquely reconstructed | **PROVED AS A DEFINITION; EXISTENCE CONDITIONAL** | Exact fibre definition in `docs/IVI.md`; witnesses depend on non-faithfulness |
| Relation is metaphysically prior to selected language | **METAPHYSICAL INTERPRETATION** | Motivates the architecture; not a consequence of the Lean theorems |

When code or a theorem changes, update this table in the same pull request.
