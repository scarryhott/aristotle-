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
| An inhabited independent relative-equality witness issues at most one token and a self-claim alone issues none | **PROVED** | `IndependentlyReturned`, `episode_tokens_le_one`, and `self_certification_no_token` in `NRRF627IndependentReturnBridge.lean` |
| A canonical independent return plus reversible temporary-presentation codecs constructs the NRRF627 frame | **PROVED** | `derivedFrame`, `return_square_is_derived`, and `temporary_presentation_cancels` |
| A runtime reference frame is exactly an admitted equality, and resolution is equivalent to factorization through its quotient | **PROVED** | `ReferenceFrame`, `resolvedIn_iff_factors`, and `factor_through_quotient_unique` in `NRRF631RuntimeFrameConditionalBridge.lean` |
| `TransFrame` translations are axiom-geometry equivalences and transport resolution and openness | **PROVED** | `TransFrame.transGeomEquiv`, `resolution_language_independent`, and `openness_language_independent` in the runtime bridge |
| The literal-pole question can be open in a closure frame and resolved in the discrete frame | **PROVED** | `literalPole_open_in_closure` and `literalPole_resolved_in_discrete` |
| Origin independence, recoverability, and coherent comparison force the common carrier/codecs | **CONJECTURED** | Target necessity/representation theorem; not assumed to follow from the current bridge |
| The reversal walk is classified by even/odd displacement and translates compatibly | **PROVED** | `residue_is_parity` and supporting alternating-path theorems |
| Parity is the only possible invariant in every fibre of `W` | **CONJECTURED / NOT ESTABLISHED** | NRRF627 does not classify arbitrary fibres |
| Verification return can be non-faithful | **PROVED** | `return_not_faithful` under `Separated`, with witness models |
| The blind D4 fixture distinguishes a total `GeomEquiv` candidate, a counterexample, and an incomplete comparison without calling incompleteness `OpenIn` | **PROVED BY EXHAUSTIVE FINITE TEST** | 8 element returns, 64 products, and `tests/test_aristotle_d4_closure.py` |
| Aristotle independently generates both D4 systems and discovers a closing bridge afterward | **EXPERIMENTAL — OPEN** | Protocol is committed; no qualifying Aristotle evidence bundle exists yet |
| Two separate classical mathematical-agent processes each learn and exhaustively execute a D4 presentation before translation | **EXPERIMENTAL — EXECUTED** | `experiments/full_stack_math_asi.py`; frozen A/B artifacts; 20 independent observations and 44/44 held-out products per learner |
| A `GeomEquiv` constructed after artifact freeze realizes the subsequent translational operations | **EXPERIMENTAL — EXECUTED FOR THE CLASSICAL PROXY** | Main run: 256 preservation plus 256 reflection checks first; then 16/16 `T_ret`, `T_ext`, `T_J`, and `T_C`; 64/64 operation cases |
| The D4 mathematical runtime enforces `frame equality ≺ GeomEquiv ≺ naturality ≺ ResolvedIn/OpenIn ≺ next basis` | **EXPERIMENTAL CONTROL — EXECUTED** | Separate learner subprocesses, frozen hashes, post-hoc frame comparison, independent verifier, and deterministic receipts |
| The eight D4 isomorphisms are internal ambiguity in one fixed frame | **REFUTED BY THE CORRECTED RUNTIME MODEL** | Each isomorphism extends to a coherent `GeomEquiv`; all eight preserve and reflect the frame equality and satisfy downstream operations |
| Orientation reversal breaks closure | **REFUTED BY EXHAUSTIVE FINITE TEST** | The reversed form has nontrivial `pi` and passes all `W,E,T,phi,pi,J,C` and relative-equality checks |
| A non-natural sign-erasing deformation is admissible translation | **REFUTED BY EXHAUSTIVE FINITE TEST** | It fails bijectivity and learned-operation naturality with an explicit counterexample |
| Self-certification can replace independent relational return | **REFUTED BY ADMISSION RELATION AND TEST** | `self_certification_only` selects no `GeomEquiv` and issues no token |
| The accepted returned relation supports a subsequent cross-presentation execution | **EXPERIMENTAL — EXECUTED** | `returned_basis.json`; observed and expected target results both `a6` |
| The classical proxy is an actual mathematical ASI or an Aristotle result | **NOT CLAIMED** | It is a bounded symbolic learning/execution runtime; the isolated Aristotle question remains open |
| Axiom-geometry operations will survive substantially greater representational freedom | **EXPERIMENTAL — OPEN / FALSIFIABLE** | Scale-up must preserve freeze, post-hoc `GeomEquiv`, operation naturality, frame-qualified questions, and explicit counterexamples |
| `IVI_W(b)` means a return is certifiable while its generating occurrence is not uniquely reconstructed | **PROVED AS A DEFINITION; EXISTENCE CONDITIONAL** | Exact fibre definition in `docs/IVI.md`; witnesses depend on non-faithfulness |
| Relation is metaphysically prior to selected language | **METAPHYSICAL INTERPRETATION** | Motivates the architecture; not a consequence of the Lean theorems |

When code or a theorem changes, update this table in the same pull request.
