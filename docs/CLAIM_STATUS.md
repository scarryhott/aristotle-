# Claim Status Ledger

This ledger is the audit boundary between formal result, experiment, open theorem, and interpretation. “PROVED” never means “suggested by the prose.” It points to a theorem or exhaustive finite check.

The project's claimed foundational novelty is **relative axiom-geometry with natural translational existence**: axioms have their role relative to their geometry/reference frame, while cross-frame identity is disclosed through natural translation and relational return rather than inherited from a privileged absolute presentation. This is the metaphysical/foundational interpretation that motivates the formal programme. Familiar categorical machinery appearing downstream is not itself claimed as the novelty.

| Claim | Status | Evidence or boundary |
|---|---|---|
| Relative axiom-geometry with natural translational existence is the proposed foundation | **METAPHYSICAL / FOUNDATIONAL INTERPRETATION** | Organizing thesis of the programme; the Lean development proves conditional consequences once the relevant frame/translation structure is specified |
| A novel axiom-geometry must be assumed conditionally in its own frame before cross-frame evaluation | **METHODOLOGICAL CONSEQUENCE OF THE FOUNDATIONAL INTERPRETATION** | Encoded experimentally by freezing each local equality frame before candidate comparison; not an unconditional theorem that every possible mathematics has such a frame |
| Translations in `TransFrame` are invertible from coherence | **PROVED** | `TransFrame.transEquiv`, `T_T`, and `phiEquiv` in NRRF627 |
| Closure equality is preserved and reflected by translation | **PROVED** | `ceq_iff` in NRRF627 |
| The commuting return square expresses natural cross-frame persistence inside `TransFrame` | **PROVED AS A FORMAL LAW; METAPHYSICAL READING IS INTERPRETIVE** | `T_ret`/return naturality in NRRF627; interpreting this as natural existence rather than covariance of pre-existing absolute objects is the foundational thesis |
| `Invariant(Q) ∧ RespectsClosure(Q) ↔ MeasuredByReturn(Q)` | **PROVED** | `axiometric_verdict_characterisation` |
| Conservation through every coherent evolutionary sequence plus closure respect is equivalent to return measurement | **PROVED** | `evolutionary_verification_is_exactly_return_measurement` |
| Return-preserving restructuring preserves admissible verdicts | **PROVED** | `capability_is_gauge`; premise already requires return preservation |
| Arbitrary real-world capability growth is gauge | **NOT ESTABLISHED** | Stronger than the theorem; requires independent modelling |
| A common relational carrier plus reversible presentation codecs derives the translation-and-return layer | **PROVED** | `deriveTranslationClosure`, `return_square_is_derived`, `translation_inverse_is_derived`, `route_coherence_is_derived` |
| Adding carrier-level polar and curvature operations constructs a full `TransFrame` | **PROVED** | `deriveTransFrame` in the weaker-requirements module |
| A runtime reference frame is exactly an admitted equality, and resolution is quotient factorization | **PROVED** | `ReferenceFrame`, `resolvedIn_iff_factors`, `factor_through_quotient_unique` in `NRRF631RuntimeFrameConditionalBridge.lean` |
| `OpenIn(F,Q)` is equivalent to an explicit frame-equal pair separated by `Q` | **PROVED** | `openIn_iff_exists_separating_pair` in the runtime bridge |
| `TransFrame` translations are axiom-geometry equivalences and transport resolution/openness | **PROVED** | `TransFrame.transGeomEquiv`, `resolution_language_independent`, `openness_language_independent` |
| Literal polar presentation can remain open while return-relational content resolves | **PROVED IN THE AVAILABLE RUNTIME BRIDGE / BROADER GENERAL RESULT REPORTED SEPARATELY** | `literalPole_open_in_closure`, `literalPole_resolved_in_discrete`; general NRRF631 source is not reconstructed in this checkout |
| Returning + grounded relational definition is uniquely closure equality | **PROVED IN NRRF633, SOURCE SUPPLIED/REPORTED OUTSIDE THIS CHECKOUT** | `unique_relational_definition`; uniqueness uses return/presentation recovery plus returning/grounded, after which translation naturality is forced |
| Naturality of the unique returning/grounded definition is forced by the translational frame | **PROVED IN NRRF633, SOURCE SUPPLIED/REPORTED OUTSIDE THIS CHECKOUT** | `naturality_is_forced`; this is downstream of the foundational translational structure, not its origin |
| Every closure form factors through a relation on returned identities, with translation-invariant identity relations giving closure forms conversely | **PROVED IN NRRF633, SOURCE SUPPLIED/REPORTED OUTSIDE THIS CHECKOUT** | `closure_form_factors`, `closureFormOf_isClosureForm`, `closure_forms_correspondence` |
| The foundational translational relation itself is derived from no prior structure whatsoever | **NOT CLAIMED AS A LEAN THEOREM** | The programme treats natural translational existence as the foundational starting interpretation; Lean formalizes conditional structures and consequences |
| A bounded D4 runtime freezes local equality frames before candidate construction | **EXPERIMENTAL CONTROL — EXECUTED** | `experiments/classical_vs_closure_asi.py`; local equality frames are independent of `W` and candidate `T` |
| Both paired verifier arms receive identical content-addressed inputs | **EXPERIMENTAL CONTROL — EXECUTED** | shared manifest and separate verifier subprocesses |
| Strong classical baseline accepts all eight ordinary D4 isomorphisms, including reversal | **EXPERIMENTAL — EXECUTED** | paired runtime evidence; prevents a straw-man comparison |
| Translational arm adds equality-transport, quotient, naturality, witnessed-openness, and next-basis certificates | **EXPERIMENTAL — EXECUTED FOR BOUNDED PROXY** | `closure_arm.json` and paired runtime receipts |
| `equality_collapse` can preserve equality but fail reflection | **EXPERIMENTAL CONTROL — EXECUTED** | separates one-way preservation from `GeomEquiv` |
| `operation_twist` can pass `GeomEquiv` but fail downstream naturality | **EXPERIMENTAL CONTROL — EXECUTED** | separates equality equivalence from full admitted translational structure |
| Pending/unselected comparisons are `OpenIn` | **REFUTED BY CURRENT FORMAL/RUNTIME SEMANTICS** | `OpenIn` requires a named frame/question and explicit separating pair; pending/non-selection is separate |
| The eight D4 isomorphisms are ambiguity internal to one fixed frame | **REFUTED BY CORRECTED RUNTIME** | all eight are coherent relative frame forms; four preserve and four reverse orientation |
| Orientation reversal breaks closure | **REFUTED BY EXHAUSTIVE FINITE TEST** | valid reversal passes equality equivalence and downstream naturality when translation data travel with it |
| Self-certification can replace independent relational contact | **REFUTED BY ADMISSION RELATION AND TEST** | no independent contact, no episode admission/token |
| Accepted returned relation supports subsequent cross-presentation execution | **EXPERIMENTAL — EXECUTED** | returned basis successfully used for subsequent execution |
| Bounded paired runtime establishes translational verification is superior to classical verification in general | **NOT CLAIMED** | only a bounded architectural/informational differential is established |
| Independently generated richer mathematical frames exhibit useful nontrivial `GeomEquiv` and natural-return relations | **EXPERIMENTAL — OPEN / FALSIFIABLE** | proposed Harmonic/Aristotle scale-up |
| Axiom-geometry operations survive substantially greater representational freedom | **EXPERIMENTAL — OPEN / FALSIFIABLE** | scale-up must preserve frozen local frames, post-hoc comparison, naturality, explicit openness witnesses and obstructions |
| `IVI_W(b)` means return can be certified without unique reconstruction of generating occurrence | **PROVED AS A DEFINITION; EXISTENCE CONDITIONAL** | exact fibre definition in `docs/IVI.md`; witnesses depend on non-faithfulness |
| Relation is metaphysically prior to isolated language selection | **METAPHYSICAL INTERPRETATION** | now sharpened by the relative axiom-geometry / natural translational existence thesis |

When code, theorem scope, or interpretation changes, update this table in the same pull request.
