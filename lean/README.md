# Formal kernel

The canonical formal artifact for this project is:

`NRRF627ClosureTranslationalFrameworkAxiometryASIEvolutionaryVerification.lean`

It is the self-contained Lean/Mathlib module establishing the `TransFrame` closure, axiometry, ASI-gauge, evolutionary-verification, parity-residue, and non-vacuity results described in the repository documentation.

The exact source artifact is carried here and is a registered build root in `lakefile.toml`.

`NRRF627WeakRequirementsRepresentation.lean` imports that kernel and proves the current
representation bridge. It constructs the translation/return layer from a common relational carrier
and reversible presentation codecs, then shows how explicit carrier-level `J` and `C` operations
construct the full `TransFrame`.

`NRRF627IndependentReturnBridge.lean` formalizes frame-relative equality forms, witness-based
one-token admission, self-certification separation, and the construction of a `TransFrame` from a
canonical independent return plus reversible temporary-presentation codecs. It has no static audit
enum: a selected comparison is the relational form `(T,phi)` with its commuting return square, and
the full runtime checks `(W,E,T,phi,pi,J,C)` together.

`NRRF631RuntimeFrameConditionalBridge.lean` makes the executable frame boundary explicit:
`ReferenceFrame` is admitted equality, `ResolvedIn` is quotient factorization, and `GeomEquiv`
preserves and reflects equality. `openIn_iff_exists_separating_pair` proves that every `OpenIn`
claim is equivalent to explicit data `x ~ y` with unequal question values.
`assumeAxiomGeometry` installs a supplied `Setoid` as the exact local evaluation frame without
adding an axiom; `resolvedIn_assumed_geometry_iff` confirms that no external equality is
substituted. Cross-frame transport still requires a later `GeomEquiv`.

`NRRF768RelativeTranslationalTruthNaturalFormSelector.lean` supplies the missing selector layer.
It derives the quotient completion and equality-saturation topology from `CEq`, proves that return
equality is exactly topological indistinguishability, and proves the completion maps and derived
topologies translate coherently. A natural form is a supplied translation-natural section with an
exact idempotent hold. Pointwise authored seeds show origin cancellation and genuine polar freedom;
proof-relevant form movements compose and contextual loop steps must carry one. No
`Classical.choice` is used; the trading bridge still requires an actual interaction and completion
witness and contains no profit selector.

`NRRF779ReportedSelectorTradingReintegration.lean` exposes the exact conditional boundary needed
to connect the reported NRRF777/778 live fill and continuum-halting selector to the local trading
chain. A nonzero optional receipt realization prevents missing data from collapsing into the
reported zero exception. An explicit `formReading` commuting square converts substrate transport
into an NRRF764 network interaction, after which the existing NRRF768 selected-form witness and
NRRF766 local witness are reused. The external NRRF777/778 sources are not in this checkout, so the
three translation certificates remain named obligations. Even when supplied, NRRF767 still
requires authenticated fill evidence and exact witnessed status; settlement and profit are not
derived.

`NRRF780LocalPriceGlobalCostEquality.lean` corrects the price/cost layer. A price is an arbitrary
local presentation; cost is the global returned equality to which that presentation completes.
Entry and exit are assessed only after the same completion interface, and positivity remains an
additional empirical predicate. The optional commutative-group realization proves
`local / (local / completed) = completed`, so refactoring a previously observed cost-completed
result into the new equality cannot alter it.

`NRRF781SocioeconomicTokenomicTradingSupernet.lean` makes the network, reported live
filled/selected/halting form, substrate interaction, local entry/exit prices, global cost
equalities, token reading, continual local witness, and completed assessment aspects of one
occurrence. Its joining law is
`tokenRead (complete price) = closureReturn (priceRead price)`, from which the same selected
interaction derives equality of the entry and exit token readings. Authentication and positivity
remain evidence aspects rather than definitions of closure.

Build all registered modules with the pinned toolchain:

```bash
lake build
```

The executable full-stack and paired-comparison D4 runs are finite Python evidence rather than Lean
theorems that learning occurred. Lean establishes the conditional framework; the frozen runtime
artifacts establish what the independent classical proxies actually selected and executed.

NRRF599 and NRRF633–640 are external formal references, not build roots in this
checkout. Their reported theorem names and source status are recorded in
`docs/EXTERNAL_LEAN_REFERENCES.md`. They must be imported with their exact
dependencies and rebuilt before any runtime-to-NRRF639/640 bridge is labelled
locally machine-checked.
