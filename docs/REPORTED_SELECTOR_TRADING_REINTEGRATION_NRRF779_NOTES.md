# NRRF779 — Reported selector trading reintegration

NRRF779 reconnects the reported NRRF777/778 live natural-form selector to the
locally checked trading chain without collapsing distinct meanings into one
word “closure.” Its formal path is:

```text
live receipt
  → optional nonzero complex datum
  → compatible rigid translation event
  → filled relation form
  → explicit formReading
  → substrate operation / network interaction commuting square
  → NRRF768 selected trading-form witness
  → NRRF766 local continual witness
  → [separate authentication + exact status]
  → NRRF767 fill admission
  → [separate assessed gross, costs, and net]
  → settlement
  → [separate positivity evidence]
  → profit.
```

This is continual closure: a supplied event can be admitted as a local stage
when the separate trading, authentication, and exact-status evidence is also
supplied. It is not an absolute origin, a terminal truth verdict, or an
inference that closure itself makes a later price profitable.

## Source boundary

The exact files reported as
`NRRF777LiveNaturalFormSelectorRelationNotSpacetimeObjectTranslationEventFilled.lean`
and
`NRRF778ContinuumHaltingSubstrateOperationClosureRelativeFormSelectionTranslationalTruthEquality.lean`
are not present in this checkout. They were also not found in any accessible
local worktree or branch of the connected GitHub repositories on 2026-08-26.

Therefore NRRF779 does **not** claim to import or reconstruct those modules.
`ReportedSelectorOperations` names their required data, while
`TranslationCertificates` names the three exact results that must be supplied
by their real definitions:

```text
compatible rigid fill = closure selection
continuum halting ↔ relative selection
formReading(substrateTransport(op, form))
  = interactionOf(op).translate(formReading(form)).
```

These are hypotheses at the external boundary. Everything after they are
supplied—construction of the existing NRRF768 and NRRF766 witnesses, and
preservation of the NRRF767 receipt boundary—is locally machine-checked.

When the exact source commit is available, the correct next step is to import
NRRF777/778, define `ReportedSelectorOperations` using their actual
definitions, and prove `TranslationCertificates` from their actual theorems.
No downstream trading theorem should change.

## Why the datum is `Option {z : ℂ // z ≠ 0}`

The reported NRRF778 result says zero is a load-bearing separating case: at
zero, the selection succeeds while the reported operation does not halt.
Consequently a missing, `OPEN`, or unrealized receipt cannot be converted to
zero. NRRF779 uses:

```text
datum : Receipt → Option {z : ℂ // z ≠ 0}.
```

`none` is absence. `some z` includes a proof that `z ≠ 0`.
`no_translation_event_of_none` proves that an absent datum cannot be promoted
to a translation event by selecting a default.

## What `TE filled` proves

`TranslationEvent` carries one actual receipt, its nonzero realization, one
partial input, and the relation-specific rigidity and compatibility evidence.
`fill_eq_closure_selection` then proves that this finite event fills to the
reported closure selection.

That does not prove `IsSelected`. In the reported reading, the closure
selection is the direction of a datum, while `IsSelected ops z` is defined
literally as

```text
closureSel(z) = datumForm(z).
```

NRRF779 requires that equality separately in a `ReintegratedTradingStage`;
`halted` then follows only through the reported `halt_iff_selected`
certificate. This avoids introducing an unrelated Boolean or proposition and
makes selection an equality of the reported forms themselves.

## The actual cross-system translation

A reported form is not a network reading and is not an NRRF627 pole. The only
admissible route is:

```text
reported Form → formReading → Network.Reading.
```

The crucial equation is

```text
formReading(substrateTransport(op, form))
  = interactionOf(op).translate(formReading(form)).
```

The fill equation, the selected-form equality, the datum-form/source-reading
equation, and the target transport equation first derive
`source_fill_reading`. Together with the commuting square,
`ReintegratedTradingStage.translates` derives that the actual network
interaction carries the source reading to the target reading. The remaining
return and contextual selector equations construct
`NRRF768.SelectedTradingFormWitness`; its already proved
`toLocalTradeWitness` is the sole entrance into NRRF766 continual closure.

The admitted receipt datum therefore audits a supplied context and interaction.
It does not choose its own target by calling itself truth, halting, or closure.

## Receipt, settlement, and profit remain distinct

`toExactFillAdmission` still requires both:

```text
AuthenticatedFill receipt
runtime.status receipt = witnessed(localWitness).
```

No fill, selection, or halting theorem derives either field. The module also
proves:

- `public_no_receipt_admission_despite_fill`;
- `public_no_exact_fill_admission_despite_halting`; and
- `public_no_settled_outcome_despite_selection`.

Settlement still requires equality to a separately supplied assessed net
outcome. Profit still requires a separate empirical positivity witness after
costs. This is the exact point at which the present negative Bitstamp replay
remains valid evidence rather than being overwritten by a formal label.

## Machine-checked boundary

The registered module is
`lean/NRRF779ReportedSelectorTradingReintegration.lean`. It contains no
`sorry`. The printed dependency audit reports only the project's accepted
standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

NRRF779 is **proved conditionally and not yet instantiated from NRRF777/778**.
It is a verified reintegration interface, not a claim that the unavailable
external source or a new live-price execution has been audited.
