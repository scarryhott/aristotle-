# NRRF767 — Live public paper receipts and authenticated settlement

`NRRF767LivePublicPaperReceiptBoundary.lean` continues the finite, append-only
closure architecture of NRRF766. It adds the exact boundary needed by a live
public-book paper bot. It does not identify a public quote with a trade.

## Reading

A `LiveReceiptBridge` uses the existing NRRF766 runtime receipt carrier and
distinguishes two externally supplied predicates on it:

- `PublicQuoteOnly`: a public, non-atomic market observation;
- `AuthenticatedFill`: evidence that an actual account fill occurred.

The bridge requires those predicates to be disjoint. It also requires every
public-only receipt to have the exact runtime status `continuing`. These are
bridge obligations, not facts that Lean manufactures about an exchange.

One supplied public receipt forms a `PublicPaperStage`. Finite public evidence
is retained in `PublicPaperTrace`; `PublicPaperExtension` appends exactly one
next stage and `extend_retains_prefix` proves that the earlier trace is
preserved. `CanExtend` is only an obligation to supply another receipt. No
future stream or terminal closure is assumed.

## Public evidence cannot settle

The decisive separation is machine checked twice:

- `PublicPaperStage.no_receipt_admission`: a public stage cannot satisfy the
  existing NRRF766 `ReceiptAdmission`, because `continuing` cannot equal the
  required exact `witnessed` status;
- `PublicPaperStage.no_exact_fill_admission`: the same public receipt cannot
  carry `AuthenticatedFill`, by the bridge's disjointness condition.

Consequently `PublicPaperStage.no_settled_outcome` proves that a public quote
stage cannot acquire a settled outcome. A runtime paper mark can be retained,
but it is not promoted to a fill, a closure-history stage, or P&L.

## What can settle

`ExactFillAdmission` requires both:

1. separately supplied authenticated-fill evidence; and
2. NRRF766's exact `ReceiptAdmission`, including its local closure witness and
   witnessed-status coherence.

`ExactFillExtension` additionally requires the reading boundary from the
current witnessed history to this actual fill. It appends one stage and proves
the old history remains an exact prefix. `CanExactFillExtend` remains a
caller-supplied obligation; no theorem says that a future fill exists.

`SettledOutcome` contains an exact fill admission and an assessed net that is
equal to the separately supplied gross/cost/net assessment. Positivity is not
part of settlement. `SettledProfit` adds positivity as further empirical
evidence, while `failed_fill_refutes_universal_profit` proves that one admitted
negative fill refutes a universal profit claim.

## Bundled result and axioms

`nrrf767_answer` collects the boundary:

- public status is continuing;
- public evidence is not a receipt admission;
- an appended fill is authenticated;
- its runtime status is the exact witnessed status;
- appending it retains the old closure history as a prefix.

The module builds without `sorry`. The printed axiom dependencies for the
bundled theorem, public-no-settlement theorem, and failed-profit refutation are
exactly `[propext, Quot.sound]`.

This formal module proves a conditional interface discipline. It does not
prove that the Python runtime implements Lean values, does not authenticate
Bitstamp data, does not authorize orders, and does not imply profit.
