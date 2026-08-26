import NRRF767LivePublicPaperReceiptBoundary
import NRRF768RelativeTranslationalTruthNaturalFormSelector
import Mathlib.Data.Complex.Basic

/-!
# NRRF779 — Reported live selector reintegrated with continual trading

The reported NRRF777/NRRF778 source files are not present in this checkout.  This module therefore
does not pretend to import or reconstruct them.  It states the smallest explicit operations and
certificates their reported results must supply, then proves how those certificates enter the
locally checked NRRF768 → NRRF766 → NRRF767 trading boundary.

The separation is load-bearing:

* a live receipt may carry no admissible datum (`none`);
* an admitted datum is nonzero, so the reported zero-degeneracy cannot be hidden as an `OPEN` case;
* compatible rigid filling, selection/halting equality, and substrate transport are certified
  translations, not a profit rule;
* a filled and selected form yields a local trade witness only with the existing interaction,
  return, and contextual-selector equations;
* receipt authentication and exact witnessed status are still required for fill admission;
* settlement and positive net outcome remain independent empirical obligations.

Thus the selector participates in continual closure without becoming an origin, terminal verdict,
order authorization, settlement, or profit guarantee.
-/

namespace NRRF779

open NRRF764

universe u v w z t q s

/-- NRRF778 reports that zero is a genuine separating case.  The trading bridge therefore carries
only explicitly nonzero complex data; absence remains `none` rather than being encoded as zero. -/
abbrev NonzeroDatum := {z : ℂ // z ≠ 0}

/-! ## Exact external surface of the reported selector/operation layer -/

/-- Operations required from the reported live relation selector.  The carriers are deliberately
abstract: this adapter does not manufacture the missing NRRF777/778 definitions. -/
structure ReportedSelectorOperations (N : Network.{u, v}) where
  Relation : Type s
  PartialInput : Type s
  Form : Type s
  SubstrateOp : Type s
  closureRel : NonzeroDatum → Relation
  Rigid : Relation → Prop
  Compatible : Relation → PartialInput → Prop
  fill : Relation → PartialInput → Form
  closureSel : NonzeroDatum → Form
  datumForm : NonzeroDatum → Form
  subHalt : NonzeroDatum → Prop
  substrateTransport : SubstrateOp → Form → Form
  interactionOf : SubstrateOp → Interaction N
  formReading : Form → N.Reading

/-- The reported reading “the selected form is the datum itself,” expressed inside the reported
form carrier before either side is sent to the trading network. -/
def IsSelected {N : Network.{u, v}}
    (ops : ReportedSelectorOperations.{u, v, s} N)
    (datum : NonzeroDatum) : Prop :=
  ops.closureSel datum = ops.datumForm datum

/-- The three reported results actually used by trading.  These are obligations until exact
NRRF777/778 sources are supplied and locally rebuilt.  In particular, no field mentions price,
P&L, an order, receipt authentication, or settlement. -/
structure TranslationCertificates {N : Network.{u, v}}
    (ops : ReportedSelectorOperations.{u, v, s} N) where
  fill_closure_selection : ∀ datum input,
    ops.Rigid (ops.closureRel datum) →
    ops.Compatible (ops.closureRel datum) input →
    ops.fill (ops.closureRel datum) input = ops.closureSel datum
  halt_iff_selected : ∀ datum, ops.subHalt datum ↔ IsSelected ops datum
  substrate_translates_reading : ∀ op form,
    ops.formReading (ops.substrateTransport op form) =
      (ops.interactionOf op).translate (ops.formReading form)

/-! ## Live receipt realization without a zero/default collapse -/

/-- A live receipt bridge plus an explicit partial realization as nonzero selector data.  `none`
means that this receipt has no datum admitted to the selector layer. -/
structure RelationalLiveBridge {N : Network.{u, v}} {R : Type w}
    (I : TradingInterface.{w, z, u, v} N R) where
  live : NRRF767.LiveReceiptBridge.{u, v, w, z, t} I
  datum : live.runtime.Receipt → Option NonzeroDatum
  ReceiptRealizes : live.runtime.Receipt → ℂ → Prop
  realizes : ∀ receipt datum', datum receipt = some datum' →
    ReceiptRealizes receipt datum'.1

/-- One actual translation event.  Rigidity and compatibility belong to this receipt and partial
input; total or terminal closure is not assumed. -/
structure TranslationEvent {N : Network.{u, v}}
    (ops : ReportedSelectorOperations.{u, v, s} N)
    {R : Type w} {I : TradingInterface.{w, z, u, v} N R}
    (bridge : RelationalLiveBridge.{u, v, w, z, t} I)
    (receipt : bridge.live.runtime.Receipt) where
  nonzeroDatum : NonzeroDatum
  datum_eq : bridge.datum receipt = some nonzeroDatum
  input : ops.PartialInput
  rigid : ops.Rigid (ops.closureRel nonzeroDatum)
  compatible : ops.Compatible (ops.closureRel nonzeroDatum) input

namespace TranslationEvent

variable {N : Network.{u, v}}
  {ops : ReportedSelectorOperations.{u, v, s} N}
  {R : Type w} {I : TradingInterface.{w, z, u, v} N R}
  {bridge : RelationalLiveBridge.{u, v, w, z, t} I}
  {receipt : bridge.live.runtime.Receipt}

/-- The form actually filled by this finite event. -/
def filled (event : TranslationEvent ops bridge receipt) : ops.Form :=
  ops.fill (ops.closureRel event.nonzeroDatum) event.input

/-- `TE filled`: a compatible rigid event fills to the reported closure selection. -/
theorem fill_eq_closure_selection
    (cert : TranslationCertificates ops)
    (event : TranslationEvent ops bridge receipt) :
    event.filled = ops.closureSel event.nonzeroDatum :=
  cert.fill_closure_selection event.nonzeroDatum event.input
    event.rigid event.compatible

/-- The live receipt realizes the admitted nonzero datum. -/
theorem receipt_realizes (event : TranslationEvent ops bridge receipt) :
    bridge.ReceiptRealizes receipt event.nonzeroDatum.1 :=
  bridge.realizes receipt event.nonzeroDatum event.datum_eq

/-- The realization cannot silently reuse the degenerate zero case. -/
theorem datum_ne_zero (event : TranslationEvent ops bridge receipt) :
    event.nonzeroDatum.1 ≠ 0 :=
  event.nonzeroDatum.2

end TranslationEvent

/-- A receipt mapped to `none` cannot be promoted to a translation event by choosing zero or any
other default value. -/
theorem no_translation_event_of_none {N : Network.{u, v}}
    {ops : ReportedSelectorOperations.{u, v, s} N}
    {R : Type w} {I : TradingInterface.{w, z, u, v} N R}
    {bridge : RelationalLiveBridge.{u, v, w, z, t} I}
    {receipt : bridge.live.runtime.Receipt}
    (missing : bridge.datum receipt = none) :
    ¬ Nonempty (TranslationEvent ops bridge receipt) := by
  rintro ⟨event⟩
  have impossible := event.datum_eq
  rw [missing] at impossible
  cases impossible

/-- The reported translational truth equality, exposed without identifying it with a network
reading before `formReading` is applied. -/
theorem halt_iff_selected {N : Network.{u, v}}
    {ops : ReportedSelectorOperations.{u, v, s} N}
    (cert : TranslationCertificates ops) (datum : NonzeroDatum) :
    ops.subHalt datum ↔ IsSelected ops datum :=
  cert.halt_iff_selected datum

/-- Substrate transport becomes a network interaction only through this commuting reading square. -/
theorem substrate_transport_translates_reading {N : Network.{u, v}}
    {ops : ReportedSelectorOperations.{u, v, s} N}
    (cert : TranslationCertificates ops) (op : ops.SubstrateOp) (form : ops.Form) :
    ops.formReading (ops.substrateTransport op form) =
      (ops.interactionOf op).translate (ops.formReading form) :=
  cert.substrate_translates_reading op form

/-! ## Reintegrated selector event into the existing continual trading witness -/

/-- A selected event can enter trading only when its filled form and substrate transport commute
with the actual source/target readings and the already proved NRRF768 contextual selector.

`selected` yields the reported halting reading.  The remaining fields are not derived from it:
they are the exact local interaction/return/selector evidence needed by NRRF768. -/
structure ReintegratedTradingStage {N : Network.{u, v}}
    (ops : ReportedSelectorOperations.{u, v, s} N)
    (cert : TranslationCertificates ops)
    {R : Type w} {I : TradingInterface.{w, z, u, v} N R}
    (bridge : RelationalLiveBridge.{u, v, w, z, t} I)
    (selector : NRRF768.NaturalFormSelector (NRRF627.flipFrame N.Reading))
    (receipt : bridge.live.runtime.Receipt) where
  event : TranslationEvent ops bridge receipt
  substrateOp : ops.SubstrateOp
  selected : IsSelected ops event.nonzeroDatum
  datum_form_reading :
    ops.formReading (ops.datumForm event.nonzeroDatum) =
      NRRF766.sourceReading (bridge.live.runtime.problem receipt)
  target_transport_reading :
    ops.formReading (ops.substrateTransport substrateOp event.filled) =
      NRRF766.targetReading (bridge.live.runtime.problem receipt)
  closure_at_source :
    I.closureReturn
        ((ops.interactionOf substrateOp).translate
          (NRRF766.sourceReading (bridge.live.runtime.problem receipt))) =
      I.closureReturn
        (NRRF766.sourceReading (bridge.live.runtime.problem receipt))
  source_is_selected :
    selector.select
        (I.perspective (bridge.live.runtime.problem receipt).source)
        (NRRF766.sourceReading (bridge.live.runtime.problem receipt)) =
      I.occurrence (bridge.live.runtime.problem receipt).source
  interaction_carries_selected :
    selector.select
        (I.perspective (bridge.live.runtime.problem receipt).source)
        ((ops.interactionOf substrateOp).translate
          (NRRF766.sourceReading (bridge.live.runtime.problem receipt))) =
      ((ops.interactionOf substrateOp).translate
          (NRRF766.sourceReading (bridge.live.runtime.problem receipt)),
        (selector.select
          (I.perspective (bridge.live.runtime.problem receipt).source)
          (NRRF766.sourceReading (bridge.live.runtime.problem receipt))).2)
  target_is_selected :
    selector.select
        (I.perspective (bridge.live.runtime.problem receipt).target)
        (NRRF766.targetReading (bridge.live.runtime.problem receipt)) =
      I.occurrence (bridge.live.runtime.problem receipt).target

namespace ReintegratedTradingStage

variable {N : Network.{u, v}}
  {ops : ReportedSelectorOperations.{u, v, s} N}
  {cert : TranslationCertificates ops}
  {R : Type w} {I : TradingInterface.{w, z, u, v} N R}
  {bridge : RelationalLiveBridge.{u, v, w, z, t} I}
  {selector : NRRF768.NaturalFormSelector (NRRF627.flipFrame N.Reading)}
  {receipt : bridge.live.runtime.Receipt}

abbrev problem (_stage : ReintegratedTradingStage ops cert bridge selector receipt) :
    TradingProblem I :=
  bridge.live.runtime.problem receipt

/-- The filled live event is the reported closure selection. -/
theorem fill_eq_closure_selection
    (stage : ReintegratedTradingStage ops cert bridge selector receipt) :
    stage.event.filled = ops.closureSel stage.event.nonzeroDatum :=
  stage.event.fill_eq_closure_selection cert

/-- Selection and continuum halting are the two reported readings of this event. -/
theorem halted (stage : ReintegratedTradingStage ops cert bridge selector receipt) :
    ops.subHalt stage.event.nonzeroDatum :=
  (cert.halt_iff_selected stage.event.nonzeroDatum).2 stage.selected

/-- Filling and selection now genuinely participate in the trading map: the filled form reads as
the actual source because it equals the closure selection, which equals the datum form. -/
theorem source_fill_reading
    (stage : ReintegratedTradingStage ops cert bridge selector receipt) :
    ops.formReading stage.event.filled =
      NRRF766.sourceReading stage.problem := by
  calc
    ops.formReading stage.event.filled =
        ops.formReading (ops.closureSel stage.event.nonzeroDatum) :=
      congrArg ops.formReading stage.fill_eq_closure_selection
    _ = ops.formReading (ops.datumForm stage.event.nonzeroDatum) :=
      congrArg ops.formReading stage.selected
    _ = NRRF766.sourceReading stage.problem :=
      stage.datum_form_reading

/-- The substrate operation translates the filled source reading to the target reading.  This is
the critical commuting-square derivation; it is not asserted by juxtaposing the two systems. -/
theorem translates (stage : ReintegratedTradingStage ops cert bridge selector receipt) :
    (ops.interactionOf stage.substrateOp).translate
        (NRRF766.sourceReading stage.problem) =
      NRRF766.targetReading stage.problem := by
  calc
    (ops.interactionOf stage.substrateOp).translate
        (NRRF766.sourceReading stage.problem) =
        (ops.interactionOf stage.substrateOp).translate
          (ops.formReading stage.event.filled) := by
      exact congrArg (ops.interactionOf stage.substrateOp).translate
        stage.source_fill_reading.symm
    _ = ops.formReading
        (ops.substrateTransport stage.substrateOp stage.event.filled) :=
      (cert.substrate_translates_reading stage.substrateOp stage.event.filled).symm
    _ = NRRF766.targetReading stage.problem :=
      stage.target_transport_reading

/-- The reintegrated stage constructs exactly the existing NRRF768 selected-form witness. -/
def toSelectedTradingFormWitness
    (stage : ReintegratedTradingStage ops cert bridge selector receipt) :
    NRRF768.SelectedTradingFormWitness selector stage.problem where
  interaction := ops.interactionOf stage.substrateOp
  closure_at_source := stage.closure_at_source
  translates := stage.translates
  source_is_selected := stage.source_is_selected
  interaction_carries_selected := stage.interaction_carries_selected
  target_is_selected := stage.target_is_selected

/-- Consequently the stage enters continual trading through the single existing local-witness
boundary.  No order, authentication, settlement, or profit follows. -/
def toLocalTradeWitness
    (stage : ReintegratedTradingStage ops cert bridge selector receipt) :
    NRRF766.LocalTradeWitness stage.problem :=
  stage.toSelectedTradingFormWitness.toLocalTradeWitness

/-- An exact fill admission still needs external authentication and the exact runtime status for
the witness constructed above. -/
def toExactFillAdmission
    (stage : ReintegratedTradingStage ops cert bridge selector receipt)
    (authenticated : bridge.live.AuthenticatedFill receipt)
    (status_witnessed : bridge.live.runtime.status receipt =
      NRRF766.StageStatus.witnessed stage.toLocalTradeWitness) :
    NRRF767.ExactFillAdmission bridge.live receipt where
  authenticated := authenticated
  receiptAdmission := {
    witness := stage.toLocalTradeWitness
    status_witnessed := status_witnessed
  }

end ReintegratedTradingStage

/-! ## Public-paper and profit boundaries survive the reintegration -/

/-- Filling a public quote-only receipt still does not admit it to witnessed closure history. -/
theorem public_no_receipt_admission_despite_fill {N : Network.{u, v}}
    {ops : ReportedSelectorOperations.{u, v, s} N}
    (cert : TranslationCertificates ops)
    {R : Type w} {I : TradingInterface.{w, z, u, v} N R}
    {bridge : RelationalLiveBridge.{u, v, w, z, t} I}
    (paper : NRRF767.PublicPaperStage bridge.live)
    (event : TranslationEvent ops bridge paper.receipt) :
    ¬ Nonempty
      (NRRF766.RuntimeBridge.ReceiptAdmission bridge.live.runtime paper.receipt) := by
  have _filled := event.fill_eq_closure_selection cert
  exact paper.no_receipt_admission

/-- Even filled + selected + halted does not turn a public quote into an authenticated fill. -/
theorem public_no_exact_fill_admission_despite_halting {N : Network.{u, v}}
    {ops : ReportedSelectorOperations.{u, v, s} N}
    {cert : TranslationCertificates ops}
    {R : Type w} {I : TradingInterface.{w, z, u, v} N R}
    {bridge : RelationalLiveBridge.{u, v, w, z, t} I}
    {selector : NRRF768.NaturalFormSelector (NRRF627.flipFrame N.Reading)}
    (paper : NRRF767.PublicPaperStage bridge.live)
    (_stage : ReintegratedTradingStage ops cert bridge selector paper.receipt) :
    ¬ Nonempty (NRRF767.ExactFillAdmission bridge.live paper.receipt) :=
  paper.no_exact_fill_admission

/-- Selector completion and local closure do not manufacture a settled P&L outcome for public
paper data. -/
theorem public_no_settled_outcome_despite_selection {N : Network.{u, v}}
    {ops : ReportedSelectorOperations.{u, v, s} N}
    {cert : TranslationCertificates ops}
    {R : Type w} {I : TradingInterface.{w, z, u, v} N R}
    {bridge : RelationalLiveBridge.{u, v, w, z, t} I}
    {selector : NRRF768.NaturalFormSelector (NRRF627.flipFrame N.Reading)}
    (paper : NRRF767.PublicPaperStage bridge.live)
    (_stage : ReintegratedTradingStage ops cert bridge selector paper.receipt)
    (assessment : NRRF767.FillAssessment.{u, v, w, z, t, q} bridge.live) :
    ¬ NRRF767.HasSettledOutcome bridge.live assessment paper.receipt :=
  paper.no_settled_outcome assessment

/-- The reintegration theorem: one supplied live stage simultaneously exposes the reported fill,
halting/selection equality, and the existing continual local trade witness.  Its conclusion stops
at that local boundary. -/
theorem nrrf779_answer {N : Network.{u, v}}
    {ops : ReportedSelectorOperations.{u, v, s} N}
    {cert : TranslationCertificates ops}
    {R : Type w} {I : TradingInterface.{w, z, u, v} N R}
    {bridge : RelationalLiveBridge.{u, v, w, z, t} I}
    {selector : NRRF768.NaturalFormSelector (NRRF627.flipFrame N.Reading)}
    {receipt : bridge.live.runtime.Receipt}
    (stage : ReintegratedTradingStage ops cert bridge selector receipt) :
    stage.event.filled = ops.closureSel stage.event.nonzeroDatum ∧
    ops.subHalt stage.event.nonzeroDatum ∧
    Nonempty (NRRF766.LocalTradeWitness stage.problem) :=
  ⟨stage.fill_eq_closure_selection, stage.halted, ⟨stage.toLocalTradeWitness⟩⟩

#print axioms NRRF779.nrrf779_answer
#print axioms NRRF779.public_no_receipt_admission_despite_fill
#print axioms NRRF779.public_no_exact_fill_admission_despite_halting
#print axioms NRRF779.public_no_settled_outcome_despite_selection

end NRRF779
