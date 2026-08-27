import NRRF766ContinualTradingClosureFeedback

/-!
# NRRF767 — Live public paper receipts and authenticated settlement

Public quote receipts may be retained as finite stage evidence, but remain `continuing`.
They cannot enter the witnessed closure history or become settled outcomes. An actual fill
enters only through separately supplied authenticated-fill evidence, the existing exact
`ReceiptAdmission`, and one boundary to the current finite history.

Nothing here supplies a future receipt, proves every history extendable, guarantees profit,
or authorizes an order.
-/

namespace NRRF767

open NRRF764

universe u v w z t q

/-- The same runtime receipt carrier may contain public quote-only observations and authenticated
fills. Authentication is an external bridge obligation; Lean does not manufacture it. -/
structure LiveReceiptBridge {N : Network.{u, v}} {R : Type w}
    (I : TradingInterface.{w, z, u, v} N R) where
  runtime : NRRF766.RuntimeBridge.{w, t, u, v, z} I
  PublicQuoteOnly : runtime.Receipt → Prop
  AuthenticatedFill : runtime.Receipt → Prop
  public_not_authenticated_fill :
    ∀ receipt, PublicQuoteOnly receipt → ¬ AuthenticatedFill receipt
  public_status_continuing :
    ∀ receipt, PublicQuoteOnly receipt → runtime.status receipt =
      NRRF766.StageStatus.continuing

/-- One actually supplied public quote receipt. It is evidence retained at this stage, not a
witnessed trade or fill. -/
structure PublicPaperStage {N : Network.{u, v}} {R : Type w}
    {I : TradingInterface.{w, z, u, v} N R}
    (bridge : LiveReceiptBridge.{u, v, w, z, t} I) where
  receipt : bridge.runtime.Receipt
  publicOnly : bridge.PublicQuoteOnly receipt

namespace PublicPaperStage

theorem status_continuing {N : Network.{u, v}} {R : Type w}
    {I : TradingInterface.{w, z, u, v} N R}
    {bridge : LiveReceiptBridge.{u, v, w, z, t} I}
    (stage : PublicPaperStage bridge) :
    bridge.runtime.status stage.receipt = NRRF766.StageStatus.continuing :=
  bridge.public_status_continuing stage.receipt stage.publicOnly

/-- A public quote-only receipt cannot satisfy the existing exact receipt-admission boundary,
because its status is `continuing`, while admission requires that exact status to be `witnessed`. -/
theorem no_receipt_admission {N : Network.{u, v}} {R : Type w}
    {I : TradingInterface.{w, z, u, v} N R}
    {bridge : LiveReceiptBridge.{u, v, w, z, t} I}
    (stage : PublicPaperStage bridge) :
    ¬ Nonempty
      (NRRF766.RuntimeBridge.ReceiptAdmission bridge.runtime stage.receipt) := by
  rintro ⟨admission⟩
  have h := admission.status_witnessed
  rw [stage.status_continuing] at h
  cases h

end PublicPaperStage

/-! ## A separate finite paper-evidence trace -/

abbrev PublicPaperTrace {N : Network.{u, v}} {R : Type w}
    {I : TradingInterface.{w, z, u, v} N R}
    (bridge : LiveReceiptBridge.{u, v, w, z, t} I) :=
  List (PublicPaperStage bridge)

def PaperTracePrefix {N : Network.{u, v}} {R : Type w}
    {I : TradingInterface.{w, z, u, v} N R}
    {bridge : LiveReceiptBridge.{u, v, w, z, t} I}
    (left right : PublicPaperTrace bridge) : Prop :=
  ∃ tail, right = left ++ tail

/-- Exactly one supplied next public stage. There is no stage after `next` in this type. -/
structure PublicPaperExtension {N : Network.{u, v}} {R : Type w}
    {I : TradingInterface.{w, z, u, v} N R}
    {bridge : LiveReceiptBridge.{u, v, w, z, t} I}
    (_trace : PublicPaperTrace bridge) where
  next : PublicPaperStage bridge

namespace PublicPaperTrace

/-- Extendability remains an obligation to supply a next stage. -/
def CanExtend {N : Network.{u, v}} {R : Type w}
    {I : TradingInterface.{w, z, u, v} N R}
    {bridge : LiveReceiptBridge.{u, v, w, z, t} I}
    (trace : PublicPaperTrace bridge) : Prop :=
  Nonempty (PublicPaperExtension trace)

/-- Append only the supplied next public stage. -/
def extend {N : Network.{u, v}} {R : Type w}
    {I : TradingInterface.{w, z, u, v} N R}
    {bridge : LiveReceiptBridge.{u, v, w, z, t} I}
    (trace : PublicPaperTrace bridge)
    (extension : PublicPaperExtension trace) :
    PublicPaperTrace bridge :=
  trace ++ [extension.next]

theorem extend_retains_prefix {N : Network.{u, v}} {R : Type w}
    {I : TradingInterface.{w, z, u, v} N R}
    {bridge : LiveReceiptBridge.{u, v, w, z, t} I}
    (trace : PublicPaperTrace bridge)
    (extension : PublicPaperExtension trace) :
    PaperTracePrefix trace (trace.extend extension) := by
  exact ⟨[extension.next], rfl⟩

end PublicPaperTrace

/-! ## Authenticated fill admission -/

/-- A fill enters only when it carries external authenticated-fill evidence and also satisfies
NRRF766's exact witnessed-status receipt admission. -/
structure ExactFillAdmission {N : Network.{u, v}} {R : Type w}
    {I : TradingInterface.{w, z, u, v} N R}
    (bridge : LiveReceiptBridge.{u, v, w, z, t} I)
    (receipt : bridge.runtime.Receipt) where
  authenticated : bridge.AuthenticatedFill receipt
  receiptAdmission :
    NRRF766.RuntimeBridge.ReceiptAdmission bridge.runtime receipt

namespace PublicPaperStage

theorem no_exact_fill_admission {N : Network.{u, v}} {R : Type w}
    {I : TradingInterface.{w, z, u, v} N R}
    {bridge : LiveReceiptBridge.{u, v, w, z, t} I}
    (stage : PublicPaperStage bridge) :
    ¬ Nonempty (ExactFillAdmission bridge stage.receipt) := by
  rintro ⟨admission⟩
  exact bridge.public_not_authenticated_fill stage.receipt stage.publicOnly
    admission.authenticated

end PublicPaperStage

namespace ExactFillAdmission

def stage {N : Network.{u, v}} {R : Type w}
    {I : TradingInterface.{w, z, u, v} N R}
    {bridge : LiveReceiptBridge.{u, v, w, z, t} I}
    {receipt : bridge.runtime.Receipt}
    (admission : ExactFillAdmission bridge receipt) :
    NRRF766.ClosureStage I :=
  admission.receiptAdmission.stage

theorem exact_status {N : Network.{u, v}} {R : Type w}
    {I : TradingInterface.{w, z, u, v} N R}
    {bridge : LiveReceiptBridge.{u, v, w, z, t} I}
    {receipt : bridge.runtime.Receipt}
    (admission : ExactFillAdmission bridge receipt) :
    bridge.runtime.status receipt =
      NRRF766.StageStatus.witnessed
        admission.receiptAdmission.witness :=
  admission.receiptAdmission.status_witnessed

end ExactFillAdmission

/-! ## One authenticated append-only extension -/

/-- Appending one authenticated fill additionally requires the exact reading boundary to the
current witnessed history. -/
structure ExactFillExtension {N : Network.{u, v}} {R : Type w}
    {I : TradingInterface.{w, z, u, v} N R}
    {current : NRRF766.ClosureStage I}
    (_history : NRRF766.ClosureHistory I current)
    (bridge : LiveReceiptBridge.{u, v, w, z, t} I) where
  receipt : bridge.runtime.Receipt
  admission : ExactFillAdmission bridge receipt
  boundary :
    NRRF766.BoundaryMatches current.problem
      (bridge.runtime.problem receipt)

namespace ExactFillExtension

def toHistoryExtension {N : Network.{u, v}} {R : Type w}
    {I : TradingInterface.{w, z, u, v} N R}
    {current : NRRF766.ClosureStage I}
    {history : NRRF766.ClosureHistory I current}
    {bridge : LiveReceiptBridge.{u, v, w, z, t} I}
    (extension : ExactFillExtension history bridge) :
    NRRF766.ClosureHistory.Extension history where
  next := extension.admission.stage
  boundary := extension.boundary

def extendHistory {N : Network.{u, v}} {R : Type w}
    {I : TradingInterface.{w, z, u, v} N R}
    {current : NRRF766.ClosureStage I}
    {history : NRRF766.ClosureHistory I current}
    {bridge : LiveReceiptBridge.{u, v, w, z, t} I}
    (extension : ExactFillExtension history bridge) :
    NRRF766.ClosureHistory I extension.toHistoryExtension.next :=
  history.extend extension.toHistoryExtension

theorem retains_prefix {N : Network.{u, v}} {R : Type w}
    {I : TradingInterface.{w, z, u, v} N R}
    {current : NRRF766.ClosureStage I}
    {history : NRRF766.ClosureHistory I current}
    {bridge : LiveReceiptBridge.{u, v, w, z, t} I}
    (extension : ExactFillExtension history bridge) :
    NRRF766.ClosureHistory.HistoryPrefix history
      extension.extendHistory :=
  NRRF766.ClosureHistory.extend_retains_prefix history
    extension.toHistoryExtension

end ExactFillExtension

/-- The existing history does not imply that an authenticated next fill exists. -/
def CanExactFillExtend {N : Network.{u, v}} {R : Type w}
    {I : TradingInterface.{w, z, u, v} N R}
    {current : NRRF766.ClosureStage I}
    (history : NRRF766.ClosureHistory I current)
    (bridge : LiveReceiptBridge.{u, v, w, z, t} I) : Prop :=
  Nonempty (ExactFillExtension history bridge)

/-! ## Settlement and P&L boundary -/

abbrev FillAssessment {N : Network.{u, v}} {R : Type w}
    {I : TradingInterface.{w, z, u, v} N R}
    (bridge : LiveReceiptBridge.{u, v, w, z, t} I) :=
  NRRF766.ContinualAssessment.{w, q, u, v, z, t}
    bridge.runtime.toContinualRealization

/-- A settled outcome requires exact fill admission and equality to the separately supplied
gross/cost/net assessment. Positivity is not a field. -/
structure SettledOutcome {N : Network.{u, v}} {R : Type w}
    {I : TradingInterface.{w, z, u, v} N R}
    (bridge : LiveReceiptBridge.{u, v, w, z, t} I)
    (assessment : FillAssessment.{u, v, w, z, t, q} bridge)
    (receipt : bridge.runtime.Receipt) where
  admission : ExactFillAdmission bridge receipt
  settledNet : assessment.Outcome
  settledNet_eq : settledNet = assessment.net receipt

def HasSettledOutcome {N : Network.{u, v}} {R : Type w}
    {I : TradingInterface.{w, z, u, v} N R}
    (bridge : LiveReceiptBridge.{u, v, w, z, t} I)
    (assessment : FillAssessment.{u, v, w, z, t, q} bridge)
    (receipt : bridge.runtime.Receipt) : Prop :=
  Nonempty (SettledOutcome bridge assessment receipt)

/-- Profit is strictly more data than settlement: it requires an empirical positivity witness. -/
structure SettledProfit {N : Network.{u, v}} {R : Type w}
    {I : TradingInterface.{w, z, u, v} N R}
    (bridge : LiveReceiptBridge.{u, v, w, z, t} I)
    (assessment : FillAssessment.{u, v, w, z, t, q} bridge)
    (receipt : bridge.runtime.Receipt) where
  settlement : SettledOutcome bridge assessment receipt
  positive : assessment.positive settlement.settledNet

namespace SettledOutcome

theorem requires_authenticated_fill {N : Network.{u, v}} {R : Type w}
    {I : TradingInterface.{w, z, u, v} N R}
    {bridge : LiveReceiptBridge.{u, v, w, z, t} I}
    {assessment : FillAssessment.{u, v, w, z, t, q} bridge}
    {receipt : bridge.runtime.Receipt}
    (settlement : SettledOutcome bridge assessment receipt) :
    bridge.AuthenticatedFill receipt :=
  settlement.admission.authenticated

theorem requires_exact_status {N : Network.{u, v}} {R : Type w}
    {I : TradingInterface.{w, z, u, v} N R}
    {bridge : LiveReceiptBridge.{u, v, w, z, t} I}
    {assessment : FillAssessment.{u, v, w, z, t, q} bridge}
    {receipt : bridge.runtime.Receipt}
    (settlement : SettledOutcome bridge assessment receipt) :
    bridge.runtime.status receipt =
      NRRF766.StageStatus.witnessed
        settlement.admission.receiptAdmission.witness :=
  settlement.admission.exact_status

end SettledOutcome

namespace PublicPaperStage

/-- A quote-only paper stage has no settled outcome. Its paper mark may remain runtime evidence,
but it is not promoted to fill settlement. -/
theorem no_settled_outcome {N : Network.{u, v}} {R : Type w}
    {I : TradingInterface.{w, z, u, v} N R}
    {bridge : LiveReceiptBridge.{u, v, w, z, t} I}
    (stage : PublicPaperStage bridge)
    (assessment : FillAssessment.{u, v, w, z, t, q} bridge) :
    ¬ HasSettledOutcome bridge assessment stage.receipt := by
  rintro ⟨settlement⟩
  exact bridge.public_not_authenticated_fill stage.receipt stage.publicOnly
    settlement.requires_authenticated_fill

end PublicPaperStage

/-! ## Profit remains independently refutable -/

def EveryAdmittedFillPositive {N : Network.{u, v}} {R : Type w}
    {I : TradingInterface.{w, z, u, v} N R}
    (bridge : LiveReceiptBridge.{u, v, w, z, t} I)
    (assessment : FillAssessment.{u, v, w, z, t, q} bridge) : Prop :=
  ∀ receipt, ExactFillAdmission bridge receipt →
    assessment.positive (assessment.net receipt)

theorem failed_fill_refutes_universal_profit {N : Network.{u, v}}
    {R : Type w} {I : TradingInterface.{w, z, u, v} N R}
    (bridge : LiveReceiptBridge.{u, v, w, z, t} I)
    (assessment : FillAssessment.{u, v, w, z, t, q} bridge)
    (receipt : bridge.runtime.Receipt)
    (admission : ExactFillAdmission bridge receipt)
    (failure : ¬ assessment.positive (assessment.net receipt)) :
    ¬ EveryAdmittedFillPositive bridge assessment := by
  intro guarantee
  exact failure (guarantee receipt admission)

/-! ## Bundled boundary -/

theorem nrrf767_answer {N : Network.{u, v}} {R : Type w}
    {I : TradingInterface.{w, z, u, v} N R}
    {bridge : LiveReceiptBridge.{u, v, w, z, t} I}
    (paper : PublicPaperStage bridge)
    {current : NRRF766.ClosureStage I}
    {history : NRRF766.ClosureHistory I current}
    (fill : ExactFillExtension history bridge) :
    bridge.runtime.status paper.receipt =
        NRRF766.StageStatus.continuing ∧
    (¬ Nonempty
      (NRRF766.RuntimeBridge.ReceiptAdmission
        bridge.runtime paper.receipt)) ∧
    bridge.AuthenticatedFill fill.receipt ∧
    bridge.runtime.status fill.receipt =
      NRRF766.StageStatus.witnessed
        fill.admission.receiptAdmission.witness ∧
    NRRF766.ClosureHistory.HistoryPrefix history
      fill.extendHistory := by
  exact ⟨paper.status_continuing, paper.no_receipt_admission,
    fill.admission.authenticated, fill.admission.exact_status,
    fill.retains_prefix⟩

#print axioms NRRF767.nrrf767_answer
#print axioms NRRF767.PublicPaperStage.no_settled_outcome
#print axioms NRRF767.failed_fill_refutes_universal_profit

end NRRF767
