import NRRF764TradingNetworkInterfaceProof

/-!
# NRRF766 — Continual trading closure and empirical feedback

Continual closure is constructed here as a finite append-only history. A history begins with one
locally witnessed interaction. Extending it requires the next problem, its local witness, and the
boundary identifying the old target with the new source. No future problem or witness is built
into the history type.

Profit and loss remain empirical observations. A stage-local feedback extension retains the net
outcome while supplying one next problem; closure never implies that the outcome is positive and
never manufactures the next extension.
-/

namespace NRRF766

open NRRF764

universe u v w z t q

/-! ## Stage-local interface readings -/

def sourceReading {N : Network} {R : Type w} {I : TradingInterface N R}
    (P : TradingProblem I) : N.Reading :=
  N.read (I.site P.source)

def targetReading {N : Network} {R : Type w} {I : TradingInterface N R}
    (P : TradingProblem I) : N.Reading :=
  N.read (I.site P.target)

/-- Two consecutive problems meet at the same network reading. Their quote records may still
carry different timestamps or provenance. -/
def BoundaryMatches {N : Network} {R : Type w} {I : TradingInterface N R}
    (P Q : TradingProblem I) : Prop :=
  targetReading P = sourceReading Q

/-! ## A local witness, not a terminal proof -/

/-- Closure witnessed only at the source actually presented by this problem. -/
structure LocalTradeWitness {N : Network} {R : Type w} {I : TradingInterface N R}
    (P : TradingProblem I) where
  interaction : Interaction N
  closure_at_source :
    I.closureReturn (interaction.translate (sourceReading P)) =
      I.closureReturn (sourceReading P)
  frame_closes :
    (NRRF627.flipFrame N.Reading).T
        (I.perspective P.source) (I.perspective P.target)
        (interaction.translate (sourceReading P), I.orientation P.source) =
      I.occurrence P.target

/-- `P` closes at this presented stage when a local witness is available. -/
def ClosesAt {N : Network} {R : Type w} {I : TradingInterface N R}
    (P : TradingProblem I) : Prop :=
  Nonempty (LocalTradeWitness P)

namespace LocalTradeWitness

/-- Every earlier global `TradeProof` supplies a local witness. -/
def ofTradeProof {N : Network} {R : Type w} {I : TradingInterface N R}
    {P : TradingProblem I} (proof : TradeProof P) : LocalTradeWitness P where
  interaction := proof.interaction
  closure_at_source := proof.closure_natural _
  frame_closes := proof.frame_closes

/-- Transport the exact local witness along equality of the presented problem. -/
def transport {N : Network} {R : Type w} {I : TradingInterface N R}
    {P Q : TradingProblem I} (problem_eq : P = Q)
    (witness : LocalTradeWitness P) : LocalTradeWitness Q :=
  problem_eq ▸ witness

theorem closesAt_of_tradeProof {N : Network} {R : Type w}
    {I : TradingInterface N R} {P : TradingProblem I} (proof : TradeProof P) :
    ClosesAt P :=
  ⟨ofTradeProof proof⟩

/-- The frame equation translates this stage's actual source into its target. -/
theorem translates {N : Network} {R : Type w} {I : TradingInterface N R}
    {P : TradingProblem I} (witness : LocalTradeWitness P) :
    witness.interaction.translate (sourceReading P) = targetReading P := by
  have h := congrArg Prod.fst witness.frame_closes
  simpa [NRRF627.flipFrame, TradingInterface.occurrence, sourceReading, targetReading] using h

/-- The closure return agrees at the two ends of this local stage. -/
theorem return_eq {N : Network} {R : Type w} {I : TradingInterface N R}
    {P : TradingProblem I} (witness : LocalTradeWitness P) :
    I.closureReturn (sourceReading P) = I.closureReturn (targetReading P) := by
  calc
    I.closureReturn (sourceReading P) =
        I.closureReturn (witness.interaction.translate (sourceReading P)) :=
      witness.closure_at_source.symm
    _ = I.closureReturn (targetReading P) :=
      congrArg I.closureReturn witness.translates

theorem geometry_quotient_eq {N : Network} {R : Type w} {I : TradingInterface N R}
    {P : TradingProblem I} (witness : LocalTradeWitness P) :
    Quotient.mk (polarSetoid R) (I.geometry P.source) =
      Quotient.mk (polarSetoid R) (I.geometry P.target) := by
  calc
    Quotient.mk (polarSetoid R) (I.geometry P.source) =
        I.closureReturn (sourceReading P) := by
      simpa [sourceReading, TradingInterface.geometry] using
        (I.quote_coherent P.source).symm
    _ = I.closureReturn (targetReading P) := witness.return_eq
    _ = Quotient.mk (polarSetoid R) (I.geometry P.target) := by
      simpa [targetReading, TradingInterface.geometry] using I.quote_coherent P.target

theorem geometry_closes {N : Network} {R : Type w} {I : TradingInterface N R}
    {P : TradingProblem I} (witness : LocalTradeWitness P) :
    PolarRel (I.geometry P.source) (I.geometry P.target) :=
  Quotient.exact witness.geometry_quotient_eq

end LocalTradeWitness

/-! ## Status has no terminal `OPEN` reading -/

/-- Semantic contradiction is supplied by the realization as a predicate on this exact problem.
Polar obstruction remains a separate geometric fact. -/
inductive StageStatus {N : Network} {R : Type w} {I : TradingInterface N R}
    (Contradicts : TradingProblem I → Prop) (P : TradingProblem I) where
  | witnessed (witness : LocalTradeWitness P)
  | continuing
  | polarObstructed (obstruction : IsContradicted P)
  | contradicted (evidence : Contradicts P)

namespace StageStatus

/-- Legacy geometric contradiction is preserved but renamed. Legacy global openness is reduced
to nonnegative `continuing`. -/
def ofLegacy {N : Network} {R : Type w} {I : TradingInterface N R}
    {P : TradingProblem I} : TradeDecision P → StageStatus (fun _ => False) P
  | .closed proof => .witnessed (LocalTradeWitness.ofTradeProof proof)
  | .contradicted obstruction => .polarObstructed obstruction
  | .open_uncontradicted _ _ => .continuing

end StageStatus

/-! ## Finite append-only continual closure -/

structure ClosureStage {N : Network} {R : Type w} (I : TradingInterface N R) where
  problem : TradingProblem I
  witness : LocalTradeWitness problem

/-- A nonempty, finite history indexed by its actual current stage. -/
inductive ClosureHistory {N : Network} {R : Type w} (I : TradingInterface N R) :
    ClosureStage I → Type _ where
  | start (stage : ClosureStage I) : ClosureHistory I stage
  | snoc {current : ClosureStage I} (history : ClosureHistory I current)
      (next : ClosureStage I)
      (boundary : BoundaryMatches current.problem next.problem) : ClosureHistory I next

namespace ClosureHistory

def initialStage {N : Network} {R : Type w} {I : TradingInterface N R}
    {current : ClosureStage I} : ClosureHistory I current → ClosureStage I
  | .start stage => stage
  | .snoc history _ _ => initialStage history

def stages {N : Network} {R : Type w} {I : TradingInterface N R}
    {current : ClosureStage I} : ClosureHistory I current → List (ClosureStage I)
  | .start stage => [stage]
  | .snoc history next _ => stages history ++ [next]

def interactions {N : Network} {R : Type w} {I : TradingInterface N R}
    {current : ClosureStage I} : ClosureHistory I current → List (Interaction N)
  | .start stage => [stage.witness.interaction]
  | .snoc history next _ => interactions history ++ [next.witness.interaction]

/-- The exact data needed to append one stage. It contains no stage after `next`. -/
structure Extension {N : Network} {R : Type w} {I : TradingInterface N R}
    {current : ClosureStage I} (_history : ClosureHistory I current) where
  next : ClosureStage I
  boundary : BoundaryMatches current.problem next.problem

/-- Extendability is evidence supplied from outside the existing history. -/
def CanExtend {N : Network} {R : Type w} {I : TradingInterface N R}
    {current : ClosureStage I} (history : ClosureHistory I current) : Prop :=
  Nonempty (Extension history)

/-- Append exactly the supplied next stage. -/
def extend {N : Network} {R : Type w} {I : TradingInterface N R}
    {current : ClosureStage I} (history : ClosureHistory I current)
    (extension : Extension history) : ClosureHistory I extension.next :=
  .snoc history extension.next extension.boundary

/-- Prefix is stated extensionally on the finite stage lists. -/
def HistoryPrefix {N : Network} {R : Type w} {I : TradingInterface N R}
    {leftCurrent rightCurrent : ClosureStage I}
    (left : ClosureHistory I leftCurrent) (right : ClosureHistory I rightCurrent) : Prop :=
  ∃ tail, right.stages = left.stages ++ tail

/-- Appending one stage retains every old stage as an exact prefix. -/
theorem extend_retains_prefix {N : Network} {R : Type w} {I : TradingInterface N R}
    {current : ClosureStage I} (history : ClosureHistory I current)
    (extension : Extension history) :
    HistoryPrefix history (history.extend extension) := by
  refine ⟨[extension.next], ?_⟩
  rfl

theorem memory_append {N : Network} (xs ys : List (Interaction N)) (r : N.Reading) :
    memory (xs ++ ys) r = memory ys (memory xs r) := by
  simp [memory, List.foldl_append]

/-- Executing the finite history reaches the target of its current stage. -/
theorem memory_eq_current_target {N : Network} {R : Type w}
    {I : TradingInterface N R} {current : ClosureStage I}
    (history : ClosureHistory I current) :
    memory history.interactions (sourceReading history.initialStage.problem) =
      targetReading current.problem := by
  induction history with
  | start stage =>
      simpa [interactions, initialStage, memory] using stage.witness.translates
  | snoc history next boundary ih =>
      rw [interactions, memory_append]
      change memory [next.witness.interaction]
          (memory history.interactions (sourceReading history.initialStage.problem)) =
        targetReading next.problem
      rw [ih, boundary]
      simpa [memory] using next.witness.translates

/-- Every executed history remains inside the shared network field. -/
theorem memory_shared {N : Network} {R : Type w} {I : TradingInterface N R}
    {current : ClosureStage I} (history : ClosureHistory I current) :
    memory history.interactions (sourceReading history.initialStage.problem) ∈ N.shared :=
  memory_admissible _ (N.read_shared _)

/-- Local return equality composes from the initial source to the current target. -/
theorem closureReturn_initial_eq_current_target {N : Network} {R : Type w}
    {I : TradingInterface N R} {current : ClosureStage I}
    (history : ClosureHistory I current) :
    I.closureReturn (sourceReading history.initialStage.problem) =
      I.closureReturn (targetReading current.problem) := by
  induction history with
  | start stage =>
      exact stage.witness.return_eq
  | snoc history next boundary ih =>
      exact ih.trans ((congrArg I.closureReturn boundary).trans next.witness.return_eq)

/-- The supplied extension reaches its own next target. -/
theorem extend_memory_eq_next_target {N : Network} {R : Type w}
    {I : TradingInterface N R} {current : ClosureStage I}
    (history : ClosureHistory I current) (extension : Extension history) :
    memory (history.extend extension).interactions
        (sourceReading (history.extend extension).initialStage.problem) =
      targetReading extension.next.problem :=
  memory_eq_current_target (history.extend extension)

/-- Extending preserves sharedness of the executed memory. -/
theorem extend_memory_shared {N : Network} {R : Type w}
    {I : TradingInterface N R} {current : ClosureStage I}
    (history : ClosureHistory I current) (extension : Extension history) :
    memory (history.extend extension).interactions
        (sourceReading (history.extend extension).initialStage.problem) ∈ N.shared :=
  memory_shared (history.extend extension)

/-- Extending preserves the initial closure return through the supplied next target. -/
theorem extend_preserves_closureReturn {N : Network} {R : Type w}
    {I : TradingInterface N R} {current : ClosureStage I}
    (history : ClosureHistory I current) (extension : Extension history) :
    I.closureReturn
        (sourceReading (history.extend extension).initialStage.problem) =
      I.closureReturn (targetReading extension.next.problem) :=
  closureReturn_initial_eq_current_target (history.extend extension)

end ClosureHistory

/-! ## Realization and semantic status -/

/-- A realization maps possible observations into the formal interface. It does not assert that
any particular future observation will occur. -/
structure ContinualRealization {N : Network} {R : Type w} (I : TradingInterface N R) where
  Observation : Type t
  Contradicts : TradingProblem I → Prop
  problem : Observation → TradingProblem I
  status : ∀ observation, StageStatus Contradicts (problem observation)

namespace ContinualRealization

def ofLegacy {N : Network} {R : Type w} {I : TradingInterface N R}
    (realization : TradingRealization I) : ContinualRealization I where
  Observation := realization.Observation
  Contradicts := fun _ => False
  problem := realization.problem
  status observation := StageStatus.ofLegacy (realization.decision observation)

end ContinualRealization

/-! ## Runtime receipt obligations -/

/-- An external receipt source enters the formal architecture only through caller-supplied problem
and status maps. A status may carry a witness, but this mapping alone does not admit that witness or
receipt into a closure history. -/
structure RuntimeBridge {N : Network} {R : Type w} (I : TradingInterface N R) where
  Receipt : Type t
  Contradicts : TradingProblem I → Prop
  problem : Receipt → TradingProblem I
  status : ∀ receipt, StageStatus Contradicts (problem receipt)

/-- Synonym emphasizing that the external runtime values may be signed or append-only receipts. -/
abbrev ReceiptBridge {N : Network} {R : Type w} (I : TradingInterface N R) := RuntimeBridge I

namespace RuntimeBridge

def toContinualRealization {N : Network} {R : Type w} {I : TradingInterface N R}
    (bridge : RuntimeBridge I) : ContinualRealization I where
  Observation := bridge.Receipt
  Contradicts := bridge.Contradicts
  problem := bridge.problem
  status := bridge.status

/-- Admission of one actual receipt requires its own local witness. -/
structure ReceiptAdmission {N : Network} {R : Type w} {I : TradingInterface N R}
    (bridge : RuntimeBridge I) (receipt : bridge.Receipt) where
  witness : LocalTradeWitness (bridge.problem receipt)
  status_witnessed : bridge.status receipt = .witnessed witness

namespace ReceiptAdmission

def stage {N : Network} {R : Type w} {I : TradingInterface N R}
    {bridge : RuntimeBridge I} {receipt : bridge.Receipt}
    (admission : ReceiptAdmission bridge receipt) : ClosureStage I where
  problem := bridge.problem receipt
  witness := admission.witness

def startHistory {N : Network} {R : Type w} {I : TradingInterface N R}
    {bridge : RuntimeBridge I} {receipt : bridge.Receipt}
    (admission : ReceiptAdmission bridge receipt) :
    ClosureHistory I admission.stage :=
  .start admission.stage

end ReceiptAdmission

/-- Appending one actual receipt additionally requires its local witness and boundary. -/
structure ReceiptExtension {N : Network} {R : Type w} {I : TradingInterface N R}
    {current : ClosureStage I} (_history : ClosureHistory I current)
    (bridge : RuntimeBridge I) where
  receipt : bridge.Receipt
  witness : LocalTradeWitness (bridge.problem receipt)
  status_witnessed : bridge.status receipt = .witnessed witness
  boundary : BoundaryMatches current.problem (bridge.problem receipt)

namespace ReceiptExtension

def toHistoryExtension {N : Network} {R : Type w} {I : TradingInterface N R}
    {current : ClosureStage I} {history : ClosureHistory I current}
    {bridge : RuntimeBridge I} (extension : ReceiptExtension history bridge) :
    ClosureHistory.Extension history where
  next := ⟨bridge.problem extension.receipt, extension.witness⟩
  boundary := extension.boundary

def extendHistory {N : Network} {R : Type w} {I : TradingInterface N R}
    {current : ClosureStage I} {history : ClosureHistory I current}
    {bridge : RuntimeBridge I} (extension : ReceiptExtension history bridge) :
    ClosureHistory I extension.toHistoryExtension.next :=
  history.extend extension.toHistoryExtension

end ReceiptExtension

end RuntimeBridge

/-! ## Stage-local empirical feedback -/

structure ContinualAssessment {N : Network} {R : Type w} {I : TradingInterface N R}
    (realization : ContinualRealization I) where
  Outcome : Type q
  gross : realization.Observation → Outcome
  costs : realization.Observation → Outcome
  netOf : Outcome → Outcome → Outcome
  positive : Outcome → Prop

namespace ContinualAssessment

def net {N : Network} {R : Type w} {I : TradingInterface N R}
    {realization : ContinualRealization I} (assessment : ContinualAssessment realization)
    (observation : realization.Observation) : assessment.Outcome :=
  assessment.netOf (assessment.gross observation) (assessment.costs observation)

def ofLegacy {N : Network} {R : Type w} {I : TradingInterface N R}
    {realization : TradingRealization I} (assessment : EmpiricalAssessment realization) :
    ContinualAssessment (ContinualRealization.ofLegacy realization) where
  Outcome := assessment.Outcome
  gross := assessment.gross
  costs := assessment.costs
  netOf := assessment.netOf
  positive := assessment.positive

end ContinualAssessment

/-- One actual feedback extension. Its assessed net, next observation, local witness and boundary
are all supplied at this stage; it contains no rule quantified over future observations. -/
structure FeedbackExtension {N : Network} {R : Type w} {I : TradingInterface N R}
    {current : ClosureStage I} (_history : ClosureHistory I current)
    {realization : ContinualRealization I} (assessment : ContinualAssessment realization)
    (observation : realization.Observation) where
  current_problem : current.problem = realization.problem observation
  current_status_witnessed :
    realization.status observation =
      .witnessed (LocalTradeWitness.transport current_problem current.witness)
  assessedNet : assessment.Outcome
  assessedNet_eq : assessedNet = assessment.net observation
  nextObservation : realization.Observation
  nextWitness : LocalTradeWitness (realization.problem nextObservation)
  next_status_witnessed :
    realization.status nextObservation = .witnessed nextWitness
  boundary : BoundaryMatches current.problem (realization.problem nextObservation)

namespace FeedbackExtension

def toHistoryExtension {N : Network} {R : Type w} {I : TradingInterface N R}
    {current : ClosureStage I} {history : ClosureHistory I current}
    {realization : ContinualRealization I} {assessment : ContinualAssessment realization}
    {observation : realization.Observation}
    (feedback : FeedbackExtension history assessment observation) :
    ClosureHistory.Extension history where
  next := ⟨realization.problem feedback.nextObservation, feedback.nextWitness⟩
  boundary := feedback.boundary

def extendHistory {N : Network} {R : Type w} {I : TradingInterface N R}
    {current : ClosureStage I} {history : ClosureHistory I current}
    {realization : ContinualRealization I} {assessment : ContinualAssessment realization}
    {observation : realization.Observation}
    (feedback : FeedbackExtension history assessment observation) :
    ClosureHistory I feedback.toHistoryExtension.next :=
  history.extend feedback.toHistoryExtension

/-- The possibility of feedback extension is an obligation, not a theorem of closure. -/
def CanFeedbackExtend {N : Network} {R : Type w} {I : TradingInterface N R}
    {current : ClosureStage I} (history : ClosureHistory I current)
    {realization : ContinualRealization I} (assessment : ContinualAssessment realization)
    (observation : realization.Observation) : Prop :=
  Nonempty (FeedbackExtension history assessment observation)

/-- A failed net assessment is retained in the supplied extension, and the old history remains an
exact prefix. This theorem does not produce such an extension. -/
theorem failed_net_retained {N : Network} {R : Type w} {I : TradingInterface N R}
    {current : ClosureStage I} {history : ClosureHistory I current}
    {realization : ContinualRealization I} {assessment : ContinualAssessment realization}
    {observation : realization.Observation}
    (feedback : FeedbackExtension history assessment observation)
    (failure : ¬ assessment.positive (assessment.net observation)) :
    (¬ assessment.positive feedback.assessedNet) ∧
      BoundaryMatches current.problem
        (realization.problem feedback.nextObservation) ∧
      ClosureHistory.HistoryPrefix history feedback.extendHistory := by
  have retainedFailure : ¬ assessment.positive feedback.assessedNet := by
    rw [feedback.assessedNet_eq]
    exact failure
  exact ⟨retainedFailure, feedback.boundary,
    ClosureHistory.extend_retains_prefix history feedback.toHistoryExtension⟩

end FeedbackExtension

/-! ## Profit remains an independently refutable bridge -/

def ClosureImpliesProfit {N : Network} {R : Type w} {I : TradingInterface N R}
    {realization : ContinualRealization I}
    (assessment : ContinualAssessment realization) : Prop :=
  ∀ observation, LocalTradeWitness (realization.problem observation) →
    assessment.positive (assessment.net observation)

theorem local_failure_refutes_closure_implies_profit {N : Network} {R : Type w}
    {I : TradingInterface N R} {realization : ContinualRealization I}
    (assessment : ContinualAssessment realization) (observation : realization.Observation)
    (witness : LocalTradeWitness (realization.problem observation))
    (failure : ¬ assessment.positive (assessment.net observation)) :
    ¬ ClosureImpliesProfit assessment := by
  intro bridge
  exact failure (bridge observation witness)

/-! ## Bundled append-only result -/

theorem nrrf766_answer {N : Network} {R : Type w} {I : TradingInterface N R}
    {current : ClosureStage I} (history : ClosureHistory I current)
    (extension : ClosureHistory.Extension history) :
    ClosureHistory.HistoryPrefix history (history.extend extension) ∧
    memory (history.extend extension).interactions
        (sourceReading (history.extend extension).initialStage.problem) =
      targetReading extension.next.problem ∧
    memory (history.extend extension).interactions
        (sourceReading (history.extend extension).initialStage.problem) ∈ N.shared ∧
    I.closureReturn
        (sourceReading (history.extend extension).initialStage.problem) =
      I.closureReturn (targetReading extension.next.problem) := by
  exact ⟨ClosureHistory.extend_retains_prefix history extension,
    ClosureHistory.extend_memory_eq_next_target history extension,
    ClosureHistory.extend_memory_shared history extension,
    ClosureHistory.extend_preserves_closureReturn history extension⟩

#print axioms NRRF766.nrrf766_answer
#print axioms NRRF766.FeedbackExtension.failed_net_retained
#print axioms NRRF766.local_failure_refutes_closure_implies_profit

end NRRF766
