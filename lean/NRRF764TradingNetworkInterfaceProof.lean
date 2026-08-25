import NRRF764ConsciousCulturalMoralitySuperNetwork
import NRRF627ClosureTranslationalFrameworkAxiometryASIEvolutionaryVerification

/-!
# NRRF764 trading adapter — Network, Interface, Proof

The formal chain is
`Network → TradingInterface → TradingProblem → TradeProof → continued memory`.

A proof must exhibit an admissible network interaction, show that it preserves the interface's
closure return, and close through the actual NRRF627 `flipFrame` translation. Polar equality is
then derived; it is not a second unrelated assumption. Empirical gross outcome, costs and
positivity remain an explicit falsifiable layer.
-/

namespace NRRF764

universe u v w z t

/-! ## One coherent Network–Interface presentation -/

/-- Turn an NRRF627 pole into its NRRF764 polar presentation at radius `r`. -/
def polarPresentation {R : Type w} : NRRF627.Pole → R → PolarPoint R
  | .zero, r => zero r
  | .inf, r => infinity r

/-- A quote presents one network site inside one language of the NRRF627 two-language frame. Its
network reading and polar presentation are required to have the same closure return. -/
structure TradingInterface (N : Network) (R : Type w) where
  Quote : Type z
  site : Quote → N.Site
  perspective : Quote → Bool
  orientation : Quote → NRRF627.Pole
  radius : Quote → R
  closureReturn : N.Reading → ZeroInfClosure R
  quote_coherent : ∀ q,
    closureReturn (N.read (site q)) =
      Quotient.mk (polarSetoid R) (polarPresentation (orientation q) (radius q))

namespace TradingInterface

/-- Geometry is derived from orientation and radius; it cannot disagree with them. -/
def geometry {N : Network} {R : Type w} (I : TradingInterface N R) (q : I.Quote) :
    PolarPoint R :=
  polarPresentation (I.orientation q) (I.radius q)

/-- The quote as an occurrence in the repository's NRRF627 `flipFrame`. -/
def occurrence {N : Network} {R : Type w} (I : TradingInterface N R) (q : I.Quote) :
    N.Reading × NRRF627.Pole :=
  (N.read (I.site q), I.orientation q)

end TradingInterface

/-- A proposed trade is an oriented pair of interface quotes. -/
structure TradingProblem {N : Network} {R : Type w} (I : TradingInterface N R) where
  source : I.Quote
  target : I.Quote

namespace TradingProblem

def sourceProblem {N : Network} {R : Type w} {I : TradingInterface N R}
    (P : TradingProblem I) : RealProblem N :=
  ⟨N.read (I.site P.source), N.read_shared _⟩

def targetProblem {N : Network} {R : Type w} {I : TradingInterface N R}
    (P : TradingProblem I) : RealProblem N :=
  ⟨N.read (I.site P.target), N.read_shared _⟩

end TradingProblem

/-! ## Proof closes the two returns through one frame translation -/

/-- `closure_natural` relates network interaction to interface return. `frame_closes` routes the
translated reading and orientation through the actual NRRF627 occurrence translation. -/
structure TradeProof {N : Network} {R : Type w} {I : TradingInterface N R}
    (P : TradingProblem I) where
  interaction : Interaction N
  closure_natural : ∀ r,
    I.closureReturn (interaction.translate r) = I.closureReturn r
  frame_closes :
    (NRRF627.flipFrame N.Reading).T
        (I.perspective P.source) (I.perspective P.target)
        (interaction.translate (N.read (I.site P.source)), I.orientation P.source) =
      I.occurrence P.target

namespace TradeProof

/-- The full occurrence equation entails translation of the network reading. -/
theorem translates {N : Network} {R : Type w} {I : TradingInterface N R}
    {P : TradingProblem I} (proof : TradeProof P) :
    proof.interaction.translate (N.read (I.site P.source)) =
      N.read (I.site P.target) := by
  have h := congrArg Prod.fst proof.frame_closes
  simpa [NRRF627.flipFrame, TradingInterface.occurrence] using h

/-- Interface coherence and return naturality derive equality of polar quotient images. -/
theorem geometry_quotient_eq {N : Network} {R : Type w} {I : TradingInterface N R}
    {P : TradingProblem I} (proof : TradeProof P) :
    Quotient.mk (polarSetoid R) (I.geometry P.source) =
      Quotient.mk (polarSetoid R) (I.geometry P.target) := by
  calc
    Quotient.mk (polarSetoid R) (I.geometry P.source) =
        I.closureReturn (N.read (I.site P.source)) :=
      (I.quote_coherent P.source).symm
    _ = I.closureReturn
        (proof.interaction.translate (N.read (I.site P.source))) :=
      (proof.closure_natural _).symm
    _ = I.closureReturn (N.read (I.site P.target)) :=
      congrArg I.closureReturn proof.translates
    _ = Quotient.mk (polarSetoid R) (I.geometry P.target) :=
      I.quote_coherent P.target

/-- Polar closure is derived from quotient equality. -/
theorem geometry_closes {N : Network} {R : Type w} {I : TradingInterface N R}
    {P : TradingProblem I} (proof : TradeProof P) :
    PolarRel (I.geometry P.source) (I.geometry P.target) :=
  Quotient.exact proof.geometry_quotient_eq

end TradeProof

/-- Quotient equality is exactly the polar relation, in both directions. -/
theorem geometry_quotient_iff {N : Network} {R : Type w} (I : TradingInterface N R)
    (q₁ q₂ : I.Quote) :
    Quotient.mk (polarSetoid R) (I.geometry q₁) =
        Quotient.mk (polarSetoid R) (I.geometry q₂) ↔
      PolarRel (I.geometry q₁) (I.geometry q₂) :=
  ⟨Quotient.exact, fun h => @Quotient.sound _ (polarSetoid R) _ _ h⟩

/-- A complete trade retains its interface as a parameter and contains its problem and proof. -/
structure ClosedTrade {N : Network} {R : Type w} (I : TradingInterface N R) where
  problem : TradingProblem I
  proof : TradeProof problem

def IsClosed {N : Network} {R : Type w} {I : TradingInterface N R}
    (P : TradingProblem I) : Prop :=
  Nonempty (TradeProof P)

/-- `OPEN` is the strong proposition that no closing proof exists for this interface and problem;
mere absence of a proof in hand is not silently promoted to `OPEN`. -/
def IsOpen {N : Network} {R : Type w} {I : TradingInterface N R}
    (P : TradingProblem I) : Prop :=
  ¬ IsClosed P

/-- `CONTRADICTED` means the reciprocal polar relation itself fails. -/
def IsContradicted {N : Network} {R : Type w} {I : TradingInterface N R}
    (P : TradingProblem I) : Prop :=
  ¬ PolarRel (I.geometry P.source) (I.geometry P.target)

theorem contradicted_is_open {N : Network} {R : Type w} {I : TradingInterface N R}
    (P : TradingProblem I) (h : IsContradicted P) : IsOpen P := by
  intro hclosed
  rcases hclosed with ⟨proof⟩
  exact h proof.geometry_closes

theorem closed_not_open {N : Network} {R : Type w} {I : TradingInterface N R}
    (P : TradingProblem I) (hclosed : IsClosed P) : ¬ IsOpen P :=
  fun hopen => hopen hclosed

theorem contradicted_not_open_uncontradicted {N : Network} {R : Type w}
    {I : TradingInterface N R} (P : TradingProblem I) (h : IsContradicted P) :
    ¬ (IsOpen P ∧ ¬ IsContradicted P) :=
  fun hopen => hopen.2 h

/-! ## Consequences of a closed trade -/

theorem trade_source_shared {N : Network} {R : Type w} {I : TradingInterface N R}
    (T : ClosedTrade I) : N.read (I.site T.problem.source) ∈ N.shared :=
  N.read_shared _

theorem trade_target_shared {N : Network} {R : Type w} {I : TradingInterface N R}
    (T : ClosedTrade I) : N.read (I.site T.problem.target) ∈ N.shared :=
  N.read_shared _

theorem trade_memory_eq_target {N : Network} {R : Type w} {I : TradingInterface N R}
    (T : ClosedTrade I) :
    memory [T.proof.interaction] (N.read (I.site T.problem.source)) =
      N.read (I.site T.problem.target) := by
  rw [interaction_as_one_step_memory]
  exact T.proof.translates

theorem trade_memory_shared {N : Network} {R : Type w} {I : TradingInterface N R}
    (T : ClosedTrade I) :
    memory [T.proof.interaction] (N.read (I.site T.problem.source)) ∈ N.shared :=
  memory_admissible _ (trade_source_shared T)

/-- Genuine use of the NRRF627 frame return and occurrence translation, not `CEq id`. -/
theorem trade_translation_is_nrrf627_closure {N : Network} {R : Type w}
    {I : TradingInterface N R} (T : ClosedTrade I) :
    NRRF627.CEq
        ((NRRF627.flipFrame N.Reading).W (I.perspective T.problem.target))
        ((NRRF627.flipFrame N.Reading).T
          (I.perspective T.problem.source) (I.perspective T.problem.target)
          (T.proof.interaction.translate (N.read (I.site T.problem.source)),
            I.orientation T.problem.source))
        (I.occurrence T.problem.target) := by
  unfold NRRF627.CEq
  rw [T.proof.frame_closes]

theorem trade_geometry_quotient_eq {N : Network} {R : Type w}
    {I : TradingInterface N R} (T : ClosedTrade I) :
    Quotient.mk (polarSetoid R) (I.geometry T.problem.source) =
      Quotient.mk (polarSetoid R) (I.geometry T.problem.target) :=
  T.proof.geometry_quotient_eq

theorem trade_geometry_closes {N : Network} {R : Type w}
    {I : TradingInterface N R} (T : ClosedTrade I) :
    PolarRel (I.geometry T.problem.source) (I.geometry T.problem.target) :=
  T.proof.geometry_closes

namespace ClosedTrade

def sourceReading {N : Network} {R : Type w} {I : TradingInterface N R}
    (T : ClosedTrade I) : N.Reading :=
  N.read (I.site T.problem.source)

def targetReading {N : Network} {R : Type w} {I : TradingInterface N R}
    (T : ClosedTrade I) : N.Reading :=
  N.read (I.site T.problem.target)

end ClosedTrade

/-- A list of closed trades is composable from `initial` only when every interaction receives the
source it proved and every target feeds the next source. -/
def ClosedHistoryComposable {N : Network} {R : Type w} {I : TradingInterface N R} :
    N.Reading → List (ClosedTrade I) → Prop
  | _, [] => True
  | initial, T :: history =>
      initial = T.sourceReading ∧ ClosedHistoryComposable T.targetReading history

def closedHistoryTarget {N : Network} {R : Type w} {I : TradingInterface N R} :
    N.Reading → List (ClosedTrade I) → N.Reading
  | initial, [] => initial
  | _, T :: history => closedHistoryTarget T.targetReading history

def closedHistoryInteractions {N : Network} {R : Type w} {I : TradingInterface N R}
    (history : List (ClosedTrade I)) : List (Interaction N) :=
  history.map fun T => T.proof.interaction

/-- A composable history is continuous closure: executing it reaches its recursively defined final
target, rather than merely applying individually valid interactions to unrelated inputs. -/
theorem closedHistory_memory_eq_target {N : Network} {R : Type w}
    {I : TradingInterface N R} (history : List (ClosedTrade I)) {initial : N.Reading}
    (hcomposable : ClosedHistoryComposable initial history) :
    memory (closedHistoryInteractions history) initial =
      closedHistoryTarget initial history := by
  induction history generalizing initial with
  | nil => rfl
  | cons T history ih =>
      rcases hcomposable with ⟨hsource, hrest⟩
      change memory (closedHistoryInteractions history)
          (T.proof.interaction.translate initial) =
        closedHistoryTarget T.targetReading history
      have hstep : T.proof.interaction.translate initial = T.targetReading := by
        rw [hsource]
        exact T.proof.translates
      rw [hstep]
      exact ih hrest

/-! ## A concrete non-vacuous reciprocal trade -/

def polarInteraction {R : Type w} (r : R) : Interaction (polesNetwork r) where
  translate := polar
  admissible := by
    intro _ _
    trivial
  moral_natural := by
    intro _
    rfl

def polesTradingInterface {R : Type w} (r : R) : TradingInterface (polesNetwork r) R where
  Quote := Bool
  site := fun b => b
  perspective := fun b => b
  orientation := fun b => if b then .inf else .zero
  radius := fun _ => r
  closureReturn := fun x => Quotient.mk (polarSetoid R) x
  quote_coherent := by
    intro b
    cases b <;> rfl

def polesTradeProblem {R : Type w} (r : R) : TradingProblem (polesTradingInterface r) where
  source := false
  target := true

def polesTradeProof {R : Type w} (r : R) : TradeProof (polesTradeProblem r) where
  interaction := polarInteraction r
  closure_natural := by
    intro x
    apply Quotient.sound
    exact Or.inr (polar_involutive x).symm
  frame_closes := rfl

def polesClosedTrade {R : Type w} (r : R) : ClosedTrade (polesTradingInterface r) where
  problem := polesTradeProblem r
  proof := polesTradeProof r

theorem polar_trade_nonvacuous {R : Type w} (r : R) :
    IsClosed (polesTradeProblem r) :=
  ⟨polesTradeProof r⟩

/-! ## Observations carry proof/open/contradicted decisions -/

inductive TradeDecision {N : Network} {R : Type w} {I : TradingInterface N R}
    (P : TradingProblem I) where
  | closed (proof : TradeProof P)
  | contradicted (proof : IsContradicted P)
  | open_uncontradicted (open_proof : IsOpen P)
      (not_contradicted : ¬ IsContradicted P)

namespace TradeDecision

def interaction? {N : Network} {R : Type w} {I : TradingInterface N R}
    {P : TradingProblem I} : TradeDecision P → Option (Interaction N)
  | .closed proof => some proof.interaction
  | .contradicted _ => none
  | .open_uncontradicted _ _ => none

def closedTrade? {N : Network} {R : Type w} {I : TradingInterface N R}
    {P : TradingProblem I} : TradeDecision P → Option (ClosedTrade I)
  | .closed proof => some ⟨P, proof⟩
  | .contradicted _ => none
  | .open_uncontradicted _ _ => none

end TradeDecision

/-- Every observation supplies one problem and a proof-bearing decision about that problem. -/
structure TradingRealization {N : Network} {R : Type w} (I : TradingInterface N R) where
  Observation : Type t
  problem : Observation → TradingProblem I
  decision : ∀ o, TradeDecision (problem o)

def realizedClosedTrades {N : Network} {R : Type w} {I : TradingInterface N R}
    (E : TradingRealization I) (history : List E.Observation) : List (ClosedTrade I) :=
  history.filterMap fun o => (E.decision o).closedTrade?

def realizedInteractions {N : Network} {R : Type w} {I : TradingInterface N R}
    (E : TradingRealization I) (history : List E.Observation) : List (Interaction N) :=
  closedHistoryInteractions (realizedClosedTrades E history)

def realizedMemory {N : Network} {R : Type w} {I : TradingInterface N R}
    (E : TradingRealization I) (history : List E.Observation) (initial : N.Reading) :
    N.Reading :=
  memory (realizedInteractions E history) initial

def realizedConnection {N : Network} {R : Type w} {I : TradingInterface N R}
    (E : TradingRealization I) (history : List E.Observation) : Multiset (Interaction N) :=
  connection (realizedInteractions E history)

theorem realizedMemory_shared {N : Network} {R : Type w} {I : TradingInterface N R}
    (E : TradingRealization I) (history : List E.Observation) {initial : N.Reading}
    (hshared : initial ∈ N.shared) : realizedMemory E history initial ∈ N.shared :=
  memory_admissible _ hshared

/-- A realized history closes continuously only with the explicit adjacency condition. -/
def RealizedHistoryComposable {N : Network} {R : Type w} {I : TradingInterface N R}
    (E : TradingRealization I) (history : List E.Observation) (initial : N.Reading) : Prop :=
  ClosedHistoryComposable initial (realizedClosedTrades E history)

def realizedFinalTarget {N : Network} {R : Type w} {I : TradingInterface N R}
    (E : TradingRealization I) (history : List E.Observation) (initial : N.Reading) :
    N.Reading :=
  closedHistoryTarget initial (realizedClosedTrades E history)

/-- Under composability, realized memory reaches the final proved target. -/
theorem realizedMemory_eq_finalTarget {N : Network} {R : Type w}
    {I : TradingInterface N R} (E : TradingRealization I)
    (history : List E.Observation) {initial : N.Reading}
    (hcomposable : RealizedHistoryComposable E history initial) :
    realizedMemory E history initial = realizedFinalTarget E history initial :=
  closedHistory_memory_eq_target _ hcomposable

theorem realizedInteractions_append {N : Network} {R : Type w}
    {I : TradingInterface N R} (E : TradingRealization I)
    (xs ys : List E.Observation) :
    realizedInteractions E (xs ++ ys) =
      realizedInteractions E xs ++ realizedInteractions E ys := by
  simp [realizedInteractions, realizedClosedTrades, closedHistoryInteractions]

theorem realizedConnection_append {N : Network} {R : Type w}
    {I : TradingInterface N R} (E : TradingRealization I)
    (xs ys : List E.Observation) :
    realizedConnection E (xs ++ ys) =
      realizedConnection E xs + realizedConnection E ys := by
  unfold realizedConnection
  rw [realizedInteractions_append, conn_append]

/-! ## Empirical profitability is attached to realized observations -/

/-- The outcome carrier and its operations remain explicit empirical inputs. -/
structure EmpiricalAssessment {N : Network} {R : Type w} {I : TradingInterface N R}
    (E : TradingRealization I) where
  Outcome : Type u
  gross : E.Observation → Outcome
  costs : E.Observation → Outcome
  netOf : Outcome → Outcome → Outcome
  positive : Outcome → Prop

namespace EmpiricalAssessment

def net {N : Network} {R : Type w} {I : TradingInterface N R}
    {E : TradingRealization I} (A : EmpiricalAssessment E) (o : E.Observation) : A.Outcome :=
  A.netOf (A.gross o) (A.costs o)

def PositiveBridge {N : Network} {R : Type w} {I : TradingInterface N R}
    {E : TradingRealization I} (A : EmpiricalAssessment E) (o : E.Observation) : Prop :=
  A.positive (A.net o)

/-- Positivity is asserted only for observations whose formal problem closes. -/
def ValidatedPositiveBridge {N : Network} {R : Type w} {I : TradingInterface N R}
    {E : TradingRealization I} (A : EmpiricalAssessment E) : Prop :=
  ∀ o, IsClosed (E.problem o) → A.PositiveBridge o

/-- One closed observation with failed net positivity refutes the proposed empirical bridge. -/
theorem observed_failure_refutes_validated_bridge {N : Network} {R : Type w}
    {I : TradingInterface N R} {E : TradingRealization I} (A : EmpiricalAssessment E)
    (o : E.Observation) (hclosed : IsClosed (E.problem o))
    (hfailure : ¬ A.PositiveBridge o) : ¬ A.ValidatedPositiveBridge := by
  intro hbridge
  exact hfailure (hbridge o hclosed)

end EmpiricalAssessment

/-! ## Bundled answer -/

/-- The result contains no profitability conclusion and does not mislabel ambient terminality as
a consequence of one trade. -/
theorem nrrf764_trading_answer {N : Network} {R : Type w}
    {I : TradingInterface N R} (T : ClosedTrade I) :
    N.read (I.site T.problem.source) ∈ N.shared ∧
    N.read (I.site T.problem.target) ∈ N.shared ∧
    memory [T.proof.interaction] (N.read (I.site T.problem.source)) =
      N.read (I.site T.problem.target) ∧
    NRRF627.CEq
        ((NRRF627.flipFrame N.Reading).W (I.perspective T.problem.target))
        ((NRRF627.flipFrame N.Reading).T
          (I.perspective T.problem.source) (I.perspective T.problem.target)
          (T.proof.interaction.translate (N.read (I.site T.problem.source)),
            I.orientation T.problem.source))
        (I.occurrence T.problem.target) ∧
    Quotient.mk (polarSetoid R) (I.geometry T.problem.source) =
      Quotient.mk (polarSetoid R) (I.geometry T.problem.target) ∧
    PolarRel (I.geometry T.problem.source) (I.geometry T.problem.target) := by
  exact ⟨trade_source_shared T, trade_target_shared T, trade_memory_eq_target T,
    trade_translation_is_nrrf627_closure T, trade_geometry_quotient_eq T,
    trade_geometry_closes T⟩

#print axioms NRRF764.nrrf764_trading_answer
#print axioms NRRF764.polar_trade_nonvacuous
#print axioms NRRF764.EmpiricalAssessment.observed_failure_refutes_validated_bridge

end NRRF764
