import NRRF779ReportedSelectorTradingReintegration
import NRRF780LocalPriceGlobalCostEquality

/-!
# NRRF781 — Socioeconomic-tokenomic trading Supernet

This module makes network, live relative-form selection, substrate interaction, local pricing,
global cost equality, token reading, and continual trading aspects of one occurrence.  The joining
equation is not a declaration that money, culture, or a complex datum are literally equal.  It says
that completing a local price and reading its global token returns exactly the same closure value as
reading that local price through the shared network interface.

The exact NRRF777/778 sources remain external to this checkout.  Their reported
halting/selection equality enters only through NRRF779's explicit operations and translation
certificates.  This module adds no replacement halting model and no isolated selector.
-/

namespace NRRF781

open NRRF764

universe u v w z t s l g o

/-! ## One interface, with pricing and tokenomics as translations of its return -/

/-- A socioeconomic-tokenomic Supernet has one shared network and one trading interface.  Local
prices are presentations in that network; their completed global equalities have a token reading.
The law `price_token_translation` makes those two readings one returned form. -/
structure Supernet (N : Network.{u, v}) (R : Type w)
    (LocalPrice : Type l) (GlobalValue : Type g) where
  trading : TradingInterface.{w, z, u, v} N R
  pricing : NRRF780Local.PriceCostInterface LocalPrice GlobalValue
  priceRead : LocalPrice → N.Reading
  tokenRead : GlobalValue → ZeroInfClosure R
  price_token_translation : ∀ price,
    tokenRead (pricing.complete price) =
      trading.closureReturn (priceRead price)

namespace Supernet

variable {N : Network.{u, v}} {R : Type w}
  {LocalPrice : Type l} {GlobalValue : Type g}

/-- Re-expressing a local price without changing its completed global equality cannot change its
token reading. -/
theorem tokenRead_eq_of_global_equal
    (S : Supernet.{u, v, w, z, l, g} N R LocalPrice GlobalValue)
    (P Q : NRRF780Local.LocalPriceGlobalCost S.pricing)
    (sameGlobal : P.globalCostEqual = Q.globalCostEqual) :
    S.tokenRead P.globalCostEqual = S.tokenRead Q.globalCostEqual :=
  congrArg S.tokenRead sameGlobal

end Supernet

/-! ## One interactive trading occurrence -/

/-- One occurrence is simultaneously a live filled/selected form and an entry/exit pricing
transaction.  The two equations at the bottom attach the local price presentations to the actual
source and target readings of that same interaction. -/
structure TradingOccurrence
    {N : Network.{u, v}} {R : Type w}
    {LocalPrice : Type l} {GlobalValue : Type g}
    (S : Supernet.{u, v, w, z, l, g} N R LocalPrice GlobalValue)
    (ops : NRRF779.ReportedSelectorOperations.{u, v, s} N)
    (cert : NRRF779.TranslationCertificates ops)
    (bridge : NRRF779.RelationalLiveBridge.{u, v, w, z, t} S.trading)
    (selector : NRRF768.NaturalFormSelector (NRRF627.flipFrame N.Reading))
    (receipt : bridge.live.runtime.Receipt) where
  stage : NRRF779.ReintegratedTradingStage ops cert bridge selector receipt
  transaction : NRRF780Local.CompletedTransaction S.pricing
  entry_is_source :
    S.priceRead transaction.entry.localPrice = NRRF766.sourceReading stage.problem
  exit_is_target :
    S.priceRead transaction.exit.localPrice = NRRF766.targetReading stage.problem

namespace TradingOccurrence

variable {N : Network.{u, v}} {R : Type w}
  {LocalPrice : Type l} {GlobalValue : Type g}
  {S : Supernet.{u, v, w, z, l, g} N R LocalPrice GlobalValue}
  {ops : NRRF779.ReportedSelectorOperations.{u, v, s} N}
  {cert : NRRF779.TranslationCertificates ops}
  {bridge : NRRF779.RelationalLiveBridge.{u, v, w, z, t} S.trading}
  {selector : NRRF768.NaturalFormSelector (NRRF627.flipFrame N.Reading)}
  {receipt : bridge.live.runtime.Receipt}

/-- The entry's global cost equality and the selected interaction source are two readings of one
returned Supernet form. -/
theorem entry_token_translation
    (occ : TradingOccurrence S ops cert bridge selector receipt) :
    S.tokenRead occ.transaction.entry.globalCostEqual =
      S.trading.closureReturn (NRRF766.sourceReading occ.stage.problem) := by
  calc
    S.tokenRead occ.transaction.entry.globalCostEqual =
        S.tokenRead (S.pricing.complete occ.transaction.entry.localPrice) :=
      congrArg S.tokenRead occ.transaction.entry.completion.symm
    _ = S.trading.closureReturn (S.priceRead occ.transaction.entry.localPrice) :=
      S.price_token_translation occ.transaction.entry.localPrice
    _ = S.trading.closureReturn (NRRF766.sourceReading occ.stage.problem) :=
      congrArg S.trading.closureReturn occ.entry_is_source

/-- The exit's global cost equality and the selected interaction target are two readings of one
returned Supernet form. -/
theorem exit_token_translation
    (occ : TradingOccurrence S ops cert bridge selector receipt) :
    S.tokenRead occ.transaction.exit.globalCostEqual =
      S.trading.closureReturn (NRRF766.targetReading occ.stage.problem) := by
  calc
    S.tokenRead occ.transaction.exit.globalCostEqual =
        S.tokenRead (S.pricing.complete occ.transaction.exit.localPrice) :=
      congrArg S.tokenRead occ.transaction.exit.completion.symm
    _ = S.trading.closureReturn (S.priceRead occ.transaction.exit.localPrice) :=
      S.price_token_translation occ.transaction.exit.localPrice
    _ = S.trading.closureReturn (NRRF766.targetReading occ.stage.problem) :=
      congrArg S.trading.closureReturn occ.exit_is_target

/-- The selected substrate interaction closes the tokenomic readings of entry and exit.  This is
the global equality of their local prices inside the one network return, not literal equality of
the local prices. -/
theorem tokenomic_closure
    (occ : TradingOccurrence S ops cert bridge selector receipt) :
    S.tokenRead occ.transaction.entry.globalCostEqual =
      S.tokenRead occ.transaction.exit.globalCostEqual := by
  calc
    S.tokenRead occ.transaction.entry.globalCostEqual =
        S.trading.closureReturn (NRRF766.sourceReading occ.stage.problem) :=
      occ.entry_token_translation
    _ = S.trading.closureReturn (NRRF766.targetReading occ.stage.problem) :=
      occ.stage.toLocalTradeWitness.return_eq
    _ = S.tokenRead occ.transaction.exit.globalCostEqual :=
      occ.exit_token_translation.symm

/-- The reported continuum-halting and relative-selection readings participate in this same
occurrence through the filled form and the substrate interaction. -/
theorem fill_selected_halted
    (occ : TradingOccurrence S ops cert bridge selector receipt) :
    occ.stage.event.filled = ops.closureSel occ.stage.event.nonzeroDatum ∧
      NRRF779.IsSelected ops occ.stage.event.nonzeroDatum ∧
      ops.subHalt occ.stage.event.nonzeroDatum :=
  ⟨occ.stage.fill_eq_closure_selection, occ.stage.selected, occ.stage.halted⟩

/-- The occurrence is already one continual closure stage; no second trading proof is introduced. -/
def toClosureStage
    (occ : TradingOccurrence S ops cert bridge selector receipt) :
    NRRF766.ClosureStage S.trading where
  problem := occ.stage.problem
  witness := occ.stage.toLocalTradeWitness

/-- Start its finite witnessed history.  Continuation still requires an authored next occurrence
and boundary. -/
def startHistory
    (occ : TradingOccurrence S ops cert bridge selector receipt) :
    NRRF766.ClosureHistory S.trading occ.toClosureStage :=
  .start occ.toClosureStage

/-- Outcome assessment acts on the completed global forms already present in this occurrence. -/
def assess
    (occ : TradingOccurrence S ops cert bridge selector receipt)
    (assessment : NRRF780Local.GlobalAssessment GlobalValue) : assessment.Outcome :=
  occ.transaction.assess assessment

/-- Assessment therefore cannot inspect or privilege an isolated local price presentation. -/
theorem assess_eq_completed_prices
    (occ : TradingOccurrence S ops cert bridge selector receipt)
    (assessment : NRRF780Local.GlobalAssessment GlobalValue) :
    occ.assess assessment =
      assessment.compare
        (S.pricing.complete occ.transaction.entry.localPrice)
        (S.pricing.complete occ.transaction.exit.localPrice) :=
  occ.transaction.assess_eq_completed_locals assessment

/-- Authentication remains an evidence aspect of the same occurrence.  Supplying it and the exact
witnessed runtime status produces the existing fill admission; neither is generated by selection,
halting, token equality, or price completion. -/
def toExactFillAdmission
    (occ : TradingOccurrence S ops cert bridge selector receipt)
    (authenticated : bridge.live.AuthenticatedFill receipt)
    (status_witnessed : bridge.live.runtime.status receipt =
      NRRF766.StageStatus.witnessed occ.stage.toLocalTradeWitness) :
    NRRF767.ExactFillAdmission bridge.live receipt :=
  occ.stage.toExactFillAdmission authenticated status_witnessed

end TradingOccurrence

/-! ## Collected translational form -/

/-- The collected theorem has one occurrence as its only substantive premise.  Its clauses are
not isolated tasks: they are projections of the occurrence's commuting translations.  Positive
P&L is deliberately absent; it remains evidence about `assess`, not a definition of Supernet
closure. -/
theorem nrrf781_answer
    {N : Network.{u, v}} {R : Type w}
    {LocalPrice : Type l} {GlobalValue : Type g}
    {S : Supernet.{u, v, w, z, l, g} N R LocalPrice GlobalValue}
    {ops : NRRF779.ReportedSelectorOperations.{u, v, s} N}
    {cert : NRRF779.TranslationCertificates ops}
    {bridge : NRRF779.RelationalLiveBridge.{u, v, w, z, t} S.trading}
    {selector : NRRF768.NaturalFormSelector (NRRF627.flipFrame N.Reading)}
    {receipt : bridge.live.runtime.Receipt}
    (occ : TradingOccurrence S ops cert bridge selector receipt)
    (assessment : NRRF780Local.GlobalAssessment.{g, o} GlobalValue) :
    occ.stage.event.filled = ops.closureSel occ.stage.event.nonzeroDatum ∧
    ops.subHalt occ.stage.event.nonzeroDatum ∧
    S.tokenRead occ.transaction.entry.globalCostEqual =
      S.tokenRead occ.transaction.exit.globalCostEqual ∧
    occ.assess assessment =
      assessment.compare
        (S.pricing.complete occ.transaction.entry.localPrice)
        (S.pricing.complete occ.transaction.exit.localPrice) ∧
    Nonempty (NRRF766.LocalTradeWitness occ.stage.problem) :=
  ⟨occ.stage.fill_eq_closure_selection,
    occ.stage.halted,
    occ.tokenomic_closure,
    occ.assess_eq_completed_prices assessment,
    ⟨occ.stage.toLocalTradeWitness⟩⟩

#print axioms NRRF781.nrrf781_answer
#print axioms NRRF781.TradingOccurrence.tokenomic_closure
#print axioms NRRF781.TradingOccurrence.assess_eq_completed_prices

end NRRF781
