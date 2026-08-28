import NRRFTradingTranslationFirstLifeLocalBallInfGlobalHairZeroExecutor

/-!
# Trading signals derived as relations through interaction

NRRF806 correctly made global hair the residual of the closure equation, but its runtime operands
were still derived inside one presentation, so zero tested accounting only.  This module separates
two temporal readings:

* `priorPotential` is committed by the local-ball reactor at stage `t`;
* `realizedPotential` is read from a later, independently presented interaction at `t+1`.

Local hair translates the later zero-hair realization into its completed result.  Global hair then
compares that completed interaction against the *prior* potential.  Under the independently checked
local accounting equation, global hair is exactly `realizedPotential - priorPotential`; its zero is
therefore equivalent to preservation of the signal through interaction, not true by construction.
-/

namespace NRRFTradingInteractiveSignal

open NRRF800
open NRRFTradingTranslationFirstLife

/-- One prior commitment and one later realized interaction. -/
structure InteractiveFlow where
  priorPotential : ℚ
  realizedPotential : ℚ
  localHair : ℚ
  completed : ℚ

/-- The later interaction accounts locally for its own hair. -/
def InteractiveFlow.AccountingCloses (flow : InteractiveFlow) : Prop :=
  flow.completed = flow.realizedPotential - flow.localHair

instance (flow : InteractiveFlow) : Decidable flow.AccountingCloses :=
  inferInstanceAs (Decidable (flow.completed = flow.realizedPotential - flow.localHair))

/-- The signal relation is derived across stages: the later realization preserves the prior form. -/
def InteractiveFlow.SignalRel (flow : InteractiveFlow) : Prop :=
  flow.realizedPotential = flow.priorPotential

/-- Global hair is the residual against the prior committed potential. -/
def InteractiveFlow.globalHair (flow : InteractiveFlow) : ℚ :=
  flow.completed - (flow.priorPotential - flow.localHair)

/-- Once the later interaction accounts for local hair, global hair is the temporal potential gap. -/
theorem InteractiveFlow.globalHair_eq_realized_sub_prior (flow : InteractiveFlow)
    (accounting : flow.AccountingCloses) :
    flow.globalHair = flow.realizedPotential - flow.priorPotential := by
  simp only [globalHair, AccountingCloses] at *
  rw [accounting]
  ring

/-- Global hair zero now tests preservation through interaction, not a single-stage identity. -/
theorem InteractiveFlow.globalHair_eq_zero_iff_signalRel (flow : InteractiveFlow)
    (accounting : flow.AccountingCloses) :
    flow.globalHair = 0 ↔ flow.SignalRel := by
  rw [flow.globalHair_eq_realized_sub_prior accounting]
  change flow.realizedPotential - flow.priorPotential = 0 ↔
    flow.realizedPotential = flow.priorPotential
  exact sub_eq_zero

inductive Verdict
  | hold
  | admit
  deriving DecidableEq, Repr

/-- Admit only when both later accounting and the cross-stage global-hair relation close. -/
def executor (flow : InteractiveFlow) : Verdict :=
  if flow.AccountingCloses ∧ flow.globalHair = 0 then .admit else .hold

theorem executor_admit_iff (flow : InteractiveFlow) :
    executor flow = .admit ↔ flow.AccountingCloses ∧ flow.SignalRel := by
  unfold executor
  by_cases closed : flow.AccountingCloses
  · simpa [closed] using flow.globalHair_eq_zero_iff_signalRel closed
  · simp [closed]

/-- Local accounting can close while the interactive signal relation fails. -/
theorem accounting_does_not_force_interactive_closure :
    ∃ flow : InteractiveFlow,
      flow.AccountingCloses ∧ flow.globalHair ≠ 0 ∧ executor flow = .hold := by
  refine ⟨⟨0, 1, 0, 1⟩, by norm_num [InteractiveFlow.AccountingCloses], ?_, ?_⟩
  · norm_num [InteractiveFlow.globalHair]
  · norm_num [executor, InteractiveFlow.AccountingCloses, InteractiveFlow.globalHair]

/-- The two temporal sides use the existing action and inverse-potential continuations. -/
structure Interaction where
  priorLife : Life
  laterLife : Life
  flow : InteractiveFlow

def Interaction.action (interaction : Interaction) : Life :=
  ballReturn interaction.priorLife

def Interaction.potential (interaction : Interaction) : Life :=
  hairReturn interaction.laterLife

def Interaction.priorReactor (interaction : Interaction) : Set Life :=
  LocalBallInf interaction.priorLife

def Interaction.laterReactor (interaction : Interaction) : Set Life :=
  LocalBallInf interaction.laterLife

theorem Interaction.action_mem_priorReactor (interaction : Interaction) :
    interaction.action ∈ interaction.priorReactor :=
  action_mem_localBallInf interaction.priorLife

theorem Interaction.potential_mem_laterReactor (interaction : Interaction) :
    interaction.potential ∈ interaction.laterReactor :=
  potential_mem_localBallInf interaction.laterLife

/-- Collected result: action and potential belong to their temporal reactors, and zero global hair
is admitted exactly when later accounting closes and the later potential preserves the committed
prior signal. -/
theorem derived_interactive_signal_answer (interaction : Interaction) :
    interaction.action ∈ interaction.priorReactor ∧
    interaction.potential ∈ interaction.laterReactor ∧
    (executor interaction.flow = .admit ↔
      interaction.flow.AccountingCloses ∧ interaction.flow.SignalRel) := by
  exact ⟨interaction.action_mem_priorReactor, interaction.potential_mem_laterReactor,
    executor_admit_iff interaction.flow⟩

#print axioms InteractiveFlow.globalHair_eq_realized_sub_prior
#print axioms InteractiveFlow.globalHair_eq_zero_iff_signalRel
#print axioms executor_admit_iff
#print axioms accounting_does_not_force_interactive_closure
#print axioms derived_interactive_signal_answer

end NRRFTradingInteractiveSignal
