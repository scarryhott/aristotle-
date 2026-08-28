import NRRFTradingLifeActionPotentialGlobalHairExecutor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Relativistically integrated trading signals and a command open to closure

This module removes an absolute price level, a preferred route name, and a supplied phase from the
signal interface.  A candidate carries only two dimensionless relative readings: action potential
and global hair.  Their difference is completed flow.  Candidates are integrated by comparison
inside one simultaneously observed field, and a signal closes only when one reciprocal route class
has a unique positive completed reading.

The command is deliberately partial.  Relational signal closure and authenticated execution
authority are independent fields.  With no authority the command is provably open; when authority
arrives, the same command closes exactly when the relational signal already closes.  Thus the
command itself is open to closure, without pretending that private authority can be derived from
public prices.
-/

namespace NRRFTradingRelativisticCommand

/-! ## Dimensionless relative candidates -/

/-- A routed presentation read only through dimensionless action and hair relations. -/
structure Candidate (Route : Type) where
  route : Route
  actionPotentialReturn : ℚ
  globalHairReturn : ℚ

/-- The completed relative flow. -/
def Candidate.completedReturn {Route : Type} (c : Candidate Route) : ℚ :=
  c.actionPotentialReturn - c.globalHairReturn

/-- Build the relative readings from one start, its zero-hair return, and its cost-completed return. -/
def Candidate.ofReturns {Route : Type} (route : Route) (start zeroHairFinal costFinal : ℚ) :
    Candidate Route where
  route := route
  actionPotentialReturn := zeroHairFinal / start - 1
  globalHairReturn := (zeroHairFinal - costFinal) / start

/-- The relative closure identity used by the executable overlay. -/
theorem Candidate.completedReturn_ofReturns {Route : Type} (route : Route)
    (start zeroHairFinal costFinal : ℚ) (start_ne : start ≠ 0) :
    (Candidate.ofReturns route start zeroHairFinal costFinal).completedReturn =
      costFinal / start - 1 := by
  simp only [ofReturns, completedReturn]
  field_simp
  ring

/-- A common nonzero rescaling changes no relative candidate reading. -/
theorem Candidate.ofReturns_scale {Route : Type} (route : Route)
    (start zeroHairFinal costFinal scale : ℚ) (start_ne : start ≠ 0) (scale_ne : scale ≠ 0) :
    Candidate.ofReturns route (scale * start) (scale * zeroHairFinal) (scale * costFinal) =
      Candidate.ofReturns route start zeroHairFinal costFinal := by
  have action : (scale * zeroHairFinal) / (scale * start) - 1 =
      zeroHairFinal / start - 1 := by
    field_simp
  have hair : (scale * zeroHairFinal - scale * costFinal) / (scale * start) =
      (zeroHairFinal - costFinal) / start := by
    field_simp
  simp only [ofReturns]
  rw [action, hair]

/-! ## Reciprocal topology and relative selection -/

/-- Route reversal is supplied as an involution; no PLUS/MINUS label is privileged. -/
structure RouteField (Route : Type) where
  inverse : Route → Route
  inverse_inverse : ∀ route, inverse (inverse route) = route

/-- Every observed routed presentation has its inverse potential inside the same field. -/
def ReciprocalClosed {Route : Type} (field : RouteField Route)
    (candidates : List (Candidate Route)) : Prop :=
  ∀ candidate ∈ candidates,
    ∃ potential ∈ candidates, potential.route = field.inverse candidate.route

/-- A candidate is selected only by its relation to the whole simultaneous field. -/
def UniquePositiveLeader {Route : Type} (candidates : List (Candidate Route))
    (candidate : Candidate Route) : Prop :=
  candidate ∈ candidates ∧
  0 < candidate.completedReturn ∧
  ∀ other ∈ candidates, other ≠ candidate →
    other.completedReturn < candidate.completedReturn

/-- Two distinct candidates cannot both be the unique relational leader. -/
theorem uniquePositiveLeader_unique {Route : Type} {candidates : List (Candidate Route)}
    {left right : Candidate Route}
    (hleft : UniquePositiveLeader candidates left)
    (hright : UniquePositiveLeader candidates right) : left = right := by
  by_contra different
  have right_lt_left := hleft.2.2 right hright.1 (Ne.symm different)
  have left_lt_right := hright.2.2 left hleft.1 different
  exact lt_asymm right_lt_left left_lt_right

/-- Signal closure is reciprocal topology together with a unique positive relational leader. -/
def SignalCloses {Route : Type} (field : RouteField Route)
    (candidates : List (Candidate Route)) : Prop :=
  ReciprocalClosed field candidates ∧
  ∃ candidate, UniquePositiveLeader candidates candidate

/-! ## The command is open to closure -/

/-- A command stage contains public relational evidence and, independently, optional authority. -/
structure CommandStage (Route Authority : Type) where
  field : RouteField Route
  candidates : List (Candidate Route)
  authority : Option Authority

/-- A command closes only when both the relational signal and execution authority close. -/
def CommandStage.Closes {Route Authority : Type} (command : CommandStage Route Authority) : Prop :=
  SignalCloses command.field command.candidates ∧
  ∃ authority, command.authority = some authority

/-- Open means precisely that the two-field command has not yet closed. -/
def CommandStage.Open {Route Authority : Type} (command : CommandStage Route Authority) : Prop :=
  ¬ command.Closes

/-- Add authority without rewriting the already-derived relational field. -/
def CommandStage.authorize {Route Authority : Type} (command : CommandStage Route Authority)
    (authority : Authority) : CommandStage Route Authority :=
  { command with authority := some authority }

/-- Public evidence alone can never manufacture an executable closed command. -/
theorem CommandStage.open_without_authority {Route Authority : Type}
    (field : RouteField Route) (candidates : List (Candidate Route)) :
    (CommandStage.mk field candidates none : CommandStage Route Authority).Open := by
  intro closed
  obtain ⟨_, authority, impossible⟩ := closed
  cases impossible

/-- Filling the authority field closes exactly when the relational field already closes. -/
theorem CommandStage.authorize_closes_iff {Route Authority : Type}
    (command : CommandStage Route Authority) (authority : Authority) :
    (command.authorize authority).Closes ↔
      SignalCloses command.field command.candidates := by
  simp [Closes, authorize]

/-- The command is genuinely open *to* closure: a closed signal plus later authority completes it. -/
theorem CommandStage.open_to_closure {Route Authority : Type}
    (command : CommandStage Route Authority)
    (signal : SignalCloses command.field command.candidates)
    (authority : Authority) :
    (command.authorize authority).Closes :=
  (command.authorize_closes_iff authority).2 signal

/-- Closing never changes the candidates: authority fills only its own missing interface. -/
@[simp] theorem CommandStage.authorize_candidates {Route Authority : Type}
    (command : CommandStage Route Authority) (authority : Authority) :
    (command.authorize authority).candidates = command.candidates := rfl

/-- Collected statement: relative scaling is invisible, the leader is forced by relation, public
evidence remains open, and later authority can close without changing that evidence. -/
theorem relativistic_signal_open_command_answer {Route Authority : Type}
    (route : Route) (start zeroHairFinal costFinal scale : ℚ)
    (start_ne : start ≠ 0) (scale_ne : scale ≠ 0)
    (field : RouteField Route) (candidates : List (Candidate Route))
    (signal : SignalCloses field candidates) (authority : Authority) :
    Candidate.ofReturns route (scale * start) (scale * zeroHairFinal) (scale * costFinal) =
        Candidate.ofReturns route start zeroHairFinal costFinal ∧
    (CommandStage.mk field candidates none : CommandStage Route Authority).Open ∧
    ((CommandStage.mk field candidates none : CommandStage Route Authority).authorize authority).Closes := by
  exact ⟨Candidate.ofReturns_scale route start zeroHairFinal costFinal scale start_ne scale_ne,
    CommandStage.open_without_authority field candidates,
    CommandStage.open_to_closure _ signal authority⟩

#print axioms Candidate.completedReturn_ofReturns
#print axioms Candidate.ofReturns_scale
#print axioms uniquePositiveLeader_unique
#print axioms CommandStage.open_without_authority
#print axioms CommandStage.open_to_closure
#print axioms relativistic_signal_open_command_answer

end NRRFTradingRelativisticCommand
