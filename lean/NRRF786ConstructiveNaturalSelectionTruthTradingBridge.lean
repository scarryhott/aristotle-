import NRRF783RelativePotentialClassicalFlowSupernetBridge

/-!
# NRRF786 — Constructive natural selection and orbit truth in trading

The reported NRRF783–785 constructive sources are not present in this checkout.  This module names
only their downstream surface and proves how it constrains the NRRF783 temporal trading bridge.

Selection and partial truth are invariant under supplied level shifts.  Resource cost is absent
from their definition and enters only in the classical temporal-flow assessment.  Consequently a
natural selected flow is profitable only when its relative potential moves beyond cost and its
endpoints occupy distinct returned-token/translational-closure classes.
-/

namespace NRRF786

open NRRF764

universe u v w z l g p f k

/-! ## Choice-free surface of the reported constructive naturality results -/

/-- The exact consequences needed from NRRF784/785.  A level shift acts on completed global forms;
the selector, partial truth, and returned token are all natural under that action.  No metric or
minimization operation occurs in this structure. -/
structure NaturalSelectionTruth
    {N : Network.{u, v}} {R : Type w}
    {LocalPrice : Type l} {GlobalValue : Type g}
    (S : NRRF781.Supernet.{u, v, w, z, l, g} N R LocalPrice GlobalValue) where
  LevelShift : Type k
  shift : LevelShift → GlobalValue → GlobalValue
  selected : GlobalValue → Prop
  orbitTruth : GlobalValue → Option Bool
  token_natural : ∀ level value,
    S.tokenRead (shift level value) = S.tokenRead value
  selected_natural : ∀ level value,
    selected (shift level value) ↔ selected value
  truth_natural : ∀ level value,
    orbitTruth (shift level value) = orbitTruth value

namespace NaturalSelectionTruth

variable {N : Network.{u, v}} {R : Type w}
  {LocalPrice : Type l} {GlobalValue : Type g}
  {S : NRRF781.Supernet.{u, v, w, z, l, g} N R LocalPrice GlobalValue}
  {potentialBridge : NRRF783.RelativePotentialBridge.{u, v, w, z, l, g, p} S}

/-- Naturality of the returned token forces naturality of the complete relative-potential field. -/
theorem potential_natural
    (surface : NaturalSelectionTruth.{u, v, w, z, l, g, k} S)
    (level : surface.LevelShift) (value : GlobalValue) :
    potentialBridge.potential (surface.shift level value) =
      potentialBridge.potential value :=
  (potentialBridge.token_eq_iff_potential_eq _ _).mp
    (surface.token_natural level value)

/-- Changing or adding a resource metric cannot alter the naturality law because the metric is not
an argument of the selector.  Metrics can assess a selected temporal flow downstream. -/
theorem selection_naturality_independent_of_resource
    (surface : NaturalSelectionTruth.{u, v, w, z, l, g, k} S)
    {Resource : Type*} (_first _second : GlobalValue → Resource) :
    (∀ level value, surface.selected (surface.shift level value) ↔
      surface.selected value) :=
  surface.selected_natural

end NaturalSelectionTruth

/-! ## One natural temporal trading flow -/

/-- A temporal flow whose endpoints have both passed the same natural selector.  Selection is an
admissibility aspect; the evaluator's price movement and cost still decide positivity. -/
structure NaturalTemporalFlow
    {N : Network.{u, v}} {R : Type w}
    {LocalPrice : Type l} {GlobalValue : Type g}
    {S : NRRF781.Supernet.{u, v, w, z, l, g} N R LocalPrice GlobalValue}
    (potentialBridge : NRRF783.RelativePotentialBridge.{u, v, w, z, l, g, p} S)
    (surface : NaturalSelectionTruth.{u, v, w, z, l, g, k} S)
    (Value : Type f) [AddCommGroup Value] [LinearOrder Value]
    [IsOrderedAddMonoid Value] where
  evaluation : NRRF783.TemporalFlow potentialBridge Value
  entry_selected : surface.selected evaluation.entry
  exit_selected : surface.selected evaluation.exit
  profit_criterion :
    0 < evaluation.flow.net ↔
      evaluation.flow.cost <
        evaluation.readPotential (potentialBridge.potential evaluation.exit) -
          evaluation.readPotential (potentialBridge.potential evaluation.entry)

namespace NaturalTemporalFlow

variable {N : Network.{u, v}} {R : Type w}
  {LocalPrice : Type l} {GlobalValue : Type g}
  {S : NRRF781.Supernet.{u, v, w, z, l, g} N R LocalPrice GlobalValue}
  {potentialBridge : NRRF783.RelativePotentialBridge.{u, v, w, z, l, g, p} S}
  {surface : NaturalSelectionTruth.{u, v, w, z, l, g, k} S}
  {Value : Type f} [AddCommGroup Value] [LinearOrder Value] [IsOrderedAddMonoid Value]

/-- Selection remains valid after any simultaneous level re-expression of either endpoint. -/
theorem selected_after_shift
    (flow : NaturalTemporalFlow potentialBridge surface Value)
    (level : surface.LevelShift) :
    surface.selected (surface.shift level flow.evaluation.entry) ∧
      surface.selected (surface.shift level flow.evaluation.exit) :=
  ⟨(surface.selected_natural level _).2 flow.entry_selected,
    (surface.selected_natural level _).2 flow.exit_selected⟩

/-- Partial orbit truth is likewise independent of the level at which each endpoint is presented. -/
theorem truth_after_shift
    (flow : NaturalTemporalFlow potentialBridge surface Value)
    (level : surface.LevelShift) :
    surface.orbitTruth (surface.shift level flow.evaluation.entry) =
        surface.orbitTruth flow.evaluation.entry ∧
      surface.orbitTruth (surface.shift level flow.evaluation.exit) =
        surface.orbitTruth flow.evaluation.exit :=
  ⟨surface.truth_natural level _, surface.truth_natural level _⟩

/-- Naturality does not replace the empirical inequality: positive flow still means invariant
relative-potential movement exceeds friction. -/
theorem profitable_iff_potential_move_exceeds_cost
    (flow : NaturalTemporalFlow potentialBridge surface Value) :
    0 < flow.evaluation.flow.net ↔
      flow.evaluation.flow.cost <
        flow.evaluation.readPotential
            (potentialBridge.potential flow.evaluation.exit) -
          flow.evaluation.readPotential
            (potentialBridge.potential flow.evaluation.entry) :=
  flow.profit_criterion

/-- A naturally selected profitable flow must still enter a new returned-token class. -/
theorem profit_requires_token_change
    (flow : NaturalTemporalFlow potentialBridge surface Value)
    (profitable : 0 < flow.evaluation.flow.net) :
    S.tokenRead flow.evaluation.entry ≠ S.tokenRead flow.evaluation.exit :=
  flow.evaluation.profit_requires_token_change profitable

/-- The same boundary in the reported constructive translational-truth language. -/
theorem profit_requires_new_translational_closure
    (flow : NaturalTemporalFlow potentialBridge surface Value)
    (profitable : 0 < flow.evaluation.flow.net) :
    ¬ potentialBridge.TransTruth flow.evaluation.entry flow.evaluation.exit :=
  flow.evaluation.profit_requires_new_translational_closure profitable

end NaturalTemporalFlow

/-! ## Collected constructive trading consequence -/

theorem nrrf786_answer
    {N : Network.{u, v}} {R : Type w}
    {LocalPrice : Type l} {GlobalValue : Type g}
    {S : NRRF781.Supernet.{u, v, w, z, l, g} N R LocalPrice GlobalValue}
    {potentialBridge : NRRF783.RelativePotentialBridge.{u, v, w, z, l, g, p} S}
    {surface : NaturalSelectionTruth.{u, v, w, z, l, g, k} S}
    {Value : Type f} [AddCommGroup Value] [LinearOrder Value] [IsOrderedAddMonoid Value]
    (flow : NaturalTemporalFlow potentialBridge surface Value)
    (level : surface.LevelShift) :
    surface.selected (surface.shift level flow.evaluation.entry) ∧
    surface.selected (surface.shift level flow.evaluation.exit) ∧
    surface.orbitTruth (surface.shift level flow.evaluation.entry) =
      surface.orbitTruth flow.evaluation.entry ∧
    surface.orbitTruth (surface.shift level flow.evaluation.exit) =
      surface.orbitTruth flow.evaluation.exit ∧
    (0 < flow.evaluation.flow.net ↔
      flow.evaluation.flow.cost <
        flow.evaluation.readPotential
            (potentialBridge.potential flow.evaluation.exit) -
          flow.evaluation.readPotential
            (potentialBridge.potential flow.evaluation.entry)) ∧
    (0 < flow.evaluation.flow.net →
      S.tokenRead flow.evaluation.entry ≠ S.tokenRead flow.evaluation.exit) :=
  ⟨(flow.selected_after_shift level).1,
    (flow.selected_after_shift level).2,
    (flow.truth_after_shift level).1,
    (flow.truth_after_shift level).2,
    flow.profitable_iff_potential_move_exceeds_cost,
    flow.profit_requires_token_change⟩

#print axioms NRRF786.nrrf786_answer
#print axioms NRRF786.NaturalSelectionTruth.potential_natural
#print axioms NRRF786.NaturalTemporalFlow.selected_after_shift
#print axioms NRRF786.NaturalTemporalFlow.truth_after_shift
#print axioms NRRF786.NaturalTemporalFlow.profitable_iff_potential_move_exceeds_cost
#print axioms NRRF786.NaturalTemporalFlow.profit_requires_token_change
#print axioms NRRF786.NaturalTemporalFlow.profit_requires_new_translational_closure

end NRRF786
