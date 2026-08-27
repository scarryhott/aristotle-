import NRRF781SocioeconomicTokenomicTradingSupernet

/-!
# NRRF783 — Relative potential and classical value flow in the trading Supernet

The authenticated NRRF780 classical evaluator and NRRF782 translational-closure sources are
retained in the external Aristotle snapshot rather than compiled into this newer-toolchain root.
This module states the exact potential classification and value-flow equations needed from those
results and proves their consequence for the locally checked NRRF781 trading bridge.

The consequence separates two forms:

* inside one closure-preserving occurrence, relative potential cannot move, so classical net flow
  is exactly negative friction;
* across closure classes in time, positive flow is possible exactly when the relative-potential
  move exceeds friction, and it necessarily changes the returned token class.
-/

namespace NRRF783

open NRRF764

universe u v w z l g p f

/-! ## Exact external surface of translational truth and relative potential -/

/-- A bridge from NRRF781's returned token equality to the reported NRRF782 classification.
`PotentialField` may carry every pairwise relative potential; no scalar representation is imposed. -/
structure RelativePotentialBridge
    {N : Network.{u, v}} {R : Type w}
    {LocalPrice : Type l} {GlobalValue : Type g}
    (S : NRRF781TradingBridge.Supernet.{u, v, w, z, l, g} N R LocalPrice GlobalValue) where
  PotentialField : Type p
  TransTruth : GlobalValue → GlobalValue → Prop
  potential : GlobalValue → PotentialField
  token_eq_iff_transTruth : ∀ x y,
    S.tokenRead x = S.tokenRead y ↔ TransTruth x y
  transTruth_iff_potential_eq : ∀ x y,
    TransTruth x y ↔ potential x = potential y

namespace RelativePotentialBridge

variable {N : Network.{u, v}} {R : Type w}
  {LocalPrice : Type l} {GlobalValue : Type g}
  {S : NRRF781TradingBridge.Supernet.{u, v, w, z, l, g} N R LocalPrice GlobalValue}

/-- Returned token equality is exactly equality of the complete relative-potential field. -/
theorem token_eq_iff_potential_eq
    (B : RelativePotentialBridge.{u, v, w, z, l, g, p} S)
    (x y : GlobalValue) :
    S.tokenRead x = S.tokenRead y ↔ B.potential x = B.potential y := by
  rw [B.token_eq_iff_transTruth, B.transTruth_iff_potential_eq]

end RelativePotentialBridge

/-! ## Classical value flow, without rebuilding the six reported layers -/

/-- Only the reported evaluation equation and nonnegative friction are needed downstream. -/
structure ClassicalFlow (Value : Type f) [AddCommGroup Value] [LinearOrder Value]
    [IsOrderedAddMonoid Value] where
  priceMove : Value
  cost : Value
  net : Value
  cost_nonnegative : 0 ≤ cost
  net_eq_priceMove_sub_cost : net = priceMove - cost

/-! ## A closure-internal execution -/

/-- The classical flow attached to one already unified NRRF781 occurrence.  `readPotential` is a
chosen numerical reading of the invariant potential field; the field itself remains primary. -/
structure OccurrenceFlow
    {N : Network.{u, v}} {R : Type w}
    {LocalPrice : Type l} {GlobalValue : Type g}
    {S : NRRF781TradingBridge.Supernet.{u, v, w, z, l, g} N R LocalPrice GlobalValue}
    {ops : NRRF779.ReportedSelectorOperations N}
    {cert : NRRF779.TranslationCertificates ops}
    {bridge : NRRF779.RelationalLiveBridge S.trading}
    {selector : NRRF768.NaturalFormSelector (NRRF627.flipFrame N.Reading)}
    {receipt : bridge.live.runtime.Receipt}
    (occ : NRRF781TradingBridge.TradingOccurrence S ops cert bridge selector receipt)
    (potentialBridge : RelativePotentialBridge.{u, v, w, z, l, g, p} S)
    (Value : Type f) [AddCommGroup Value] [LinearOrder Value]
    [IsOrderedAddMonoid Value] where
  flow : ClassicalFlow Value
  readPotential : potentialBridge.PotentialField → Value
  priceMove_eq : flow.priceMove =
    readPotential (potentialBridge.potential occ.transaction.exit.globalCostEqual) -
      readPotential (potentialBridge.potential occ.transaction.entry.globalCostEqual)

namespace OccurrenceFlow

variable {N : Network.{u, v}} {R : Type w}
  {LocalPrice : Type l} {GlobalValue : Type g}
  {S : NRRF781TradingBridge.Supernet.{u, v, w, z, l, g} N R LocalPrice GlobalValue}
  {ops : NRRF779.ReportedSelectorOperations N}
  {cert : NRRF779.TranslationCertificates ops}
  {bridge : NRRF779.RelationalLiveBridge S.trading}
  {selector : NRRF768.NaturalFormSelector (NRRF627.flipFrame N.Reading)}
  {receipt : bridge.live.runtime.Receipt}
  {occ : NRRF781TradingBridge.TradingOccurrence S ops cert bridge selector receipt}
  {potentialBridge : RelativePotentialBridge.{u, v, w, z, l, g, p} S}
  {Value : Type f} [AddCommGroup Value] [LinearOrder Value] [IsOrderedAddMonoid Value]

/-- One Supernet occurrence has equal complete relative-potential fields at its two ends. -/
theorem potential_eq
    (_evaluation : OccurrenceFlow occ potentialBridge Value) :
    potentialBridge.potential occ.transaction.entry.globalCostEqual =
      potentialBridge.potential occ.transaction.exit.globalCostEqual :=
  (potentialBridge.token_eq_iff_potential_eq _ _).mp occ.tokenomic_closure

/-- Hence an internal closure-preserving execution has no relative-potential move. -/
theorem priceMove_eq_zero
    (evaluation : OccurrenceFlow occ potentialBridge Value) :
    evaluation.flow.priceMove = 0 := by
  rw [evaluation.priceMove_eq, evaluation.potential_eq]
  simp

/-- The reported classical identity now closes exactly: internal net flow is negative friction. -/
theorem net_eq_neg_cost
    (evaluation : OccurrenceFlow occ potentialBridge Value) :
    evaluation.flow.net = -evaluation.flow.cost := by
  rw [evaluation.flow.net_eq_priceMove_sub_cost, evaluation.priceMove_eq_zero]
  exact zero_sub _

/-- Nonnegative friction makes every such internal occurrence nonpositive. -/
theorem net_nonpositive
    (evaluation : OccurrenceFlow occ potentialBridge Value) :
    evaluation.flow.net ≤ 0 := by
  rw [evaluation.net_eq_neg_cost]
  exact neg_nonpos.mpr evaluation.flow.cost_nonnegative

/-- A positive result cannot be manufactured inside a closure-preserving occurrence. -/
theorem not_profitable
    (evaluation : OccurrenceFlow occ potentialBridge Value) :
    ¬ 0 < evaluation.flow.net :=
  not_lt_of_ge evaluation.net_nonpositive

end OccurrenceFlow

/-! ## Trading across closure classes in time -/

/-- A temporal flow compares two completed global forms in the same Supernet.  Unlike one
closure-internal occurrence, its endpoints are not assumed to have the same token return. -/
structure TemporalFlow
    {N : Network.{u, v}} {R : Type w}
    {LocalPrice : Type l} {GlobalValue : Type g}
    {S : NRRF781TradingBridge.Supernet.{u, v, w, z, l, g} N R LocalPrice GlobalValue}
    (potentialBridge : RelativePotentialBridge.{u, v, w, z, l, g, p} S)
    (Value : Type f) [AddCommGroup Value] [LinearOrder Value]
    [IsOrderedAddMonoid Value] where
  entry : GlobalValue
  exit : GlobalValue
  flow : ClassicalFlow Value
  readPotential : potentialBridge.PotentialField → Value
  priceMove_eq : flow.priceMove =
    readPotential (potentialBridge.potential exit) -
      readPotential (potentialBridge.potential entry)

namespace TemporalFlow

variable {N : Network.{u, v}} {R : Type w}
  {LocalPrice : Type l} {GlobalValue : Type g}
  {S : NRRF781TradingBridge.Supernet.{u, v, w, z, l, g} N R LocalPrice GlobalValue}
  {potentialBridge : RelativePotentialBridge.{u, v, w, z, l, g, p} S}
  {Value : Type f} [AddCommGroup Value] [LinearOrder Value] [IsOrderedAddMonoid Value]

/-- The temporal classical P&L condition: invariant potential movement must exceed friction. -/
theorem profitable_iff_potential_move_exceeds_cost
    (evaluation : TemporalFlow potentialBridge Value) :
    0 < evaluation.flow.net ↔
      evaluation.flow.cost <
        evaluation.readPotential (potentialBridge.potential evaluation.exit) -
          evaluation.readPotential (potentialBridge.potential evaluation.entry) := by
  rw [evaluation.flow.net_eq_priceMove_sub_cost, evaluation.priceMove_eq, sub_pos]

/-- Positive temporal flow necessarily crosses to a distinct returned token class.  Global-shift
freedom inside one closure therefore cannot be the source of profit. -/
theorem profit_requires_token_change
    (evaluation : TemporalFlow potentialBridge Value)
    (profitable : 0 < evaluation.flow.net) :
    S.tokenRead evaluation.entry ≠ S.tokenRead evaluation.exit := by
  intro sameToken
  have samePotential :
      potentialBridge.potential evaluation.entry =
        potentialBridge.potential evaluation.exit :=
    (potentialBridge.token_eq_iff_potential_eq _ _).mp sameToken
  have moveZero : evaluation.flow.priceMove = 0 := by
    rw [evaluation.priceMove_eq, samePotential]
    simp
  have netNonpositive : evaluation.flow.net ≤ 0 := by
    rw [evaluation.flow.net_eq_priceMove_sub_cost, moveZero]
    simpa using neg_nonpos.mpr evaluation.flow.cost_nonnegative
  exact (not_lt_of_ge netNonpositive) profitable

/-- Equivalently, profit requires failure of translational truth between the temporal endpoints. -/
theorem profit_requires_new_translational_closure
    (evaluation : TemporalFlow potentialBridge Value)
    (profitable : 0 < evaluation.flow.net) :
    ¬ potentialBridge.TransTruth evaluation.entry evaluation.exit := by
  intro sameClosure
  apply evaluation.profit_requires_token_change profitable
  exact (potentialBridge.token_eq_iff_transTruth _ _).mpr sameClosure

end TemporalFlow

/-! ## Collected result -/

theorem nrrf783_answer
    {N : Network.{u, v}} {R : Type w}
    {LocalPrice : Type l} {GlobalValue : Type g}
    {S : NRRF781TradingBridge.Supernet.{u, v, w, z, l, g} N R LocalPrice GlobalValue}
    {ops : NRRF779.ReportedSelectorOperations N}
    {cert : NRRF779.TranslationCertificates ops}
    {bridge : NRRF779.RelationalLiveBridge S.trading}
    {selector : NRRF768.NaturalFormSelector (NRRF627.flipFrame N.Reading)}
    {receipt : bridge.live.runtime.Receipt}
    {occ : NRRF781TradingBridge.TradingOccurrence S ops cert bridge selector receipt}
    {potentialBridge : RelativePotentialBridge.{u, v, w, z, l, g, p} S}
    {Value : Type f} [AddCommGroup Value] [LinearOrder Value] [IsOrderedAddMonoid Value]
    (internal : OccurrenceFlow occ potentialBridge Value)
    (temporal : TemporalFlow potentialBridge Value) :
    internal.flow.net = -internal.flow.cost ∧
    internal.flow.net ≤ 0 ∧
    (0 < temporal.flow.net ↔
      temporal.flow.cost <
        temporal.readPotential (potentialBridge.potential temporal.exit) -
          temporal.readPotential (potentialBridge.potential temporal.entry)) ∧
    (0 < temporal.flow.net →
      S.tokenRead temporal.entry ≠ S.tokenRead temporal.exit) :=
  ⟨internal.net_eq_neg_cost,
    internal.net_nonpositive,
    temporal.profitable_iff_potential_move_exceeds_cost,
    temporal.profit_requires_token_change⟩

#print axioms NRRF783.nrrf783_answer
#print axioms NRRF783.OccurrenceFlow.net_eq_neg_cost
#print axioms NRRF783.TemporalFlow.profit_requires_new_translational_closure

end NRRF783
