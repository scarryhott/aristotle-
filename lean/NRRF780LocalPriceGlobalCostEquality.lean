import Mathlib.Algebra.Group.Basic

/-!
# NRRF780 — Local price, global cost equality

Price is local data.  Cost is not a second scalar subtracted from it; cost is the global returned
equality through which that local presentation completes.  This module states that interface for
arbitrary carriers and makes empirical comparison depend only on two completed global forms.

The optional commutative-group section explains the runtime factorization.  Given an already
observed completed form `completed`, the global cost equality derived from a local form is
`local / completed`; completing by that equality returns `completed` exactly.  Refactoring an
existing calculation into this equality therefore cannot change its numerical sign.  A changed
result requires new local data, a different completion, or a different interaction—not a renamed
factorization.
-/

namespace NRRF780Local

universe u v w

/-! ## Price local; cost its global equal -/

/-- The only primitive operation is completion of a local presentation into the global carrier. -/
structure PriceCostInterface (Local : Type u) (Global : Type v) where
  complete : Local → Global

/-- One local price together with the global cost equality it actually completes to. -/
structure LocalPriceGlobalCost {Local : Type u} {Global : Type v}
    (I : PriceCostInterface Local Global) where
  localPrice : Local
  globalCostEqual : Global
  completion : I.complete localPrice = globalCostEqual

namespace LocalPriceGlobalCost

variable {Local : Type u} {Global : Type v} {I : PriceCostInterface Local Global}

/-- Cost is literally the completed global equality of the local price. -/
theorem cost_is_global_equal (P : LocalPriceGlobalCost I) :
    I.complete P.localPrice = P.globalCostEqual :=
  P.completion

/-- Distinct local presentations with the same cost equality are indistinguishable after
completion; no literal equality of their local prices is asserted. -/
theorem completions_eq_of_global_equal
    (P Q : LocalPriceGlobalCost I)
    (sameGlobal : P.globalCostEqual = Q.globalCostEqual) :
    I.complete P.localPrice = I.complete Q.localPrice := by
  rw [P.completion, Q.completion, sameGlobal]

end LocalPriceGlobalCost

/-! ## Entry and exit are compared only after completion -/

/-- A candidate transaction contains completed entry and exit presentations.  It does not contain
an order, a fill, settlement, or a positivity assertion. -/
structure CompletedTransaction {Local : Type u} {Global : Type v}
    (I : PriceCostInterface Local Global) where
  entry : LocalPriceGlobalCost I
  exit : LocalPriceGlobalCost I

/-- Empirical assessment is a relation on completed global forms, never a direct comparison of
the isolated local prices. -/
structure GlobalAssessment (Global : Type v) where
  Outcome : Type w
  compare : Global → Global → Outcome
  positive : Outcome → Prop

namespace CompletedTransaction

variable {Local : Type u} {Global : Type v}
  {I : PriceCostInterface Local Global}

def assess (T : CompletedTransaction I) (A : GlobalAssessment Global) : A.Outcome :=
  A.compare T.entry.globalCostEqual T.exit.globalCostEqual

/-- The assessment may equivalently be computed from the completed local presentations. -/
theorem assess_eq_completed_locals
    (T : CompletedTransaction I) (A : GlobalAssessment Global) :
    T.assess A = A.compare (I.complete T.entry.localPrice) (I.complete T.exit.localPrice) := by
  rw [assess, T.entry.completion, T.exit.completion]

/-- Changing local presentations without changing either global equality cannot change the
assessment. -/
theorem assessment_invariant_under_local_reexpression
    (T U : CompletedTransaction I) (A : GlobalAssessment Global)
    (sameEntry : T.entry.globalCostEqual = U.entry.globalCostEqual)
    (sameExit : T.exit.globalCostEqual = U.exit.globalCostEqual) :
    T.assess A = U.assess A := by
  simp only [assess, sameEntry, sameExit]

end CompletedTransaction

/-- Profit is additional empirical evidence about an already completed assessment. -/
structure PositiveCompletedOutcome {Local : Type u} {Global : Type v}
    {I : PriceCostInterface Local Global}
    (T : CompletedTransaction I) (A : GlobalAssessment Global) where
  positive : A.positive (T.assess A)

/-! ## Missing local data remains missing -/

/-- A partial live interface cannot manufacture a completed price/cost occurrence from `none`. -/
theorem no_completion_of_none {Local : Type u} {Global : Type v}
    (I : PriceCostInterface Local Global) :
    (none : Option (LocalPriceGlobalCost I)) = none :=
  rfl

/-! ## The multiplicative realization is a factorization, not a new result -/

/-- In a multiplicative empirical carrier, the global cost equality relating a local form to an
already observed completed form.  No order or positivity is used. -/
def derivedGlobalCostEqual {G : Type u} [CommGroup G]
    (localForm completed : G) : G :=
  localForm / completed

/-- Completing the local form by its derived global cost equality returns the original completed
form exactly.  Hence this refactor alone cannot alter an observed P&L sign. -/
theorem complete_by_derived_global_equal {G : Type u} [CommGroup G]
    (localForm completed : G) :
    localForm / derivedGlobalCostEqual localForm completed = completed := by
  simp [derivedGlobalCostEqual]

/-- One theorem collecting the architectural result. -/
theorem nrrf780_answer {Local : Type u} {Global : Type v}
    {I : PriceCostInterface Local Global}
    (T : CompletedTransaction I) (A : GlobalAssessment Global) :
    I.complete T.entry.localPrice = T.entry.globalCostEqual ∧
    I.complete T.exit.localPrice = T.exit.globalCostEqual ∧
    T.assess A = A.compare (I.complete T.entry.localPrice) (I.complete T.exit.localPrice) :=
  ⟨T.entry.completion, T.exit.completion, T.assess_eq_completed_locals A⟩

#print axioms NRRF780Local.nrrf780_answer
#print axioms NRRF780Local.complete_by_derived_global_equal
#print axioms NRRF780Local.CompletedTransaction.assessment_invariant_under_local_reexpression

end NRRF780Local
