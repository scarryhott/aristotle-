/-!
# NRRF787 — Canonical admitted continuum and unique partial-operator descent

This file uses only Lean's kernel.  It makes the requested order explicit:

1. an existence admission identifies the presentations in scope;
2. translational truth is a supplied and proved equivalence on those presentations;
3. completion is the quotient by that equivalence;
4. substrate operations preserving translational truth descend to completion;
5. any invariant partial operator descends uniquely to completion; and
6. every exact presented resolution is canonically equivalent to completion.

No universal machine, Turing completeness, halting decider, physical universe, selector, metric,
or classical law is assumed.  A computation-like reading arises only when `PartialOperator.run` is
instantiated by an explicitly supplied partial transition.
-/

namespace NRRF787

universe u v w

-- `Presentation` and `Substrate` are intentionally independent carriers stored in one structure.
set_option linter.checkUnivs false

/-! ## Existence admission, translational truth, and substrate interaction -/

/-- An admitted relational universe.  `Presentation` is only a carrier of possible descriptions;
`admitted` says which of them exist in the present interface.  `TransTruth` is the relative
identification to be proved for those admitted descriptions.  Substrate composition and its action
are supplied as data, with their laws, rather than inferred from an ambient machine model. -/
structure AdmissionUniverse where
  Presentation : Type u
  admitted : Presentation → Prop
  Substrate : Type v
  substrateUnit : Substrate
  substrateComp : Substrate → Substrate → Substrate
  substrateUnit_left : ∀ s, substrateComp substrateUnit s = s
  substrateUnit_right : ∀ s, substrateComp s substrateUnit = s
  substrateComp_assoc : ∀ a b c,
    substrateComp (substrateComp a b) c = substrateComp a (substrateComp b c)
  act : Substrate → Subtype admitted → Subtype admitted
  act_unit : ∀ x, act substrateUnit x = x
  act_comp : ∀ a b x, act (substrateComp a b) x = act a (act b x)
  TransTruth : Subtype admitted → Subtype admitted → Prop
  trans_refl : ∀ x, TransTruth x x
  trans_symm : ∀ {x y}, TransTruth x y → TransTruth y x
  trans_trans : ∀ {x y z}, TransTruth x y → TransTruth y z → TransTruth x z
  act_natural : ∀ s {x y}, TransTruth x y → TransTruth (act s x) (act s y)

namespace AdmissionUniverse

variable (U : AdmissionUniverse.{u, v})

/-- Existence admission is a subtype: witnesses are retained as data. -/
abbrev Admitted := Subtype U.admitted

/-- Translational truth, already carrying its equivalence proofs, presents a setoid. -/
def transSetoid : Setoid U.Admitted where
  r := U.TransTruth
  iseqv := ⟨U.trans_refl, U.trans_symm, U.trans_trans⟩

/-- The natural relational continuum is the quotient of admitted presentations by translational
truth.  It is derived after admission and relative identification; it is not postulated first. -/
abbrev Continuum := Quotient U.transSetoid

/-- Completion sends an admitted presentation to its translational-truth class. -/
def complete (x : U.Admitted) : U.Continuum :=
  Quotient.mk U.transSetoid x

/-- Completion identifies exactly the supplied translational-truth relation. -/
theorem complete_eq_iff (x y : U.Admitted) :
    U.complete x = U.complete y ↔ U.TransTruth x y :=
  ⟨Quotient.exact,
    fun h => @Quotient.sound U.Admitted U.transSetoid x y h⟩

/-- Every substrate operation descends to the continuum because it preserves translational truth. -/
def substrateAction (s : U.Substrate) : U.Continuum → U.Continuum :=
  Quotient.lift
    (fun x => U.complete (U.act s x))
    (fun x y h =>
      @Quotient.sound U.Admitted U.transSetoid (U.act s x) (U.act s y)
        (U.act_natural s h))

@[simp] theorem substrateAction_complete (s : U.Substrate) (x : U.Admitted) :
    U.substrateAction s (U.complete x) = U.complete (U.act s x) :=
  rfl

/-- The substrate unit remains the identity after completion. -/
theorem substrateAction_unit (q : U.Continuum) :
    U.substrateAction U.substrateUnit q = q := by
  refine Quotient.inductionOn q ?_
  intro x
  change U.complete (U.act U.substrateUnit x) = U.complete x
  rw [U.act_unit]

/-- Composition of substrate operations is preserved by completion. -/
theorem substrateAction_comp (a b : U.Substrate) (q : U.Continuum) :
    U.substrateAction (U.substrateComp a b) q =
      U.substrateAction a (U.substrateAction b q) := by
  refine Quotient.inductionOn q ?_
  intro x
  change U.complete (U.act (U.substrateComp a b) x) =
    U.complete (U.act a (U.act b x))
  rw [U.act_comp]

end AdmissionUniverse

/-! ## Canonical equivalence with any exact presented resolution -/

/-- The constructive data of an equivalence.  This local definition keeps the file kernel-only:
both translations and both cancellation proofs are supplied explicitly. -/
structure CanonicalEquiv (A : Type u) (B : Type v) where
  toFun : A → B
  invFun : B → A
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b

/-- A resolution is *presented* when both directions are data.  `resolve` forgets only relative
presentation, while `present` supplies one admitted representative for every resolved point.
`exact` says this round trip stays in the original translational-truth class.  Because the section
is part of the structure, no choice principle is required. -/
structure PresentedResolution (U : AdmissionUniverse.{u, v}) where
  Carrier : Type w
  resolve : U.Admitted → Carrier
  present : Carrier → U.Admitted
  respects : ∀ {x y}, U.TransTruth x y → resolve x = resolve y
  return_eq : ∀ c, resolve (present c) = c
  exact : ∀ x, U.TransTruth (present (resolve x)) x

namespace PresentedResolution

variable {U : AdmissionUniverse.{u, v}} (R : PresentedResolution.{u, v, w} U)

/-- A resolution receives the canonical map from the admitted continuum. -/
def fromContinuum : U.Continuum → R.Carrier :=
  Quotient.lift R.resolve (fun _ _ h => R.respects h)

@[simp] theorem fromContinuum_complete (x : U.Admitted) :
    R.fromContinuum (U.complete x) = R.resolve x :=
  rfl

/-- A presented resolution is canonically equivalent to the quotient continuum. -/
def continuumEquiv : CanonicalEquiv U.Continuum R.Carrier where
  toFun := R.fromContinuum
  invFun := fun c => U.complete (R.present c)
  left_inv q := by
    refine Quotient.inductionOn q ?_
    intro x
    exact Quotient.sound (R.exact x)
  right_inv c := R.return_eq c

/-- The canonical map is the unique map agreeing with resolution on admitted presentations.
Uniqueness is pointwise, so function extensionality is not needed. -/
theorem fromContinuum_unique
    (f : U.Continuum → R.Carrier)
    (commutes : ∀ x, f (U.complete x) = R.resolve x)
    (q : U.Continuum) :
    f q = R.fromContinuum q := by
  refine Quotient.inductionOn q ?_
  intro x
  exact commutes x

end PresentedResolution

/-! ## Unique descent of a partial operator -/

/-- A partial operator is an explicitly supplied `Option`-valued interaction.  Its two laws say
that presentation changes and substrate changes do not alter its answer.  The definition neither
assumes nor entails that the operator is universal, total, terminating, or Turing complete. -/
structure PartialOperator (U : AdmissionUniverse.{u, v}) where
  Output : Type w
  run : U.Admitted → Option Output
  trans_natural : ∀ {x y}, U.TransTruth x y → run x = run y
  substrate_natural : ∀ s x, run (U.act s x) = run x

namespace PartialOperator

variable {U : AdmissionUniverse.{u, v}} (op : PartialOperator.{u, v, w} U)

/-- The partial operator on the relational continuum. -/
def descend : U.Continuum → Option op.Output :=
  Quotient.lift op.run (fun _ _ h => op.trans_natural h)

@[simp] theorem descend_complete (x : U.Admitted) :
    op.descend (U.complete x) = op.run x :=
  rfl

/-- Descent is natural under every admitted substrate operation. -/
theorem descend_substrate (s : U.Substrate) (q : U.Continuum) :
    op.descend (U.substrateAction s q) = op.descend q := by
  refine Quotient.inductionOn q ?_
  intro x
  exact op.substrate_natural s x

/-- Any other continuum operator with the same admitted readings is pointwise the same descent. -/
theorem descend_unique
    (f : U.Continuum → Option op.Output)
    (commutes : ∀ x, f (U.complete x) = op.run x)
    (q : U.Continuum) :
    f q = op.descend q := by
  refine Quotient.inductionOn q ?_
  intro x
  exact commutes x

/-- The partial domain is a property of the translational-truth class, not its presentation. -/
def Defined (q : U.Continuum) : Prop :=
  ∃ output, op.descend q = some output

/-- Definedness is substrate-natural. -/
theorem defined_substrate_iff (s : U.Substrate) (q : U.Continuum) :
    op.Defined (U.substrateAction s q) ↔ op.Defined q := by
  unfold Defined
  rw [op.descend_substrate]

end PartialOperator

/-! ## Collected unification -/

/-- Existence admission, translational truth, the canonical continuum, an exact resolution, and a
partial substrate-natural operator form one commuting architecture. -/
theorem nrrf787_unification
    {U : AdmissionUniverse.{u, v}}
    (R : PresentedResolution.{u, v, w} U)
    (op : PartialOperator.{u, v, w} U)
    (x y : U.Admitted) (s : U.Substrate) (q : U.Continuum) :
    (U.complete x = U.complete y ↔ U.TransTruth x y) ∧
    R.fromContinuum (U.complete x) = R.resolve x ∧
    R.continuumEquiv.invFun (R.continuumEquiv.toFun q) = q ∧
    op.descend (U.complete x) = op.run x ∧
    op.descend (U.substrateAction s q) = op.descend q ∧
    (op.Defined (U.substrateAction s q) ↔ op.Defined q) :=
  ⟨U.complete_eq_iff x y,
    R.fromContinuum_complete x,
    R.continuumEquiv.left_inv q,
    op.descend_complete x,
    op.descend_substrate s q,
    op.defined_substrate_iff s q⟩

#print axioms NRRF787.AdmissionUniverse.complete_eq_iff
#print axioms NRRF787.AdmissionUniverse.substrateAction_unit
#print axioms NRRF787.AdmissionUniverse.substrateAction_comp
#print axioms NRRF787.PresentedResolution.continuumEquiv
#print axioms NRRF787.PresentedResolution.fromContinuum_unique
#print axioms NRRF787.PartialOperator.descend_substrate
#print axioms NRRF787.PartialOperator.descend_unique
#print axioms NRRF787.PartialOperator.defined_substrate_iff
#print axioms NRRF787.nrrf787_unification

end NRRF787
