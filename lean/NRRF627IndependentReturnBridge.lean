import NRRF627ClosureTranslationalFrameworkAxiometryASIEvolutionaryVerification

/-!
# NRRF627 — independent-return derivation bridge

This companion does not take arbitrary `T`, `phi`, or their coherence laws as primitive.
It starts with:

* one canonical, independently returned trace carrier `X`;
* a return protocol on `X`; and
* reversible codecs from `X` into each temporary presentation language.

The pairwise translations, their inverses, their composition law, and the commuting return square
are then constructions.  The reversal and curvature laws remain explicit obligations of the
independent return protocol; the executable experiment tests their concrete presentation-level
instances after seller return.
-/

namespace NRRF627IndependentReturn

open NRRF627

universe u v w z

/-! ## TRUE / FALSE / OPEN and the one-token gate -/

inductive GateVerdict where
  | verified
  | contradicted
  | open_
deriving DecidableEq, Repr

/-- Independent evidence.  `selfClaim` is retained for audit but cannot decide the gate. -/
structure Evidence where
  sellerReturn : Option Bool
  selfClaim : Bool
deriving DecidableEq, Repr

def decide (e : Evidence) : GateVerdict :=
  match e.sellerReturn with
  | some true => .verified
  | some false => .contradicted
  | none => .open_

def tokenCount : GateVerdict → Nat
  | .verified => 1
  | .contradicted => 0
  | .open_ => 0

def admittedToNextBasis : GateVerdict → Bool
  | .verified => true
  | .contradicted => false
  | .open_ => false

theorem episode_tokens_le_one (v : GateVerdict) : tokenCount v ≤ 1 := by
  cases v <;> simp [tokenCount]

theorem self_certification_no_token (claim : Bool) :
    tokenCount (decide ⟨none, claim⟩) = 0 := by
  rfl

theorem seller_contradiction_no_token (claim : Bool) :
    tokenCount (decide ⟨some false, claim⟩) = 0 := by
  rfl

theorem authenticated_return_one_token (claim : Bool) :
    tokenCount (decide ⟨some true, claim⟩) = 1 := by
  rfl

theorem open_branch_not_in_next_basis : admittedToNextBasis .open_ = false := by
  rfl

theorem contradiction_not_in_next_basis : admittedToNextBasis .contradicted = false := by
  rfl

/-! ## A canonical independent return and reversible temporary presentations -/

/--
The operational obligations that remain on the canonical returned trace.  In the executable model,
`W` is computed from authenticated seller receipts; it is defined before any topology is disclosed.
-/
structure ReturnProtocol (X : Type v) (R : Type w) where
  W : X → R
  E : Pole → R → X
  recov : ∀ p r, W (E p r) = r
  J : X → X
  J_invol : ∀ x, J (J x) = x
  J_ret : ∀ x, W (J x) = W x
  J_ext : ∀ p r, J (E p r) = E (Pole.other p) r
  C : X → X
  C_idem : ∀ x, C (C x) = C x
  C_ret : ∀ x, W (C x) = W x

/-- Every admitted language is only a reversible presentation of the same canonical trace. -/
structure PresentationFamily (L : Type u) (X : Type v) (Y : L → Type z) where
  codec : ∀ ℓ, X ≃ Y ℓ

/--
Derive the full NRRF627 `TransFrame`.  Translation is decode-then-encode, so identity,
composition, invertibility, naturality, and the return square are consequences of the codecs.
-/
def derivedFrame
    {L : Type u} {X : Type v} {R : Type w} {Y : L → Type z}
    (P : ReturnProtocol X R) (F : PresentationFamily L X Y) :
    TransFrame L (fun _ => R) Y where
  W := fun ℓ y => P.W ((F.codec ℓ).symm y)
  E := fun ℓ p r => F.codec ℓ (P.E p r)
  recov := by
    intro ℓ p r
    simp [P.recov]
  phi := fun _ _ r => r
  phi_id := by
    intro ℓ r
    rfl
  phi_comp := by
    intro ℓ m k r
    rfl
  T := fun ℓ m y => F.codec m ((F.codec ℓ).symm y)
  T_id := by
    intro ℓ y
    simp
  T_comp := by
    intro ℓ m k y
    simp
  T_ret := by
    intro ℓ m y
    simp
  pi := fun _ _ => Equiv.refl Pole
  pi_id := by
    intro ℓ
    rfl
  pi_comp := by
    intro ℓ m k p
    rfl
  T_ext := by
    intro ℓ m p r
    simp
  J := fun ℓ y => F.codec ℓ (P.J ((F.codec ℓ).symm y))
  J_invol := by
    intro ℓ y
    simp [P.J_invol]
  J_ret := by
    intro ℓ y
    simp [P.J_ret]
  J_ext := by
    intro ℓ p r
    simp [P.J_ext]
  T_J := by
    intro ℓ m y
    simp
  C := fun ℓ y => F.codec ℓ (P.C ((F.codec ℓ).symm y))
  C_idem := by
    intro ℓ y
    simp [P.C_idem]
  C_ret := by
    intro ℓ y
    simp [P.C_ret]
  T_C := by
    intro ℓ m y
    simp

section Consequences

variable {L : Type u} {X : Type v} {R : Type w} {Y : L → Type z}
variable (P : ReturnProtocol X R) (F : PresentationFamily L X Y)

/-- The return square is derived from decoding and re-encoding one canonical trace. -/
theorem return_square_is_derived (ℓ m : L) (y : Y ℓ) :
    (derivedFrame P F).W m ((derivedFrame P F).T ℓ m y) =
      (derivedFrame P F).phi ℓ m ((derivedFrame P F).W ℓ y) := by
  simp [derivedFrame]

/-- Translation back is derived, not separately postulated. -/
theorem translation_inverse_is_derived (ℓ m : L) (y : Y ℓ) :
    (derivedFrame P F).T m ℓ ((derivedFrame P F).T ℓ m y) = y := by
  simp [derivedFrame]

/-- Routing through a temporary presentation adds no new result. -/
theorem temporary_presentation_cancels (ℓ m k : L) (y : Y ℓ) :
    (derivedFrame P F).T m k ((derivedFrame P F).T ℓ m y) =
      (derivedFrame P F).T ℓ k y := by
  simp [derivedFrame]

/-- Once the independent-return frame is derived, NRRF627's characterization applies. -/
theorem axiometry_flows_from_independent_return
    {Ω : Type*} (Q : ∀ ℓ, Y ℓ → Ω) :
    (((derivedFrame P F).Invariant Q ∧ (derivedFrame P F).RespectsClosure Q) ↔
      (derivedFrame P F).MeasuredByReturn Q) :=
  (derivedFrame P F).axiometric_verdict_characterisation Q

/-- The evolutionary characterization is inherited by the derived frame. -/
theorem evolution_flows_from_independent_return
    {Ω : Type*} (Q : ∀ ℓ, Y ℓ → Ω) :
    (((∀ (g : Nat → L) (n : Nat) (y : Y (g 0)),
        Q (g n) ((derivedFrame P F).evolve g n y) = Q (g 0) y) ∧
      (derivedFrame P F).RespectsClosure Q) ↔
      (derivedFrame P F).MeasuredByReturn Q) :=
  (derivedFrame P F).evolutionary_verification_is_exactly_return_measurement Q

end Consequences

end NRRF627IndependentReturn

#print axioms NRRF627IndependentReturn.episode_tokens_le_one
#print axioms NRRF627IndependentReturn.derivedFrame
#print axioms NRRF627IndependentReturn.return_square_is_derived
#print axioms NRRF627IndependentReturn.axiometry_flows_from_independent_return
#print axioms NRRF627IndependentReturn.evolution_flows_from_independent_return

