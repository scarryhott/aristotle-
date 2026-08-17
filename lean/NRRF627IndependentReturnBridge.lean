import NRRF627ClosureTranslationalFrameworkAxiometryASIEvolutionaryVerification

/-!
# NRRF627 — independent-return derivation bridge

This companion does not take arbitrary `T`, `phi`, or their coherence laws as primitive.
It starts with:

* one canonical, independently returned trace carrier `X`;
* a return protocol on `X`; and
* reversible codecs from `X` into each temporary presentation language.

The pairwise translations, their inverses, their composition law, and the commuting return square
are then constructions. The executable experiment instantiates the whole relative form
`(W, E, T, phi, pi, J, C)`. Coherent comparison forms remain relative equalities; no fixed
coordinate system is used to turn reversal into contradiction or multiplicity into ambiguity.
-/

namespace NRRF627IndependentReturn

open NRRF627

universe u v w z

/-! ## Frame-relative equality and witness-based admission -/

/-- The commuting return square is a form of relative equality, not a truth-valued verdict. -/
def ReturnSquare {Y₀ : Type v} {Y₁ : Type w} {B₀ : Type z} {B₁ : Type u}
    (W₀ : Y₀ → B₀) (W₁ : Y₁ → B₁) (T : Y₀ → Y₁) (φ : B₀ → B₁) : Prop :=
  ∀ y, W₁ (T y) = φ (W₀ y)

/-- One admissible comparison carries occurrences and their returned identity bases together. -/
structure RelativeEqualityForm
    (Y₀ : Type v) (Y₁ : Type w) (B₀ : Type z) (B₁ : Type u)
    (W₀ : Y₀ → B₀) (W₁ : Y₁ → B₁) where
  T : Y₀ ≃ Y₁
  φ : B₀ ≃ B₁
  returnSquare : ReturnSquare W₀ W₁ T φ

/-- Relative equality is preserved and reflected by the whole comparison form `(T, φ)`. -/
theorem relativeEquality_iff
    {Y₀ : Type v} {Y₁ : Type w} {B₀ : Type z} {B₁ : Type u}
    {W₀ : Y₀ → B₀} {W₁ : Y₁ → B₁}
    (F : RelativeEqualityForm Y₀ Y₁ B₀ B₁ W₀ W₁) (x y : Y₀) :
    CEq W₁ (F.T x) (F.T y) ↔ CEq W₀ x y := by
  change W₁ (F.T x) = W₁ (F.T y) ↔ W₀ x = W₀ y
  rw [F.returnSquare x, F.returnSquare y]
  exact F.φ.injective.eq_iff

/-- Independent contact is witness data inhabiting a selected relative equality form. -/
structure IndependentlyReturned
    (Y₀ : Type v) (Y₁ : Type w) (B₀ : Type z) (B₁ : Type u)
    (W₀ : Y₀ → B₀) (W₁ : Y₁ → B₁) (Contact : Type*)
    extends RelativeEqualityForm Y₀ Y₁ B₀ B₁ W₀ W₁ where
  contact : Contact

/-- A token is a receipt of an inhabited independent-return witness, not an audit label. -/
def tokenCount
    {Y₀ : Type v} {Y₁ : Type w} {B₀ : Type z} {B₁ : Type u}
    {W₀ : Y₀ → B₀} {W₁ : Y₁ → B₁} {Contact : Type*}
    (_ : IndependentlyReturned Y₀ Y₁ B₀ B₁ W₀ W₁ Contact) : Nat := 1

theorem episode_tokens_le_one
    {Y₀ : Type v} {Y₁ : Type w} {B₀ : Type z} {B₁ : Type u}
    {W₀ : Y₀ → B₀} {W₁ : Y₁ → B₁} {Contact : Type*}
    (r : IndependentlyReturned Y₀ Y₁ B₀ B₁ W₀ W₁ Contact) :
    tokenCount r ≤ 1 := by
  rfl

/-- A self-claim is retained, but it is not a relative equality witness. -/
structure SelfClaim where
  claim : Bool
deriving DecidableEq, Repr

def selfClaimTokenCount (_ : SelfClaim) : Nat := 0

theorem self_certification_no_token (claim : Bool) :
    selfClaimTokenCount ⟨claim⟩ = 0 := by
  rfl

/-- An arbitrary candidate may instead expose a concrete failure of the return square. -/
structure CandidateComparison
    (Y₀ : Type v) (Y₁ : Type w) (B₀ : Type z) (B₁ : Type u)
    (W₀ : Y₀ → B₀) (W₁ : Y₁ → B₁) where
  T : Y₀ → Y₁
  φ : B₀ → B₁

def HasReturnCounterexample
    {Y₀ : Type v} {Y₁ : Type w} {B₀ : Type z} {B₁ : Type u}
    {W₀ : Y₀ → B₀} {W₁ : Y₁ → B₁}
    (F : CandidateComparison Y₀ Y₁ B₀ B₁ W₀ W₁) : Prop :=
  ∃ y, W₁ (F.T y) ≠ F.φ (W₀ y)

/-- Every pairwise comparison in `TransFrame` is itself a relative equality form. -/
def TransFrame.relativeEqualityForm
    {L : Type u} {B : L → Type v} {Y : L → Type w}
    (A : TransFrame L B Y) (ℓ m : L) :
    RelativeEqualityForm (Y ℓ) (Y m) (B ℓ) (B m) (A.W ℓ) (A.W m) where
  T := A.transEquiv ℓ m
  φ := A.phiEquiv ℓ m
  returnSquare := A.T_ret ℓ m

/-- The runtime operations are one conjunction of natural relational forms, not separate labels. -/
theorem TransFrame.relative_operations
    {L : Type u} {B : L → Type v} {Y : L → Type w}
    (A : TransFrame L B Y) (ℓ m : L) :
    ReturnSquare (A.W ℓ) (A.W m) (A.T ℓ m) (A.phi ℓ m) ∧
    (∀ p b, A.T ℓ m (A.E ℓ p b) = A.E m (A.pi ℓ m p) (A.phi ℓ m b)) ∧
    (∀ y, A.T ℓ m (A.J ℓ y) = A.J m (A.T ℓ m y)) ∧
    (∀ y, A.T ℓ m (A.C ℓ y) = A.C m (A.T ℓ m y)) ∧
    (∀ x y, CEq (A.W m) (A.T ℓ m x) (A.T ℓ m y) ↔ CEq (A.W ℓ) x y) := by
  exact ⟨A.T_ret ℓ m, A.T_ext ℓ m, A.T_J ℓ m, A.T_C ℓ m,
    fun x y => (A.ceq_iff ℓ m x y).symm⟩

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
#print axioms NRRF627IndependentReturn.relativeEquality_iff
#print axioms NRRF627IndependentReturn.derivedFrame
#print axioms NRRF627IndependentReturn.return_square_is_derived
#print axioms NRRF627IndependentReturn.axiometry_flows_from_independent_return
#print axioms NRRF627IndependentReturn.evolution_flows_from_independent_return
