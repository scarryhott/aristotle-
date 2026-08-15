import NRRF627ClosureTranslationalFrameworkAxiometryASIEvolutionaryVerification

/-!
# A representation bridge from weaker operational data to NRRF627

This companion separates the translational core of `NRRF627.TransFrame` from its polar
restructuring operations.

**PROVED HERE:** given one relational carrier and reversible presentation codecs for each
language, the pairwise basis maps, occurrence translations, orientation relabellings, identity
laws, composition laws, inverse laws, extension law, and commuting return square are constructions.
They are not separately assumed.

**PROVED HERE:** when independently specified polar reversal and curvature operations act on the
relational carrier, the construction extends to the full `NRRF627.TransFrame`, after which the
existing axiometric and evolutionary characterization theorems apply.

**CONJECTURED / OPEN:** derive the common relational carrier and reversible codecs themselves from
still weaker observational requirements such as origin independence, recoverability, and coherent
comparison.  This file intentionally does not relabel that open representation theorem as proved.
-/

namespace NRRF627WeakRequirements

open NRRF627

universe u v w z q

/-- A relational return carrier.  `X` and `R` are not selected languages in `L`; they are the
language-independent occurrence and return carriers whose existence is the present representation
hypothesis. -/
structure CanonicalReturn (X : Type v) (R : Type w) where
  W : X → R
  E : Pole → R → X
  recov : ∀ p r, W (E p r) = r

/-- Reversible presentation of occurrences, returns, and orientation in every language. -/
structure PresentationFamily
    (L : Type u) (X : Type v) (R : Type w)
    (B : L → Type q) (Y : L → Type z) where
  occurrence : ∀ ℓ, X ≃ Y ℓ
  basis : ∀ ℓ, R ≃ B ℓ
  orientation : (ℓ : L) → Equiv.Perm Pole

/-- The translation-and-return portion of `TransFrame`, before adding `J` and `C`. -/
structure TranslationClosure
    (L : Type u) (B : L → Type v) (Y : L → Type w) where
  W : ∀ ℓ, Y ℓ → B ℓ
  E : ∀ ℓ, Pole → B ℓ → Y ℓ
  recov : ∀ ℓ p b, W ℓ (E ℓ p b) = b
  phi : ∀ ℓ m, B ℓ → B m
  phi_id : ∀ ℓ b, phi ℓ ℓ b = b
  phi_comp : ∀ ℓ m k b, phi m k (phi ℓ m b) = phi ℓ k b
  T : ∀ ℓ m, Y ℓ → Y m
  T_id : ∀ ℓ y, T ℓ ℓ y = y
  T_comp : ∀ ℓ m k y, T m k (T ℓ m y) = T ℓ k y
  T_ret : ∀ ℓ m y, W m (T ℓ m y) = phi ℓ m (W ℓ y)
  pi : L → L → Equiv.Perm Pole
  pi_id : ∀ ℓ, pi ℓ ℓ = Equiv.refl Pole
  pi_comp : ∀ ℓ m k p, pi m k (pi ℓ m p) = pi ℓ k p
  T_ext : ∀ ℓ m p b, T ℓ m (E ℓ p b) = E m (pi ℓ m p) (phi ℓ m b)

/-- The current weaker requirements: an origin-independent relational carrier plus reversible
presentation codecs.  No pairwise translation or commuting square is supplied as a field. -/
structure WeakRequirements
    (L : Type u) (X : Type v) (R : Type w)
    (B : L → Type q) (Y : L → Type z) where
  canonical : CanonicalReturn X R
  presentations : PresentationFamily L X R B Y

/-- Decode to the relational carrier and encode into the target presentation. -/
def deriveTranslationClosure
    {L : Type u} {X : Type v} {R : Type w}
    {B : L → Type q} {Y : L → Type z}
    (K : CanonicalReturn X R) (F : PresentationFamily L X R B Y) :
    TranslationClosure L B Y where
  W := fun ℓ y => F.basis ℓ (K.W ((F.occurrence ℓ).symm y))
  E := fun ℓ p b =>
    F.occurrence ℓ (K.E ((F.orientation ℓ).symm p) ((F.basis ℓ).symm b))
  recov := by
    intro ℓ p b
    simp [K.recov]
  phi := fun ℓ m b => F.basis m ((F.basis ℓ).symm b)
  phi_id := by
    intro ℓ b
    simp
  phi_comp := by
    intro ℓ m k b
    simp
  T := fun ℓ m y => F.occurrence m ((F.occurrence ℓ).symm y)
  T_id := by
    intro ℓ y
    simp
  T_comp := by
    intro ℓ m k y
    simp
  T_ret := by
    intro ℓ m y
    simp
  pi := fun ℓ m => (F.orientation ℓ).symm.trans (F.orientation m)
  pi_id := by
    intro ℓ
    ext p
    simp
  pi_comp := by
    intro ℓ m k p
    simp
  T_ext := by
    intro ℓ m p b
    simp

namespace TranslationClosure

variable {L : Type u} {B : L → Type v} {Y : L → Type w}

/-- Coherent translations are automatically invertible; no injectivity premise is needed. -/
def transEquiv (A : TranslationClosure L B Y) (ℓ m : L) : Y ℓ ≃ Y m where
  toFun := A.T ℓ m
  invFun := A.T m ℓ
  left_inv y := by rw [A.T_comp, A.T_id]
  right_inv y := by rw [A.T_comp, A.T_id]

/-- Basis comparison is likewise automatically invertible. -/
def basisEquiv (A : TranslationClosure L B Y) (ℓ m : L) : B ℓ ≃ B m where
  toFun := A.phi ℓ m
  invFun := A.phi m ℓ
  left_inv b := by rw [A.phi_comp, A.phi_id]
  right_inv b := by rw [A.phi_comp, A.phi_id]

end TranslationClosure

namespace WeakRequirements

variable {L : Type u} {X : Type v} {R : Type w}
variable {B : L → Type q} {Y : L → Type z}

/-- **Representation result (proved):** the current weak requirements construct the entire
translation-and-return layer. -/
def toTranslationClosure (Q : WeakRequirements L X R B Y) : TranslationClosure L B Y :=
  deriveTranslationClosure Q.canonical Q.presentations

/-- The return square is a codec consequence, not a field of `WeakRequirements`. -/
theorem return_square_is_derived
    (Q : WeakRequirements L X R B Y) (ℓ m : L) (y : Y ℓ) :
    Q.toTranslationClosure.W m (Q.toTranslationClosure.T ℓ m y) =
      Q.toTranslationClosure.phi ℓ m (Q.toTranslationClosure.W ℓ y) :=
  Q.toTranslationClosure.T_ret ℓ m y

/-- Translation back cancels because both maps pass through the same relational carrier. -/
theorem translation_inverse_is_derived
    (Q : WeakRequirements L X R B Y) (ℓ m : L) (y : Y ℓ) :
    Q.toTranslationClosure.T m ℓ (Q.toTranslationClosure.T ℓ m y) = y := by
  simp [toTranslationClosure, deriveTranslationClosure]

/-- A route through a temporary presentation equals direct re-expression. -/
theorem route_coherence_is_derived
    (Q : WeakRequirements L X R B Y) (ℓ m k : L) (y : Y ℓ) :
    Q.toTranslationClosure.T m k (Q.toTranslationClosure.T ℓ m y) =
      Q.toTranslationClosure.T ℓ k y := by
  simp [toTranslationClosure, deriveTranslationClosure]

end WeakRequirements

/-- Additional protocol needed for the specific polar-reversal and curvature layer of NRRF627. -/
structure PolarProtocol {X : Type v} {R : Type w} (K : CanonicalReturn X R) where
  J : X → X
  J_invol : ∀ x, J (J x) = x
  J_ret : ∀ x, K.W (J x) = K.W x
  J_ext : ∀ p r, J (K.E p r) = K.E (Pole.other p) r
  C : X → X
  C_idem : ∀ x, C (C x) = C x
  C_ret : ∀ x, K.W (C x) = K.W x

/-- Extend the derived translation closure to the full NRRF627 `TransFrame`.  Only the genuinely
additional `J`/`C` behavior is supplied; all cross-language maps and coherence laws remain derived. -/
def deriveTransFrame
    {L : Type u} {X : Type v} {R : Type w}
    {B : L → Type q} {Y : L → Type z}
    (K : CanonicalReturn X R) (F : PresentationFamily L X R B Y)
    (P : PolarProtocol K) : TransFrame L B Y where
  W := fun ℓ y => F.basis ℓ (K.W ((F.occurrence ℓ).symm y))
  E := fun ℓ p b =>
    F.occurrence ℓ (K.E ((F.orientation ℓ).symm p) ((F.basis ℓ).symm b))
  recov := by
    intro ℓ p b
    simp [K.recov]
  phi := fun ℓ m b => F.basis m ((F.basis ℓ).symm b)
  phi_id := by
    intro ℓ b
    simp
  phi_comp := by
    intro ℓ m k b
    simp
  T := fun ℓ m y => F.occurrence m ((F.occurrence ℓ).symm y)
  T_id := by
    intro ℓ y
    simp
  T_comp := by
    intro ℓ m k y
    simp
  T_ret := by
    intro ℓ m y
    simp
  pi := fun ℓ m => (F.orientation ℓ).symm.trans (F.orientation m)
  pi_id := by
    intro ℓ
    ext p
    simp
  pi_comp := by
    intro ℓ m k p
    simp
  T_ext := by
    intro ℓ m p b
    simp
  J := fun ℓ y => F.occurrence ℓ (P.J ((F.occurrence ℓ).symm y))
  J_invol := by
    intro ℓ y
    simp [P.J_invol]
  J_ret := by
    intro ℓ y
    simp [P.J_ret]
  J_ext := by
    intro ℓ p b
    simp [P.J_ext, perm_comm_other]
  T_J := by
    intro ℓ m y
    simp
  C := fun ℓ y => F.occurrence ℓ (P.C ((F.occurrence ℓ).symm y))
  C_idem := by
    intro ℓ y
    simp [P.C_idem]
  C_ret := by
    intro ℓ y
    simp [P.C_ret]
  T_C := by
    intro ℓ m y
    simp

section FullConsequences

variable {L : Type u} {X : Type v} {R : Type w}
variable {B : L → Type q} {Y : L → Type z}
variable (K : CanonicalReturn X R) (F : PresentationFamily L X R B Y)
variable (P : PolarProtocol K)

/-- NRRF627's axiometric characterization now applies to a frame whose translations were derived. -/
theorem axiometry_flows_from_derived_translation
    {Omega : Type*} (Q : ∀ ℓ, Y ℓ → Omega) :
    (((deriveTransFrame K F P).Invariant Q ∧
        (deriveTransFrame K F P).RespectsClosure Q) ↔
      (deriveTransFrame K F P).MeasuredByReturn Q) :=
  (deriveTransFrame K F P).axiometric_verdict_characterisation Q

/-- The evolutionary characterization is inherited by the derived full frame. -/
theorem evolution_flows_from_derived_translation
    {Omega : Type*} (Q : ∀ ℓ, Y ℓ → Omega) :
    (((∀ (g : Nat → L) (n : Nat) (y : Y (g 0)),
        Q (g n) ((deriveTransFrame K F P).evolve g n y) = Q (g 0) y) ∧
      (deriveTransFrame K F P).RespectsClosure Q) ↔
      (deriveTransFrame K F P).MeasuredByReturn Q) :=
  (deriveTransFrame K F P).evolutionary_verification_is_exactly_return_measurement Q

end FullConsequences

end NRRF627WeakRequirements

#print axioms NRRF627WeakRequirements.WeakRequirements.return_square_is_derived
#print axioms NRRF627WeakRequirements.WeakRequirements.translation_inverse_is_derived
#print axioms NRRF627WeakRequirements.deriveTransFrame
#print axioms NRRF627WeakRequirements.axiometry_flows_from_derived_translation
#print axioms NRRF627WeakRequirements.evolution_flows_from_derived_translation

