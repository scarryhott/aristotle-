import Mathlib
import NRRF627ClosureTranslationalFrameworkAxiometryASIEvolutionaryVerification

/-!
# NRRF630 — What *existence* and *naturality* fall out of the basic translational relation

The unified translational axiometry (`NRRF627.TransFrame`) posits nothing but a *relation between
languages*: pairwise translations `(phi, T, pi)` obeying the identity and coherence laws, a
verification return `W`, the two orientation presentations `E`, the polar reversal `J` and the
unitary-curvature partition `C`.

This module answers: **which objects are thereby forced to exist, and which structure maps are
thereby natural?**  Nothing new is assumed; every statement below is a consequence of the frame
laws alone.  The one extra hypothesis that appears, `Separated` (already defined in `NRRF627`), is
used only where a *uniqueness* claim genuinely needs it, and it is stated explicitly there.

## Contents

* **§1 Naturality, literally.**  The languages form a groupoid `Lang L` — exactly one comparison
  between any two languages, and it is invertible, so no language is the origin.  Occurrences and
  relational identities are *functors* `occFunctor`, `ideFunctor` on that groupoid; the return is a
  **natural transformation** `retNat : occFunctor ⟶ ideFunctor`; the reversal and the curvature
  representative are natural endomorphisms `revNat`, `curvNat` of the occurrence functor.
* **§2 Existence: the closure quotient.**  `retSurjective`; the quotient of occurrences by closure
  equality *exists and is already there*: `quotBasisEquiv ℓ : Quotient (ceqSetoid A ℓ) ≃ B ℓ`,
  natural in `ℓ` (`quotBasisEquiv_natural`).  So the basis of identities is not extra data — it is
  the closure quotient.
* **§3 Existence: a natural section of the return.**  `polarSection`: choosing one pole in one
  language produces a family of presentations `∀ ℓ, B ℓ → Y ℓ` that splits the return
  (`polarSection_ret`) and is natural for translation (`polarSection_natural`).  There are exactly
  two such polar splittings, exchanged by the reversal (`polarSection_rev`, `natural_polar_iff`,
  `polar_sections_are_a_parity`): the existence is free, the choice is a single `ℤ/2` bit.
* **§4 Existence: the universal verdict.**  `Ident A` — the colimit of the identity bases along the
  translations — exists, `univVerdict` is invariant and closure-respecting, and **every**
  invariant closure-respecting verdict factors through it *uniquely*
  (`universal_verdict_property`).  Hence the axiometric characterisation upgrades from "is a
  measurement of the return" to a universal property, with the measuring family unique
  (`measuring_family_unique`).
* **§5 No origin, representably.**  `identEquivBasis`: every language represents the universal
  object, and the representations differ exactly by translation (`identEquivBasis_comp`).
  `verdictEquiv`: invariant closure-respecting verdicts with values in `Ω` are in bijection with
  plain functions `B ℓ₀ → Ω`, for *any* language `ℓ₀`.
* **§6 The bundle** `existence_naturality_from_translation`.
-/

namespace NRRF630

universe u v w

/-! ## §1a  The language groupoid -/

/-- The languages, viewed as the objects of the comparison groupoid: exactly one comparison
between any two languages, and it is invertible.  No language is the origin. -/
def Lang (L : Type u) : Type u := L

instance instCategoryLang (L : Type u) : CategoryTheory.Category.{0} (Lang L) where
  Hom _ _ := PUnit
  id _ := PUnit.unit
  comp _ _ := PUnit.unit
  id_comp := by rintro _ _ ⟨⟩; rfl
  comp_id := by rintro _ _ ⟨⟩; rfl
  assoc := by rintro _ _ _ _ ⟨⟩ ⟨⟩ ⟨⟩; rfl

instance instGroupoidLang (L : Type u) : CategoryTheory.Groupoid.{0} (Lang L) where
  inv _ := PUnit.unit
  inv_comp := by rintro _ _ ⟨⟩; rfl
  comp_inv := by rintro _ _ ⟨⟩; rfl

end NRRF630

namespace NRRF627

namespace TransFrame

open Function NRRF630 CategoryTheory

universe u v w

/-! ## §1b  Naturality, in the literal categorical sense -/

section Categorical

variable {L : Type u} {B Y : L → Type w} (A : TransFrame L B Y)

/-- Occurrences, as a functor on the language groupoid: a language is sent to its occurrences and
the comparison `ℓ ⟶ m` to the translation `T ℓ m`. -/
def occFunctor : Lang L ⥤ Type w where
  obj ℓ := Y ℓ
  map {ℓ m} _ := A.T ℓ m
  map_id ℓ := funext fun u => A.T_id ℓ u
  map_comp {ℓ m k} _ _ := funext fun u => (A.T_comp ℓ m k u).symm

/-- Relational identities, as a functor on the language groupoid. -/
def ideFunctor : Lang L ⥤ Type w where
  obj ℓ := B ℓ
  map {ℓ m} _ := A.phi ℓ m
  map_id ℓ := funext fun b => A.phi_id ℓ b
  map_comp {ℓ m k} _ _ := funext fun b => (A.phi_comp ℓ m k b).symm

/-- Every comparison of languages is an isomorphism of occurrences: the relation is a groupoid, so
translation can never lose information. -/
theorem occFunctor_map_isIso {ℓ m : Lang L} (f : ℓ ⟶ m) : IsIso ((occFunctor A).map f) :=
  (occFunctor A).map_isIso f

theorem ideFunctor_map_isIso {ℓ m : Lang L} (f : ℓ ⟶ m) : IsIso ((ideFunctor A).map f) :=
  (ideFunctor A).map_isIso f

/-- **The verification return is a natural transformation.**  Naturality is exactly the return
square `T_ret`: verifying after translating is translating after verifying. -/
def retNat : occFunctor A ⟶ ideFunctor A where
  app ℓ := A.W ℓ
  naturality {ℓ m} _ := funext fun u => A.T_ret ℓ m u

@[simp] theorem retNat_app (ℓ : Lang L) (u : Y ℓ) : (retNat A).app ℓ u = A.W ℓ u := rfl

/-- **The polar reversal is a natural endomorphism of the occurrence functor.** -/
def revNat : occFunctor A ⟶ occFunctor A where
  app ℓ := A.J ℓ
  naturality {ℓ m} _ := funext fun u => (A.T_J ℓ m u).symm

/-- The reversal is a natural *automorphism*: it is its own inverse. -/
theorem revNat_involutive (ℓ : Lang L) (u : Y ℓ) :
    (revNat A).app ℓ ((revNat A).app ℓ u) = u := A.J_invol ℓ u

/-- **The unitary-curvature representative is a natural endomorphism** of the occurrence functor,
idempotent and invisible to the return. -/
def curvNat : occFunctor A ⟶ occFunctor A where
  app ℓ := A.C ℓ
  naturality {ℓ m} _ := funext fun u => (A.T_C ℓ m u).symm

theorem curvNat_idem (ℓ : Lang L) (u : Y ℓ) :
    (curvNat A).app ℓ ((curvNat A).app ℓ u) = (curvNat A).app ℓ u := A.C_idem ℓ u

/-- The natural splitting of §3, read categorically: a natural transformation of the identity
functor into the occurrence functor, whose composite with the return is the identity. -/
def secNat (ℓ₀ : L) (p₀ : Pole) : ideFunctor A ⟶ occFunctor A where
  app ℓ b := A.E ℓ (A.pi ℓ₀ ℓ p₀) b
  naturality {ℓ m} _ := funext fun b =>
    (show A.T ℓ m (A.E ℓ (A.pi ℓ₀ ℓ p₀) b) = A.E m (A.pi ℓ₀ m p₀) (A.phi ℓ m b) by
      rw [A.T_ext, A.pi_comp]).symm

theorem secNat_retNat (ℓ₀ : L) (p₀ : Pole) : secNat A ℓ₀ p₀ ≫ retNat A = 𝟙 (ideFunctor A) := by
  ext ℓ b
  exact A.recov ℓ _ b

end Categorical

variable {L : Type u} {B : L → Type v} {Y : L → Type w} (A : TransFrame L B Y)

/-! ## §2  Existence: the closure quotient is already the basis of identities -/

/-- The return of every language is surjective: each relational identity is returned by its own
presentations. -/
theorem retSurjective (ℓ : L) : Surjective (A.W ℓ) :=
  fun b => ⟨A.E ℓ Pole.zero b, A.recov ℓ Pole.zero b⟩

/-- Closure equality, as a setoid on the occurrences of a language. -/
def ceqSetoid (ℓ : L) : Setoid (Y ℓ) :=
  ⟨CEq (A.W ℓ), ceq_equivalence (A.W ℓ)⟩

/-- **The closure quotient exists and is the basis of relational identities.**  Quotienting the
occurrences of a language by closure equality returns exactly `B ℓ`: the identities are not extra
data, they are the closure quotient. -/
def quotBasisEquiv (ℓ : L) : Quotient (A.ceqSetoid ℓ) ≃ B ℓ where
  toFun := Quotient.lift (A.W ℓ) fun _ _ h => h
  invFun b := Quotient.mk _ (A.E ℓ Pole.zero b)
  left_inv := by
    refine Quotient.ind fun u => ?_
    exact Quotient.sound (show A.W ℓ (A.E ℓ Pole.zero (A.W ℓ u)) = A.W ℓ u by rw [A.recov])
  right_inv b := A.recov ℓ Pole.zero b

@[simp] theorem quotBasisEquiv_mk (ℓ : L) (u : Y ℓ) :
    A.quotBasisEquiv ℓ (Quotient.mk _ u) = A.W ℓ u := rfl

/-- The closure quotient is natural: translation descends to the quotient and, read through the
identification, is exactly translation of relational identities. -/
theorem quotBasisEquiv_natural (ℓ m : L) (q : Quotient (A.ceqSetoid ℓ)) :
    A.quotBasisEquiv m (Quotient.map (A.T ℓ m) (fun _ _ h => (A.ceq_iff ℓ m _ _).1 h) q)
      = A.phi ℓ m (A.quotBasisEquiv ℓ q) := by
  induction q using Quotient.ind with
  | _ u => simpa using A.T_ret ℓ m u

/-! ## §3  Existence: a natural splitting of the return, unique up to one bit -/

section Splitting

variable (ℓ₀ : L) (p₀ : Pole)

/-- The presentation family obtained by choosing one pole in one language and translating the
choice everywhere: `polarSection A ℓ₀ p₀ ℓ` presents an identity of `ℓ` in the orientation that
`ℓ₀`'s choice becomes in `ℓ`. -/
def polarSection (ℓ : L) (b : B ℓ) : Y ℓ := A.E ℓ (A.pi ℓ₀ ℓ p₀) b

/-- It splits the return. -/
@[simp] theorem polarSection_ret (ℓ : L) (b : B ℓ) :
    A.W ℓ (A.polarSection ℓ₀ p₀ ℓ b) = b := A.recov _ _ _

/-- **The splitting is natural for translation.**  No coherence had to be imposed: it follows from
the composition law for the orientation relabelling. -/
theorem polarSection_natural (ℓ m : L) (b : B ℓ) :
    A.T ℓ m (A.polarSection ℓ₀ p₀ ℓ b) = A.polarSection ℓ₀ p₀ m (A.phi ℓ m b) := by
  unfold polarSection
  rw [A.T_ext, A.pi_comp]

/-- The two polar splittings are exchanged by the reversal. -/
theorem polarSection_rev (ℓ : L) (b : B ℓ) :
    A.J ℓ (A.polarSection ℓ₀ p₀ ℓ b) = A.polarSection ℓ₀ (Pole.other p₀) ℓ b := by
  unfold polarSection
  rw [A.J_ext, ← perm_comm_other]

end Splitting

/-- **Naturality pins the orientation choice.**  A family of orientations gives a natural family of
presentations exactly when it is the translate of its value at one language.  (Necessity uses
separation; sufficiency is free.) -/
theorem natural_polar_iff (hsep : A.Separated) (ℓ₀ : L) (hne : Nonempty (B ℓ₀)) (p : L → Pole) :
    (∀ ℓ m b, A.T ℓ m (A.E ℓ (p ℓ) b) = A.E m (p m) (A.phi ℓ m b)) ↔
      ∀ ℓ, p ℓ = A.pi ℓ₀ ℓ (p ℓ₀) := by
  constructor
  · intro hnat ℓ
    obtain ⟨b⟩ := hne
    have h := hnat ℓ₀ ℓ b
    rw [A.T_ext] at h
    exact (A.E_inj_pole hsep ℓ _ h).symm
  · intro hp ℓ m b
    rw [A.T_ext, hp ℓ, hp m, A.pi_comp]

/-- **The existence is free, the choice is a parity.**  Any two natural families of orientations
either agree everywhere or are everywhere opposite: the natural polar splittings of the return
form a `ℤ/2`. -/
theorem polar_sections_are_a_parity (hsep : A.Separated) (ℓ₀ : L) (hne : Nonempty (B ℓ₀))
    (p q : L → Pole)
    (hp : ∀ ℓ m b, A.T ℓ m (A.E ℓ (p ℓ) b) = A.E m (p m) (A.phi ℓ m b))
    (hq : ∀ ℓ m b, A.T ℓ m (A.E ℓ (q ℓ) b) = A.E m (q m) (A.phi ℓ m b)) :
    (∀ ℓ, p ℓ = q ℓ) ∨ (∀ ℓ, p ℓ = Pole.other (q ℓ)) := by
  have hp' := (A.natural_polar_iff hsep ℓ₀ hne p).1 hp
  have hq' := (A.natural_polar_iff hsep ℓ₀ hne q).1 hq
  rcases eq_or_ne (p ℓ₀) (q ℓ₀) with h | h
  · left; intro ℓ; rw [hp' ℓ, hq' ℓ, h]
  · right
    intro ℓ
    have hpq : p ℓ₀ = Pole.other (q ℓ₀) := by
      rw [(Pole.ne_iff (p ℓ₀) (q ℓ₀)).1 h, Pole.other_other]
    rw [hp' ℓ, hq' ℓ, hpq, perm_comm_other]

/-! ## §4  Existence: the universal verdict -/

/-- Identities of different languages, related when one translates to the other. -/
def identSetoid : Setoid (Σ ℓ : L, B ℓ) where
  r x y := A.phi x.1 y.1 x.2 = y.2
  iseqv := by
    refine ⟨fun x => A.phi_id x.1 x.2, ?_, ?_⟩
    · rintro ⟨ℓ, b⟩ ⟨m, c⟩ (h : A.phi ℓ m b = c)
      show A.phi m ℓ c = b
      rw [← h, A.phi_phi]
    · rintro ⟨ℓ, b⟩ ⟨m, c⟩ ⟨k, d⟩ (h₁ : A.phi ℓ m b = c) (h₂ : A.phi m k c = d)
      show A.phi ℓ k b = d
      rw [← h₂, ← h₁, A.phi_comp]

/-- **The universal relational identity.**  The colimit of the identity bases along the
translations: an identity, taken independently of the language that expresses it. -/
def Ident : Type max u v := Quotient A.identSetoid

/-- The class of an identity of a given language. -/
def ident (ℓ : L) (b : B ℓ) : A.Ident := Quotient.mk _ ⟨ℓ, b⟩

theorem ident_translate (ℓ m : L) (b : B ℓ) : A.ident m (A.phi ℓ m b) = A.ident ℓ b :=
  Quotient.sound (show A.phi m ℓ (A.phi ℓ m b) = b by rw [A.phi_phi])

/-- The universal verdict: return, then forget the language. -/
def univVerdict (ℓ : L) (u : Y ℓ) : A.Ident := A.ident ℓ (A.W ℓ u)

theorem univVerdict_invariant : A.Invariant A.univVerdict := by
  intro ℓ m u
  show A.ident m (A.W m (A.T ℓ m u)) = A.ident ℓ (A.W ℓ u)
  rw [A.T_ret, A.ident_translate]

theorem univVerdict_respects : A.RespectsClosure A.univVerdict := by
  intro ℓ u v h
  show A.ident ℓ (A.W ℓ u) = A.ident ℓ (A.W ℓ v)
  rw [h]

theorem univVerdict_surjective : Surjective (fun x : Σ ℓ : L, Y ℓ => A.univVerdict x.1 x.2) := by
  refine Quotient.ind fun x => ?_
  obtain ⟨ℓ, b⟩ := x
  refine ⟨⟨ℓ, A.E ℓ Pole.zero b⟩, ?_⟩
  show A.ident ℓ (A.W ℓ (A.E ℓ Pole.zero b)) = _
  rw [A.recov]
  rfl

/-- **The universal property of the verification return.**  A verdict is language-independent and
closure-respecting *exactly* when it factors through the universal verdict — and then the
factoring function is unique.  Existence and uniqueness both fall out of the translational
relation alone. -/
theorem universal_verdict_property {Ω : Type*} (Q : ∀ ℓ, Y ℓ → Ω) :
    (A.Invariant Q ∧ A.RespectsClosure Q) ↔
      ∃! f : A.Ident → Ω, ∀ ℓ u, Q ℓ u = f (A.univVerdict ℓ u) := by
  constructor
  · intro hQ
    obtain ⟨q, hq, hQq⟩ := (A.axiometric_verdict_characterisation Q).1 hQ
    refine ⟨Quotient.lift (fun x : Σ ℓ : L, B ℓ => q x.1 x.2) ?_, ?_, ?_⟩
    · rintro ⟨ℓ, b⟩ ⟨m, c⟩ (h : A.phi ℓ m b = c)
      show q ℓ b = q m c
      rw [← h, hq]
    · intro ℓ u
      exact hQq ℓ u
    · intro g hg
      funext t
      obtain ⟨⟨ℓ, u⟩, rfl⟩ := A.univVerdict_surjective t
      exact (hg ℓ u).symm.trans (hQq ℓ u)
  · rintro ⟨f, hf, -⟩
    constructor
    · intro ℓ m u
      rw [hf, hf, A.univVerdict_invariant]
    · intro ℓ u v h
      rw [hf, hf]
      exact congrArg f (A.univVerdict_respects ℓ u v h)

/-- The measuring family of an axiometric verdict is unique: two translation-compatible families
of measurements of the return that agree as verdicts agree outright. -/
theorem measuring_family_unique {Ω : Type*} (q q' : ∀ ℓ, B ℓ → Ω)
    (h : ∀ ℓ u, q ℓ (A.W ℓ u) = q' ℓ (A.W ℓ u)) : ∀ ℓ b, q ℓ b = q' ℓ b := by
  intro ℓ b
  obtain ⟨u, rfl⟩ := A.retSurjective ℓ b
  exact h ℓ u

/-! ## §5  No origin, representably -/

/-- **Every language represents the universal identity.**  The colimit is not built over a
privileged language: any one of them presents it, and the presentations differ exactly by
translation. -/
def identEquivBasis (ℓ₀ : L) : A.Ident ≃ B ℓ₀ where
  toFun := Quotient.lift (fun x : Σ ℓ : L, B ℓ => A.phi x.1 ℓ₀ x.2) (by
    rintro ⟨ℓ, b⟩ ⟨m, c⟩ (h : A.phi ℓ m b = c)
    show A.phi ℓ ℓ₀ b = A.phi m ℓ₀ c
    rw [← h, A.phi_comp])
  invFun b := A.ident ℓ₀ b
  left_inv := by
    refine Quotient.ind fun x => ?_
    obtain ⟨ℓ, b⟩ := x
    exact Quotient.sound (show A.phi ℓ₀ ℓ (A.phi ℓ ℓ₀ b) = b by rw [A.phi_phi])
  right_inv b := by
    show A.phi ℓ₀ ℓ₀ b = b
    rw [A.phi_id]

@[simp] theorem identEquivBasis_ident (ℓ₀ ℓ : L) (b : B ℓ) :
    A.identEquivBasis ℓ₀ (A.ident ℓ b) = A.phi ℓ ℓ₀ b := rfl

/-- Changing the representing language is exactly translating. -/
theorem identEquivBasis_comp (ℓ₀ m : L) (t : A.Ident) :
    A.identEquivBasis m t = A.phi ℓ₀ m (A.identEquivBasis ℓ₀ t) := by
  induction t using Quotient.ind with
  | _ x =>
      obtain ⟨ℓ, b⟩ := x
      show A.phi ℓ m b = A.phi ℓ₀ m (A.phi ℓ ℓ₀ b)
      rw [A.phi_comp]

/-- **The axiometric verdicts are exactly the functions on one language's identities.**  For any
choice of language `ℓ₀`, the language-independent closure-respecting verdicts with values in `Ω`
are in bijection with plain functions `B ℓ₀ → Ω`: the whole objective content of the frame is
carried by any single language's basis of relational identities. -/
def verdictEquiv {Ω : Type*} (ℓ₀ : L) :
    {Q : ∀ ℓ, Y ℓ → Ω // A.Invariant Q ∧ A.RespectsClosure Q} ≃ (B ℓ₀ → Ω) where
  toFun Q b := Q.1 ℓ₀ (A.E ℓ₀ Pole.zero b)
  invFun g := ⟨fun ℓ u => g (A.phi ℓ ℓ₀ (A.W ℓ u)), by
      constructor
      · intro ℓ m u
        show g (A.phi m ℓ₀ (A.W m (A.T ℓ m u))) = g (A.phi ℓ ℓ₀ (A.W ℓ u))
        rw [A.T_ret, A.phi_comp]
      · intro ℓ u v h
        show g (A.phi ℓ ℓ₀ (A.W ℓ u)) = g (A.phi ℓ ℓ₀ (A.W ℓ v))
        rw [h]⟩
  left_inv := by
    rintro ⟨Q, hQ⟩
    obtain ⟨q, hq, hQq⟩ := (A.axiometric_verdict_characterisation Q).1 hQ
    apply Subtype.ext
    funext ℓ u
    show Q ℓ₀ (A.E ℓ₀ Pole.zero (A.phi ℓ ℓ₀ (A.W ℓ u))) = Q ℓ u
    rw [hQq, hQq, A.recov, hq]
  right_inv g := by
    funext b
    show g (A.phi ℓ₀ ℓ₀ (A.W ℓ₀ (A.E ℓ₀ Pole.zero b))) = g b
    rw [A.recov, A.phi_id]

/-! ## §6  The bundle -/

/-- **What existence and naturality fall out of the basic translational relation.**

From the frame laws alone:

1. the return, the reversal and the curvature representative are natural for translation
   (categorically: `retNat`, `revNat`, `curvNat` on the language groupoid);
2. the basis of relational identities *is* the quotient of occurrences by closure equality, and
   that identification is natural;
3. a natural splitting of the return exists, obtained by translating a single choice of pole;
4. the universal relational identity exists, and every language-independent closure-respecting
   verdict factors through it uniquely;
5. every language represents that universal object, so no language is the origin. -/
theorem existence_naturality_from_translation {Ω : Type*} (ℓ₀ : L) (p₀ : Pole) :
    -- 1. naturality of the return, the reversal and the curvature representative
    (∀ (ℓ m : L) (u : Y ℓ), A.W m (A.T ℓ m u) = A.phi ℓ m (A.W ℓ u)) ∧
    (∀ (ℓ m : L) (u : Y ℓ), A.T ℓ m (A.J ℓ u) = A.J m (A.T ℓ m u)) ∧
    (∀ (ℓ m : L) (u : Y ℓ), A.T ℓ m (A.C ℓ u) = A.C m (A.T ℓ m u)) ∧
    -- 2. the identities are the closure quotient, naturally
    (∀ ℓ : L, ∃ e : Quotient (A.ceqSetoid ℓ) ≃ B ℓ, ∀ u : Y ℓ, e (Quotient.mk _ u) = A.W ℓ u) ∧
    -- 3. a natural splitting of the return exists
    (∃ s : ∀ ℓ, B ℓ → Y ℓ, (∀ ℓ b, A.W ℓ (s ℓ b) = b) ∧
        ∀ ℓ m b, A.T ℓ m (s ℓ b) = s m (A.phi ℓ m b)) ∧
    -- 4. the universal verdict, with its universal property
    (A.Invariant A.univVerdict ∧ A.RespectsClosure A.univVerdict ∧
      ∀ Q : ∀ ℓ, Y ℓ → Ω, (A.Invariant Q ∧ A.RespectsClosure Q) ↔
        ∃! f : A.Ident → Ω, ∀ ℓ u, Q ℓ u = f (A.univVerdict ℓ u)) ∧
    -- 5. every language represents it
    (∃ e : A.Ident ≃ B ℓ₀, ∀ (ℓ : L) (b : B ℓ), e (A.ident ℓ b) = A.phi ℓ ℓ₀ b) :=
  ⟨A.T_ret, A.T_J, A.T_C, fun ℓ => ⟨A.quotBasisEquiv ℓ, fun _ => rfl⟩,
    ⟨A.polarSection ℓ₀ p₀, A.polarSection_ret ℓ₀ p₀, A.polarSection_natural ℓ₀ p₀⟩,
    ⟨A.univVerdict_invariant, A.univVerdict_respects,
      fun Q => A.universal_verdict_property Q⟩,
    ⟨A.identEquivBasis ℓ₀, fun _ _ => rfl⟩⟩

end TransFrame

end NRRF627

/-! ## Axiom audit -/

namespace NRRF630

#print axioms NRRF627.TransFrame.retNat
#print axioms NRRF627.TransFrame.quotBasisEquiv
#print axioms NRRF627.TransFrame.polarSection_natural
#print axioms NRRF627.TransFrame.polar_sections_are_a_parity
#print axioms NRRF627.TransFrame.universal_verdict_property
#print axioms NRRF627.TransFrame.verdictEquiv
#print axioms NRRF627.TransFrame.existence_naturality_from_translation

end NRRF630
