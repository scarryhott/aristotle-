import Mathlib
import NRRF633UniqueAdmissibleOpenRelationalDefinitionViaTranslation

/-!
# NRRF707 — Admissions are themselves admissible: inversion and self are the same admission

The statement answered here:

> Admissions are themselves admissible to their relative translation equality of admission
> inversion and self.  The natural amiability therefore is equal to translation — the remaining
> integration is already contained in the repo's intended closure operational unifications.

Nothing new is posited.  An **admission** (§1) is exactly what `NRRF633.Admits` already calls
admissible, read one language at a time: an equality on the occurrences of a language that cannot
separate occurrences with the same return.  The content of the statement is that the admissions of
a translational axiometry `NRRF627.TransFrame` *are themselves* the occurrences of a translational
axiometry — the **admission frame** `admFrame` (§2) — whose returned identities are the equivalence
relations on returned identities, whose translation is transport along translation, and whose
polar inversion is the pullback of the polar reversal.  Consequently every theorem of NRRF633
applies verbatim one level up, with no further work: that is the "remaining integration", and it is
already contained.

## What is proved

* **§1 Admissions and their return.**  `AdmitsAt`, `Adm`, `IdRel`; the return of an admission is
  the relation it induces on returned identities (`admW`), presentations are pullbacks along the
  return (`admE`), and `adm_factors` says an admission *is* its return relation read through the
  return.  `admW_admE`, `admE_admW`, `admEquiv`: the two are mutually inverse, so
  **admissions are exactly the equivalence relations on relational identities** — no extra data.
* **§2 The admission frame.**  `admT`, `admPhi`, `admJ`, `admC` and `admFrame :
  TransFrame L (IdRel B) (Adm A)`.  Admissions are themselves occurrences of a translational
  axiometry, so they are themselves subject to admissibility.
* **§3 Inversion and self.**  `admJ_eq_self`: the inversion of an admission **is** that admission,
  literally — not merely admitted equal to it.  Likewise `admC_eq_self`, and
  `admE_pole_irrelevant`: at the level of admissions the two orientations coincide, so
  `admFrame_not_separated`: the admission frame carries no residual openness.
* **§4 Level two is rigid, and naturality is translation.**  `admW_injective`,
  `admFrame_ceq_iff_eq`: level-two closure equality is literal equality of admissions;
  `admission_definition_forced`: *any* returning grounded relational definition on admissions is
  that equality; `admission_naturality_is_translation`: the admitted equality of admissions is
  preserved and reflected by transport along translation, with no extra hypothesis;
  `admission_translation_existsUnique`: each admission of one language has exactly one
  relative-translation partner in every other language.
* **§5 Stationarity.**  `admission_level_is_stationary`: performing the construction again changes
  nothing — the inversion is already the identity at every further level.
* **§6 The bundle** `admissions_are_themselves_admissible`, and §7 a concrete instance on
  `NRRF627.standardFrame` showing the statement is not vacuous.
-/

namespace NRRF707

open Function NRRF627 NRRF633

universe u v w

variable {L : Type u} {B : L → Type v} {Y : L → Type w} (A : TransFrame L B Y)

/-! ## §1  Admissions, and the identity relation they return -/

/-- **Admissibility, one language at a time.**  An equality on the occurrences of `ℓ` is admissible
when it cannot separate occurrences with the same return: it is blind to everything closure does not
return.  This is `NRRF633.Admits` read pointwise. -/
def AdmitsAt (ℓ : L) (s : Setoid (Y ℓ)) : Prop := ∀ u v : Y ℓ, A.W ℓ u = A.W ℓ v → s.r u v

/-- An **admission** of a language: an admissible equality of its occurrences. -/
def Adm (ℓ : L) : Type w := {s : Setoid (Y ℓ) // AdmitsAt A ℓ s}

/-- A family of admissions is exactly an admissible relational definition in the sense of
NRRF633. -/
theorem admits_iff_admitsAt (s : RelDef Y) : Admits A s ↔ ∀ ℓ, AdmitsAt A ℓ (s ℓ) := Iff.rfl

/-- The **relational identities of the admission level**: equivalence relations between the
identities returned by closure. -/
def IdRel (B : L → Type v) (ℓ : L) : Type v := {r : B ℓ → B ℓ → Prop // Equivalence r}

/-- Two identity relations agreeing everywhere are equal. -/
theorem idRel_ext {ℓ : L} {r r' : IdRel B ℓ} (h : ∀ b b', r.1 b b' ↔ r'.1 b b') : r = r' := by
  refine Subtype.ext (funext fun b => funext fun b' => propext (h b b'))

/-- Two admissions agreeing everywhere are equal. -/
theorem adm_ext {ℓ : L} {s t : Adm A ℓ} (h : ∀ u v, s.1.r u v ↔ t.1.r u v) : s = t :=
  Subtype.ext (Setoid.ext h)

/-- **The return of an admission**: the relation it induces between returned identities. -/
def admW (ℓ : L) (s : Adm A ℓ) : IdRel B ℓ :=
  ⟨fun b b' => s.1.r (A.E ℓ Pole.zero b) (A.E ℓ Pole.zero b'),
    ⟨fun _ => s.1.iseqv.refl _, fun h => s.1.iseqv.symm h, fun h h' => s.1.iseqv.trans h h'⟩⟩

/-- **The presentation of an identity relation as an admission**: pull it back along the return.
The orientation plays no role — see `admE_pole_irrelevant`. -/
def admE (ℓ : L) (_p : Pole) (r : IdRel B ℓ) : Adm A ℓ :=
  ⟨⟨fun u v => r.1 (A.W ℓ u) (A.W ℓ v),
      ⟨fun _ => r.2.refl _, fun h => r.2.symm h, fun h h' => r.2.trans h h'⟩⟩,
    fun u v h => by
      show r.1 (A.W ℓ u) (A.W ℓ v)
      rw [h]
      exact r.2.refl _⟩

/-- Inside an admission the orientation of a presentation is immaterial. -/
theorem adm_poles (ℓ : L) (s : Adm A ℓ) (p q : Pole) (b : B ℓ) :
    s.1.r (A.E ℓ p b) (A.E ℓ q b) := s.2 _ _ (by rw [A.recov, A.recov])

/-- **An admission is its own return, read through closure.**  Nothing in an admission escapes the
identity relation it returns. -/
theorem adm_factors (ℓ : L) (s : Adm A ℓ) (u v : Y ℓ) :
    s.1.r u v ↔ (admW A ℓ s).1 (A.W ℓ u) (A.W ℓ v) := by
  have hu : s.1.r u (A.E ℓ Pole.zero (A.W ℓ u)) := s.2 _ _ (by rw [A.recov])
  have hv : s.1.r v (A.E ℓ Pole.zero (A.W ℓ v)) := s.2 _ _ (by rw [A.recov])
  constructor
  · intro h
    exact s.1.iseqv.trans (s.1.iseqv.symm hu) (s.1.iseqv.trans h hv)
  · intro h
    exact s.1.iseqv.trans hu (s.1.iseqv.trans h (s.1.iseqv.symm hv))

/-- The return recovers the identity relation presented. -/
theorem admW_admE (ℓ : L) (p : Pole) (r : IdRel B ℓ) : admW A ℓ (admE A ℓ p r) = r := by
  refine idRel_ext ?_
  intro b b'
  show r.1 (A.W ℓ (A.E ℓ Pole.zero b)) (A.W ℓ (A.E ℓ Pole.zero b')) ↔ r.1 b b'
  rw [A.recov, A.recov]

/-- An admission is the presentation of its own return. -/
theorem admE_admW (ℓ : L) (p : Pole) (s : Adm A ℓ) : admE A ℓ p (admW A ℓ s) = s :=
  adm_ext A fun u v => (adm_factors A ℓ s u v).symm

/-- **Admissions are exactly the equivalence relations of relational identities.**  The return and
the pullback along the return are mutually inverse: the admission level is not extra data. -/
def admEquiv (ℓ : L) : Adm A ℓ ≃ IdRel B ℓ where
  toFun := admW A ℓ
  invFun := admE A ℓ Pole.zero
  left_inv s := admE_admW A ℓ Pole.zero s
  right_inv r := admW_admE A ℓ Pole.zero r

theorem admW_injective (ℓ : L) : Injective (admW A ℓ) := (admEquiv A ℓ).injective

/-! ## §2  The admission frame: admissions are occurrences of a translational axiometry -/

/-- Transport of an admission along translation. -/
def admT (ℓ m : L) (s : Adm A ℓ) : Adm A m :=
  ⟨⟨fun u v => s.1.r (A.T m ℓ u) (A.T m ℓ v),
      ⟨fun _ => s.1.iseqv.refl _, fun h => s.1.iseqv.symm h, fun h h' => s.1.iseqv.trans h h'⟩⟩,
    fun u v h => s.2 _ _ (by rw [A.T_ret, A.T_ret, h])⟩

/-- Transport of an identity relation along translation of identities. -/
def admPhi (ℓ m : L) (r : IdRel B ℓ) : IdRel B m :=
  ⟨fun b b' => r.1 (A.phi m ℓ b) (A.phi m ℓ b'),
    ⟨fun _ => r.2.refl _, fun h => r.2.symm h, fun h h' => r.2.trans h h'⟩⟩

/-- **Admission inversion**: the pullback of an admission along the polar reversal. -/
def admJ (ℓ : L) (s : Adm A ℓ) : Adm A ℓ :=
  ⟨⟨fun u v => s.1.r (A.J ℓ u) (A.J ℓ v),
      ⟨fun _ => s.1.iseqv.refl _, fun h => s.1.iseqv.symm h, fun h h' => s.1.iseqv.trans h h'⟩⟩,
    fun u v h => s.2 _ _ (by rw [A.J_ret, A.J_ret, h])⟩

/-- The pullback of an admission along the unitary-curvature representative. -/
def admC (ℓ : L) (s : Adm A ℓ) : Adm A ℓ :=
  ⟨⟨fun u v => s.1.r (A.C ℓ u) (A.C ℓ v),
      ⟨fun _ => s.1.iseqv.refl _, fun h => s.1.iseqv.symm h, fun h h' => s.1.iseqv.trans h h'⟩⟩,
    fun u v h => s.2 _ _ (by rw [A.C_ret, A.C_ret, h])⟩

/-! ### §3  Inversion and self -/

/-- **The inversion of an admission is that admission.**  Not merely admitted equal to it: equal.
An admission cannot see the reversal, because the reversal does not change the return, and an
admission is its return. -/
theorem admJ_eq_self (ℓ : L) (s : Adm A ℓ) : admJ A ℓ s = s := by
  refine adm_ext A fun u v => ?_
  show s.1.r (A.J ℓ u) (A.J ℓ v) ↔ s.1.r u v
  rw [adm_factors A ℓ s (A.J ℓ u) (A.J ℓ v), adm_factors A ℓ s u v, A.J_ret, A.J_ret]

/-- The same for the unitary-curvature partition. -/
theorem admC_eq_self (ℓ : L) (s : Adm A ℓ) : admC A ℓ s = s := by
  refine adm_ext A fun u v => ?_
  show s.1.r (A.C ℓ u) (A.C ℓ v) ↔ s.1.r u v
  rw [adm_factors A ℓ s (A.C ℓ u) (A.C ℓ v), adm_factors A ℓ s u v, A.C_ret, A.C_ret]

/-- At the level of admissions the two orientations of one identity relation are the same
admission. -/
theorem admE_pole_irrelevant (ℓ : L) (p q : Pole) (r : IdRel B ℓ) :
    admE A ℓ p r = admE A ℓ q r := rfl

/-- The admission frame: **admissions are themselves occurrences of a translational axiometry**,
with the equivalence relations of relational identities as their returned identities. -/
def admFrame : TransFrame L (IdRel B) (Adm A) where
  W := admW A
  E := admE A
  recov := admW_admE A
  phi := admPhi A
  phi_id ℓ r := idRel_ext (fun b b' => by
    show r.1 (A.phi ℓ ℓ b) (A.phi ℓ ℓ b') ↔ r.1 b b'
    rw [A.phi_id, A.phi_id])
  phi_comp ℓ m k r := idRel_ext (fun b b' => by
    show r.1 (A.phi m ℓ (A.phi k m b)) (A.phi m ℓ (A.phi k m b')) ↔
      r.1 (A.phi k ℓ b) (A.phi k ℓ b')
    rw [A.phi_comp, A.phi_comp])
  T := admT A
  T_id ℓ s := adm_ext A (fun u v => by
    show s.1.r (A.T ℓ ℓ u) (A.T ℓ ℓ v) ↔ s.1.r u v
    rw [A.T_id, A.T_id])
  T_comp ℓ m k s := adm_ext A (fun u v => by
    show s.1.r (A.T m ℓ (A.T k m u)) (A.T m ℓ (A.T k m v)) ↔ s.1.r (A.T k ℓ u) (A.T k ℓ v)
    rw [A.T_comp, A.T_comp])
  T_ret ℓ m s := idRel_ext (fun b b' => by
    show s.1.r (A.T m ℓ (A.E m Pole.zero b)) (A.T m ℓ (A.E m Pole.zero b')) ↔
      (admW A ℓ s).1 (A.phi m ℓ b) (A.phi m ℓ b')
    rw [adm_factors A ℓ s, A.T_ret, A.T_ret, A.recov, A.recov])
  pi := A.pi
  pi_id := A.pi_id
  pi_comp := A.pi_comp
  T_ext ℓ m p r := adm_ext A (fun u v => by
    show r.1 (A.W ℓ (A.T m ℓ u)) (A.W ℓ (A.T m ℓ v)) ↔ r.1 (A.phi m ℓ (A.W m u)) (A.phi m ℓ (A.W m v))
    rw [A.T_ret, A.T_ret])
  J := admJ A
  J_invol ℓ s := by rw [admJ_eq_self, admJ_eq_self]
  J_ret ℓ s := by rw [admJ_eq_self]
  J_ext _ _ _ := by rw [admJ_eq_self]; rfl
  T_J ℓ m s := by rw [admJ_eq_self, admJ_eq_self]
  C := admC A
  C_idem ℓ s := by rw [admC_eq_self, admC_eq_self]
  C_ret ℓ s := by rw [admC_eq_self]
  T_C ℓ m s := by rw [admC_eq_self, admC_eq_self]

@[simp] theorem admFrame_W (ℓ : L) (s : Adm A ℓ) : (admFrame A).W ℓ s = admW A ℓ s := rfl

@[simp] theorem admFrame_J (ℓ : L) (s : Adm A ℓ) : (admFrame A).J ℓ s = s := admJ_eq_self A ℓ s

/-- **Admission inversion and self are the same admission**, stated in the admission frame:
the polar reversal of the admission level is the identity. -/
theorem admFrame_reversal_is_identity : (admFrame A).J = fun _ s => s := by
  funext ℓ s
  exact admJ_eq_self A ℓ s

/-- The admission frame carries no residual openness: its two orientations coincide. -/
theorem admFrame_not_separated (ℓ : L) : ¬ (admFrame A).Separated := by
  intro h
  exact h ℓ ⟨Eq, eq_equivalence⟩ rfl

/-! ## §4  Level two is rigid, and its naturality is translation -/

/-- **Level-two closure equality is literal equality of admissions.**  Two admissions with the same
return are the same admission. -/
theorem admFrame_ceq_iff_eq (ℓ : L) (s t : Adm A ℓ) :
    (closureDef (admFrame A) ℓ).r s t ↔ s = t :=
  ⟨fun h => admW_injective A ℓ h, fun h => by rw [h]⟩

/-- Closure equality of admissions is the admissible relational definition of the admission
level. -/
theorem admFrame_closureDef_closureForm : ClosureForm (admFrame A) (closureDef (admFrame A)) :=
  closureDef_closureForm (admFrame A)

/-- **Admissions are themselves admissible, and their admitted equality is forced.**  Any returning
grounded relational definition on the admissions is literal equality of admissions: there is one
admissible reading of admissions, and it is the one translation already supplies. -/
theorem admission_definition_forced (S : RelDef (Adm A)) (hret : Returns (admFrame A) S)
    (hgr : Grounded (admFrame A) S) (ℓ : L) (s t : Adm A ℓ) : (S ℓ).r s t ↔ s = t :=
  (unique_relational_definition (admFrame A) S hret hgr ℓ s t).trans (admFrame_ceq_iff_eq A ℓ s t)

/-- **The natural reading of admissions is translation.**  Naturality is not an extra assumption at
the admission level either: a returning grounded definition of admissions is preserved and
reflected by transport along translation. -/
theorem admission_naturality_is_translation (S : RelDef (Adm A)) (hret : Returns (admFrame A) S)
    (hgr : Grounded (admFrame A) S) : Natural (admFrame A) S :=
  naturality_is_forced (admFrame A) S hret hgr

/-- Every admission is admitted equal to its own inversion — and here, equal to it. -/
theorem admission_inversion_admitted_equal_self (S : RelDef (Adm A)) (hadm : Admits (admFrame A) S)
    (ℓ : L) (s : Adm A ℓ) : (S ℓ).r s ((admFrame A).J ℓ s) :=
  blind_to_reversal (admFrame A) S hadm ℓ s

/-- **Relative translation of admissions.**  An admission of one language has exactly one
relative-translation partner in any other language: its transport. -/
theorem admission_translation_existsUnique (ℓ m : L) (s : Adm A ℓ) :
    ∃! t : Adm A m, CrossRel (admFrame A) ℓ m s t := by
  refine ⟨admT A ℓ m s, no_language_is_isolated (admFrame A) ℓ m s, ?_⟩
  intro t ht
  have h : (admFrame A).W m t = (admFrame A).W m (admT A ℓ m s) := by
    rw [← ht]
    exact no_language_is_isolated (admFrame A) ℓ m s
  exact admW_injective A m h

/-- Transport of admissions is a bijection between the admissions of two languages: no language
holds admissions that another does not. -/
def admTranslationEquiv (ℓ m : L) : Adm A ℓ ≃ Adm A m := (admFrame A).transEquiv ℓ m

/-! ## §5  Stationarity: repeating the construction adds nothing -/

/-- **The admission level is stationary.**  Forming the admissions of the admissions changes
nothing further: at every level above the first, inversion is already the identity and the admitted
equality is already literal equality. -/
theorem admission_level_is_stationary (ℓ : L) (S : Adm (admFrame A) ℓ) :
    admJ (admFrame A) ℓ S = S ∧ admC (admFrame A) ℓ S = S ∧
      ∀ T : Adm (admFrame A) ℓ, (closureDef (admFrame (admFrame A)) ℓ).r S T ↔ S = T :=
  ⟨admJ_eq_self (admFrame A) ℓ S, admC_eq_self (admFrame A) ℓ S,
    fun T => admFrame_ceq_iff_eq (admFrame A) ℓ S T⟩

/-! ## §6  The bundle -/

/-- **Admissions are themselves admissible to their relative translation equality of admission
inversion and self.**

1. *Admissions are occurrences of a translational axiometry.*  `admFrame` is a `TransFrame`; its
   returns are the equivalence relations of relational identities, and return and presentation are
   mutually inverse (`admEquiv`), so the admission level is not extra data.
2. *Inversion and self.*  The inversion of an admission is that admission, literally; the
   curvature representative likewise; the two orientations of an identity relation are the same
   admission, so the admission frame is not separated.
3. *Their relative translation equality.*  Two admissions are closure equal exactly when they are
   equal, and every admission has exactly one relative-translation partner in every language.
4. *Naturality is translation.*  Any returning grounded reading of admissions is literal equality
   and is automatically preserved and reflected by translation.
5. *The remaining integration is already contained.*  Repeating the construction changes nothing. -/
theorem admissions_are_themselves_admissible (ℓ m : L) (s t : Adm A ℓ) :
    (admJ A ℓ s = s ∧ admC A ℓ s = s) ∧
    (∀ p q : Pole, ∀ r : IdRel B ℓ, admE A ℓ p r = admE A ℓ q r) ∧
    ¬ (admFrame A).Separated ∧
    ((closureDef (admFrame A) ℓ).r s t ↔ s = t) ∧
    (∀ S : RelDef (Adm A), Returns (admFrame A) S → Grounded (admFrame A) S →
      (∀ k (x y : Adm A k), (S k).r x y ↔ x = y) ∧ Natural (admFrame A) S ∧
        Admits (admFrame A) S) ∧
    (∃! t' : Adm A m, CrossRel (admFrame A) ℓ m s t') ∧
    (∀ S : Adm (admFrame A) ℓ, admJ (admFrame A) ℓ S = S) := by
  refine ⟨⟨admJ_eq_self A ℓ s, admC_eq_self A ℓ s⟩, fun p q r => admE_pole_irrelevant A ℓ p q r,
    admFrame_not_separated A ℓ, admFrame_ceq_iff_eq A ℓ s t, ?_,
    admission_translation_existsUnique A ℓ m s, fun S => admJ_eq_self (admFrame A) ℓ S⟩
  intro S hret hgr
  exact ⟨fun k x y => admission_definition_forced A S hret hgr k x y,
    naturality_is_forced (admFrame A) S hret hgr,
    admissibility_is_forced (admFrame A) S hret hgr⟩

/-! ## §7  A concrete instance: the admission level is not vacuous -/

section Concrete

variable (L₀ : Type u) (B₀ : Type v)

/-- On the standard model, the admissions of a language are exactly the equivalence relations on
the relational identities `B₀`, and each of them is its own inversion. -/
theorem standard_admissions (ℓ : L₀) :
    Nonempty (Adm (standardFrame L₀ B₀) ℓ ≃ IdRel (fun _ : L₀ => B₀) ℓ) ∧
      ∀ s : Adm (standardFrame L₀ B₀) ℓ, admJ (standardFrame L₀ B₀) ℓ s = s :=
  ⟨⟨admEquiv (standardFrame L₀ B₀) ℓ⟩, fun s => admJ_eq_self (standardFrame L₀ B₀) ℓ s⟩

/-- The standard frame is separated, yet its admission frame is not: the openness of the first
level is exactly what the admission level integrates away. -/
theorem standard_openness_integrated (ℓ : L₀) :
    (standardFrame L₀ B₀).Separated ∧ ¬ (admFrame (standardFrame L₀ B₀)).Separated :=
  ⟨standardFrame_separated L₀ B₀, admFrame_not_separated (standardFrame L₀ B₀) ℓ⟩

end Concrete

/-! ## §8  Axiom audit -/

end NRRF707

#print axioms NRRF707.adm_factors
#print axioms NRRF707.admEquiv
#print axioms NRRF707.admJ_eq_self
#print axioms NRRF707.admFrame
#print axioms NRRF707.admFrame_ceq_iff_eq
#print axioms NRRF707.admission_definition_forced
#print axioms NRRF707.admission_translation_existsUnique
#print axioms NRRF707.admission_level_is_stationary
#print axioms NRRF707.admissions_are_themselves_admissible
