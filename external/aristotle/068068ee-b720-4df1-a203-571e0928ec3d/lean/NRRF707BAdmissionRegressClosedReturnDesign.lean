import Mathlib
import NRRF707AdmissionsAreThemselvesAdmissible

/-!
# NRRF707B — Closing the admission regress: an admission is an equivalence relation on returns

This module states and proves, in the barest possible setting — a single **return map**
`r : A → B` from occurrences to returned relational identities — the terminal layer of the
translational axiometry:

> occurrence → hair/path → returned identity → Closure → admission → stationarity.

An **admission** on occurrences is an equality of occurrences that cannot separate occurrences
with the same return (`Adm r`; this is exactly `NRRF707.AdmitsAt` read for the return map
`A.W ℓ` of a translational frame — see `adm_eq_frame_adm`).

## What is proved

* **§1 An admission is its own return.**  `adm_factors`: `R x y ↔ R̂ (r x) (r y)` for the induced
  relation `R̂ = admRet R` on returned identities; `admRet_unique`: `R̂` is the *only* equivalence
  relation on `B` through which `R` factors.  `pull` is the converse operation, and
  `pull_admRet`, `admRet_pull`, `admEquivSetoid` : `Adm(A) ≃ Equiv(B)` — the two operations are
  mutually inverse, so an admission contains no occurrence-level information beyond the return
  relation it admits.
* **§2 Admission is only as rich as return.**  `same_return_admitted`: `r x = r y` implies no
  admission distinguishes `x` from `y`; `exists_adm_separating` is the converse, so
  `adm_indistinguishable_iff_same_return`.  `Refines`, `admOfRefines`, `admOfRefines_injective`
  and `adm_strictly_richer`: enriching the return strictly enlarges the supply of admissions, and
  that — not a later meta-admission — is where the remaining architectural choice sits.
* **§3 Stationarity.**  `admRet_bijective`, `adm_closureEq_iff_eq` (`R =_C S ↔ R = S`),
  `admPullMap_eq_self` (`J_Adm R = R`, `C_Adm R = R` for *every* return-preserving re-reading of
  occurrences), and `admission_level_stationary`: at the admission level the return constrains
  nothing, `Adm (admRet) ≃ Setoid (Adm r)` — the regress terminates.
* **§4 Naturality is translation.**  `admTransport_existsUnique` and `admTranslationEquiv`:
  a translation of languages induces exactly one translated admission, so admission naturality is
  not a further axiom.
* **§5 Return design.**  A finite-word instance (ball ⊏ class hair ⊏ ordered hair) and the
  product instance behind the Slearn / ASI / Black-Mirror readings: a return that records only a
  final component admits no distinction of provenance, an enriched return does.
* **§6** The bundle `nrrf707_closes_the_admission_regress`.

Nothing physical, educational or ethical is asserted: `A`, `B` are arbitrary types, `r` an
arbitrary map, and the named instances are finite integer words and product types.
-/

namespace NRRF707B

open Function

universe u v w

/-! ## §1  Admissions, their return, and the equivalence `Adm(A) ≃ Equiv(B)` -/

variable {A : Type u} {B : Type v}

/-- **An admission** for the return map `r : A → B`: an equality of occurrences that cannot
separate occurrences with the same return. -/
def Adm (r : A → B) : Type u := {R : Setoid A // ∀ x y : A, r x = r y → R.r x y}

/-- Two admissions that hold of the same pairs are equal. -/
theorem adm_ext {r : A → B} {R S : Adm r} (h : ∀ x y, R.1.r x y ↔ S.1.r x y) : R = S :=
  Subtype.ext (Setoid.ext h)

/-- An admission in the present sense is literally an admission in the sense of NRRF707, for the
return map of a translational frame. -/
theorem adm_eq_frame_adm {L : Type u} {Bf : L → Type v} {Y : L → Type u}
    (F : NRRF627.TransFrame L Bf Y) (ℓ : L) : NRRF707.Adm F ℓ = Adm (F.W ℓ) := rfl

/-- The return map of a translational frame is surjective: every relational identity is returned
by one of its presentations. -/
theorem frame_return_surjective {L : Type u} {Bf : L → Type v} {Y : L → Type u}
    (F : NRRF627.TransFrame L Bf Y) (ℓ : L) : Surjective (F.W ℓ) :=
  fun b => ⟨F.E ℓ NRRF627.Pole.zero b, F.recov ℓ NRRF627.Pole.zero b⟩

variable {r : A → B}

/-- **The return of an admission**: the relation it induces between returned identities. -/
def admRet (hr : Surjective r) (R : Adm r) : Setoid B where
  r b b' := ∃ x y : A, r x = b ∧ r y = b' ∧ R.1.r x y
  iseqv :=
    { refl := fun b => by
        obtain ⟨x, hx⟩ := hr b
        exact ⟨x, x, hx, hx, R.1.iseqv.refl x⟩
      symm := fun ⟨x, y, hx, hy, h⟩ => ⟨y, x, hy, hx, R.1.iseqv.symm h⟩
      trans := fun ⟨x, y, hx, hy, h⟩ ⟨u, v, hu, hv, h'⟩ =>
        ⟨x, v, hx, hv, R.1.iseqv.trans h (R.1.iseqv.trans (R.2 y u (by rw [hy, hu])) h')⟩ }

/-- **An admission is its own return**: `R(x,y) ↔ R̂(r x, r y)`.  Every admission factors through
the return map. -/
theorem adm_factors (hr : Surjective r) (R : Adm r) (x y : A) :
    R.1.r x y ↔ (admRet hr R).r (r x) (r y) := by
  constructor
  · intro h; exact ⟨x, y, rfl, rfl, h⟩
  · rintro ⟨u, v, hu, hv, h⟩
    exact R.1.iseqv.trans (R.2 x u hu.symm) (R.1.iseqv.trans h (R.2 v y hv))

/-- **Pullback along the return**: every equivalence relation on returned identities is an
admission of occurrences. -/
def pull (r : A → B) (E : Setoid B) : Adm r :=
  ⟨⟨fun x y => E.r (r x) (r y),
      ⟨fun _ => E.iseqv.refl _, fun h => E.iseqv.symm h, fun h h' => E.iseqv.trans h h'⟩⟩,
    fun x y h => by
      show E.r (r x) (r y)
      rw [h]⟩

@[simp] theorem pull_apply (E : Setoid B) (x y : A) : (pull r E).1.r x y ↔ E.r (r x) (r y) :=
  Iff.rfl

/-- The induced relation on returns is the **unique** equivalence relation through which an
admission factors. -/
theorem admRet_unique (hr : Surjective r) (R : Adm r) (E : Setoid B)
    (hE : ∀ x y : A, R.1.r x y ↔ E.r (r x) (r y)) : E = admRet hr R := by
  refine Setoid.ext fun b b' => ?_
  obtain ⟨x, rfl⟩ := hr b
  obtain ⟨y, rfl⟩ := hr b'
  rw [← hE, adm_factors hr R]

/-- Returning a pulled-back relation recovers it. -/
theorem admRet_pull (hr : Surjective r) (E : Setoid B) : admRet hr (pull r E) = E :=
  (admRet_unique hr (pull r E) E fun _ _ => Iff.rfl).symm

/-- An admission is the pullback of its own return. -/
theorem pull_admRet (hr : Surjective r) (R : Adm r) : pull r (admRet hr R) = R :=
  adm_ext fun x y => (adm_factors hr R x y).symm

/-- **`return : Adm(A) ≃ Equiv(B) : pull`.**  Admissions of occurrences are exactly the
equivalence relations of returned identities; the admission layer is not extra data. -/
def admEquivSetoid (hr : Surjective r) : Adm r ≃ Setoid B where
  toFun := admRet hr
  invFun := pull r
  left_inv := pull_admRet hr
  right_inv := admRet_pull hr

theorem admRet_injective (hr : Surjective r) : Injective (admRet hr) :=
  (admEquivSetoid hr).injective

theorem admRet_bijective (hr : Surjective r) : Bijective (admRet hr) :=
  (admEquivSetoid hr).bijective

/-! ## §2  Admission is only as rich as return -/

/-- **The critical design consequence.**  If two occurrences have the same return then no
admission whatsoever can distinguish them. -/
theorem same_return_admitted {x y : A} (h : r x = r y) (R : Adm r) : R.1.r x y := R.2 x y h

/-- The finest admission: the kernel of the return map. -/
def kerAdm (r : A → B) : Adm r := pull r ⟨Eq, eq_equivalence⟩

@[simp] theorem kerAdm_apply (x y : A) : (kerAdm r).1.r x y ↔ r x = r y := Iff.rfl

/-- Conversely, occurrences with different returns *are* separated by some admission. -/
theorem exists_adm_separating {x y : A} (h : r x ≠ r y) : ∃ R : Adm r, ¬ R.1.r x y :=
  ⟨kerAdm r, h⟩

/-- **Admissible indistinguishability is exactly equality of returns.** -/
theorem adm_indistinguishable_iff_same_return (x y : A) :
    (∀ R : Adm r, R.1.r x y) ↔ r x = r y :=
  ⟨fun h => h (kerAdm r), fun h R => same_return_admitted h R⟩

section Refinement

variable {A₀ : Type u} {B₁ : Type v} {B₂ : Type w}

/-- `r'` **refines** `r`: the finer return keeps every distinction the coarser one keeps. -/
def Refines (r' : A₀ → B₁) (r : A₀ → B₂) : Prop := ∀ x y : A₀, r' x = r' y → r x = r y

theorem refines_refl (r : A₀ → B₁) : Refines r r := fun _ _ h => h

/-- A return of the form `x ↦ (r x, extra x)` refines `r`: enrichment never loses a
distinction. -/
theorem refines_enrich (r : A₀ → B₂) {C : Type w} (extra : A₀ → C) :
    Refines (fun x => (r x, extra x)) r := fun _ _ h => congrArg Prod.fst h

/-- **Every admission of a coarser return is an admission of a finer one.**  Enriching the return
can only enlarge the supply of admissions. -/
def admOfRefines {r' : A₀ → B₁} {r : A₀ → B₂} (h : Refines r' r) (R : Adm r) : Adm r' :=
  ⟨R.1, fun x y hxy => R.2 x y (h x y hxy)⟩

theorem admOfRefines_injective {r' : A₀ → B₁} {r : A₀ → B₂} (h : Refines r' r) :
    Injective (admOfRefines h) := by
  intro R S hRS
  have h1 : (admOfRefines h R).val = (admOfRefines h S).val := congrArg Subtype.val hRS
  exact Subtype.ext h1

/-- **The enrichment is strict exactly where the finer return separates more.**  If `r'` refines
`r` and separates a pair that `r` identifies, then some admission for `r'` is not the image of any
admission for `r`: the finer return admits genuinely more distinctions. -/
theorem adm_strictly_richer {r' : A₀ → B₁} {r : A₀ → B₂} (h : Refines r' r) {x y : A₀}
    (hsame : r x = r y) (hdiff : r' x ≠ r' y) :
    ∃ R' : Adm r', ∀ R : Adm r, admOfRefines h R ≠ R' := by
  refine ⟨kerAdm r', ?_⟩
  intro R hR
  apply hdiff
  have h1 : R.1.r x y := R.2 x y hsame
  have h2 : (kerAdm r').1.r x y := by rw [← hR]; exact h1
  exact h2

end Refinement

theorem refines_trans {A₀ : Type u} {B₁ : Type v} {B₂ : Type w} {B₃ : Type w}
    {r'' : A₀ → B₁} {r' : A₀ → B₂} {r : A₀ → B₃}
    (h₁ : Refines r'' r') (h₂ : Refines r' r) : Refines r'' r :=
  fun x y h => h₂ x y (h₁ x y h)

/-! ## §3  Stationarity: the admission level closes the regress -/

/-- **`R =_C S ↔ R = S`.**  Two admissions with the same return are the same admission: at the
admission level, Closure equality is literal equality. -/
theorem adm_closureEq_iff_eq (hr : Surjective r) (R S : Adm r) :
    admRet hr R = admRet hr S ↔ R = S :=
  ⟨fun h => admRet_injective hr h, fun h => by rw [h]⟩

/-- **`J_Adm(R) = R` and `C_Adm(R) = R`, in one statement.**  An admission is blind to *any*
re-reading of occurrences that preserves the return — a polar reversal, a curvature
representative, a change of based path. -/
theorem adm_pullback_eq_self (hr : Surjective r) (f : A → A) (hf : ∀ x, r (f x) = r x)
    (R : Adm r) (x y : A) : R.1.r (f x) (f y) ↔ R.1.r x y := by
  rw [adm_factors hr R (f x) (f y), adm_factors hr R x y, hf, hf]

/-- The pullback of an admission along a return-preserving re-reading, as an admission. -/
def admPullMap (f : A → A) (hf : ∀ x, r (f x) = r x) (R : Adm r) : Adm r :=
  ⟨⟨fun x y => R.1.r (f x) (f y),
      ⟨fun _ => R.1.iseqv.refl _, fun h => R.1.iseqv.symm h, fun h h' => R.1.iseqv.trans h h'⟩⟩,
    fun x y h => R.2 _ _ (by rw [hf, hf, h])⟩

/-- `J_Adm(R) = R`: the inversion of an admission *is* that admission, literally. -/
theorem admPullMap_eq_self (hr : Surjective r) (f : A → A) (hf : ∀ x, r (f x) = r x) (R : Adm r) :
    admPullMap f hf R = R :=
  adm_ext fun x y => adm_pullback_eq_self hr f hf R x y

/-- **Over a bijective return the admission construction is the identity operation**: every
equivalence relation of occurrences is already an admission, because the return separates
everything. -/
def admOfBijective (hb : Bijective r) : Adm r ≃ Setoid A where
  toFun R := R.1
  invFun S := ⟨S, fun x y h => by
    obtain rfl := hb.1 h
    exact S.iseqv.refl _⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **At the admission level the return imposes no constraint.**  Since the admission-level return
map `admRet` is bijective, *every* equivalence relation on admissions is already an admission for
it: there is nothing left for a meta-admission to decide.  This is the precise sense in which
`Adm(Adm(A)) ≃ Adm(A)`: from the admission level upwards the construction is the identity
operation `X ↦ Setoid X`. -/
def admLevelEquiv (hr : Surjective r) : Adm (admRet hr) ≃ Setoid (Adm r) :=
  admOfBijective (admRet_bijective hr)

/-- **The admission construction is stationary.**  Its return map is a bijection, Closure equality
of admissions is equality, the admission level's own admissions are unconstrained, and iterating
once more changes nothing again. -/
theorem admission_level_stationary (hr : Surjective r) :
    Bijective (admRet hr) ∧
    (∀ R S : Adm r, admRet hr R = admRet hr S ↔ R = S) ∧
    Nonempty (Adm (admRet hr) ≃ Setoid (Adm r)) ∧
    Bijective (admRet (r := admRet hr) (admRet_bijective hr).2) :=
  ⟨admRet_bijective hr, adm_closureEq_iff_eq hr, ⟨admLevelEquiv hr⟩,
    admRet_bijective (admRet_bijective hr).2⟩

/-! ## §4  Admission naturality is translation -/

section Translation

variable {A' : Type u} {B' : Type v} {r : A → B} {r' : A' → B'} (T : A ≃ A') (t : B ≃ B')

/-- Transport of an admission along a translation of languages. -/
def admTransport (hcomp : ∀ x : A, r' (T x) = t (r x)) (R : Adm r) : Adm r' :=
  ⟨⟨fun x' y' => R.1.r (T.symm x') (T.symm y'),
      ⟨fun _ => R.1.iseqv.refl _, fun h => R.1.iseqv.symm h, fun h h' => R.1.iseqv.trans h h'⟩⟩,
    fun x' y' h => R.2 _ _ (t.injective (by
      rw [← hcomp, ← hcomp, T.apply_symm_apply, T.apply_symm_apply, h]))⟩

@[simp] theorem admTransport_apply (hcomp : ∀ x : A, r' (T x) = t (r x)) (R : Adm r) (x y : A) :
    (admTransport T t hcomp R).1.r (T x) (T y) ↔ R.1.r x y := by
  show R.1.r (T.symm (T x)) (T.symm (T y)) ↔ _
  rw [T.symm_apply_apply, T.symm_apply_apply]

/-- **`R'(Tx, Ty) ↔ R(x,y)` has exactly one solution.**  An admission has exactly one translated
partner, induced by translating the returned identities; no second rule chooses it. -/
theorem admTransport_existsUnique (hcomp : ∀ x : A, r' (T x) = t (r x)) (R : Adm r) :
    ∃! R' : Adm r', ∀ x y : A, R'.1.r (T x) (T y) ↔ R.1.r x y := by
  refine ⟨admTransport T t hcomp R, admTransport_apply T t hcomp R, ?_⟩
  intro S hS
  refine adm_ext fun x' y' => ?_
  have h := hS (T.symm x') (T.symm y')
  rw [T.apply_symm_apply, T.apply_symm_apply] at h
  exact h

/-- The compatibility law read backwards along the translation. -/
theorem admTransport_symm_comp (hcomp : ∀ x : A, r' (T x) = t (r x)) (x' : A') :
    r (T.symm x') = t.symm (r' x') := by
  have h := hcomp (T.symm x')
  rw [T.apply_symm_apply] at h
  rw [h, t.symm_apply_apply]

/-- **`Adm(A) ≃ Adm(A')`.**  Translation of admissions is a bijection; "admission naturality" and
"translation of admissions" are the same operation. -/
def admTranslationEquiv (hcomp : ∀ x : A, r' (T x) = t (r x)) : Adm r ≃ Adm r' where
  toFun := admTransport T t hcomp
  invFun := admTransport T.symm t.symm (admTransport_symm_comp T t hcomp)
  left_inv R := adm_ext fun x y => by
    show R.1.r (T.symm (T.symm.symm x)) (T.symm (T.symm.symm y)) ↔ R.1.r x y
    simp only [Equiv.symm_symm, Equiv.symm_apply_apply]
  right_inv R := adm_ext fun x y => by
    show R.1.r (T.symm.symm (T.symm x)) (T.symm.symm (T.symm y)) ↔ R.1.r x y
    simp only [Equiv.symm_symm, Equiv.apply_symm_apply]

end Translation

/-! ## §5  Return design: what survives into admission -/

section ReturnDesign

/-- The **ball** of a finite mirror word `γ = (g₀, …, g_{n-1})`: its total return. -/
def ball (g : List ℤ) : ℤ := g.sum

/-- The **class hair**: the steps of the word, order forgotten. -/
def classHair (g : List ℤ) : Multiset ℤ := (g : Multiset ℤ)

/-- The **ordered hair**: the based word itself. -/
def orderedHair (g : List ℤ) : List ℤ := g

theorem classHair_refines_ball : Refines classHair ball := by
  intro x y h
  have h' : ((x : Multiset ℤ)).sum = ((y : Multiset ℤ)).sum := congrArg Multiset.sum h
  simpa [ball, Multiset.sum_coe] using h'

theorem orderedHair_refines_classHair : Refines orderedHair classHair :=
  fun _ _ h => congrArg (fun l : List ℤ => (l : Multiset ℤ)) h

theorem orderedHair_refines_ball : Refines orderedHair ball :=
  refines_trans orderedHair_refines_classHair classHair_refines_ball

/-- The class hair strictly refines the ball: `[2]` and `[1,1]` have the same ball. -/
theorem classHair_strictly_refines_ball :
    ball [(2 : ℤ)] = ball [(1 : ℤ), 1] ∧ classHair [(2 : ℤ)] ≠ classHair [(1 : ℤ), 1] := by
  refine ⟨by decide, by decide⟩

/-- The ordered hair strictly refines the class hair: `[1,0]` and `[0,1]` have the same class
hair. -/
theorem orderedHair_strictly_refines_classHair :
    classHair [(1 : ℤ), 0] = classHair [(0 : ℤ), 1] ∧
      orderedHair [(1 : ℤ), 0] ≠ orderedHair [(0 : ℤ), 1] := by
  refine ⟨by decide, by decide⟩

/-- **The formalism does not erase the hair; the return signature does.**  An admission at ball
resolution cannot distinguish two words with the same ball, while at ordered-hair resolution some
admission does. -/
theorem admission_resolution_ball_vs_hair :
    (∀ R : Adm ball, R.1.r [(1 : ℤ), 0] [(0 : ℤ), 1]) ∧
      ∃ R : Adm orderedHair, ¬ R.1.r [(1 : ℤ), 0] [(0 : ℤ), 1] :=
  ⟨fun R => same_return_admitted (by decide) R, exists_adm_separating (by decide)⟩

/-- The class-hair resolution sees the multiset of steps but not their order; enriching to the
ordered hair makes that distinction admissible. -/
theorem admission_resolution_classHair_vs_hair :
    (∀ R : Adm classHair, R.1.r [(1 : ℤ), 0] [(0 : ℤ), 1]) ∧
      ∃ R : Adm orderedHair, ¬ R.1.r [(1 : ℤ), 0] [(0 : ℤ), 1] :=
  ⟨fun R => same_return_admitted (by decide) R, exists_adm_separating (by decide)⟩

/-- The general shape behind the Slearn, mathematical-ASI and Black-Mirror readings: a return that
records only a final component (a credential, a proposition, a final intensity) cannot support any
admission that distinguishes two occurrences agreeing in that component. -/
theorem final_component_return_forgets {F P : Type u} (v : F) (p q : P)
    (R : Adm (Prod.fst : F × P → F)) : R.1.r (v, p) (v, q) :=
  same_return_admitted (x := (v, p)) (y := (v, q)) rfl R

/-- Enriching the same return with the second component (the WHY-path, the proof object, the
phase-resolved partial returns) makes exactly those distinctions admissible again. -/
theorem enriched_return_distinguishes {F P : Type u} (v : F) {p q : P} (h : p ≠ q) :
    ∃ R : Adm (id : F × P → F × P), ¬ R.1.r (v, p) (v, q) := by
  refine exists_adm_separating (r := (id : F × P → F × P)) ?_
  intro hc
  exact h (congrArg Prod.snd hc)

/-- The enriched return refines the credential-style return, so it keeps every admission the weak
return had and adds more. -/
theorem enriched_return_refines {F P : Type u} :
    Refines (id : F × P → F × P) (Prod.fst : F × P → F) := fun _ _ h => congrArg Prod.fst h

end ReturnDesign

/-! ## §6  The bundle -/

/-- **NRRF707 closes the admission regress.**

1. *An admission is exactly an equivalence relation on returned identities.*  Every admission
   factors through the return, through a unique equivalence relation on returns, and return and
   pullback are mutually inverse: `Adm(A) ≃ Equiv(B)`.
2. *Admission is only as rich as return.*  Occurrences with the same return are indistinguishable
   to every admission, and only those.
3. *The admission level is stationary.*  Closure equality of admissions is literal equality; an
   admission is blind to every return-preserving re-reading (inversion, curvature, change of based
   path); and at the admission level the return constrains nothing further, so no meta-admission
   layer arises.
4. *Naturality is translation.*  Along a translation of languages each admission has exactly one
   translated partner. -/
theorem nrrf707_closes_the_admission_regress (hr : Surjective r) :
    (∀ (R : Adm r) (x y : A), R.1.r x y ↔ (admRet hr R).r (r x) (r y)) ∧
    (∀ (R : Adm r) (E : Setoid B), (∀ x y : A, R.1.r x y ↔ E.r (r x) (r y)) → E = admRet hr R) ∧
    Nonempty (Adm r ≃ Setoid B) ∧
    (∀ x y : A, (∀ R : Adm r, R.1.r x y) ↔ r x = r y) ∧
    (∀ f : A → A, (∀ x, r (f x) = r x) → ∀ R : Adm r, ∀ x y, R.1.r (f x) (f y) ↔ R.1.r x y) ∧
    (∀ R S : Adm r, admRet hr R = admRet hr S ↔ R = S) ∧
    Nonempty (Adm (admRet hr) ≃ Setoid (Adm r)) ∧
    (∀ (A₂ : Type u) (B₂ : Type v) (r₂ : A₂ → B₂) (T : A ≃ A₂) (t : B ≃ B₂),
      (∀ x : A, r₂ (T x) = t (r x)) →
        ∀ R : Adm r, ∃! R' : Adm r₂, ∀ x y : A, R'.1.r (T x) (T y) ↔ R.1.r x y) :=
  ⟨adm_factors hr, admRet_unique hr, ⟨admEquivSetoid hr⟩,
    adm_indistinguishable_iff_same_return,
    fun f hf R => adm_pullback_eq_self hr f hf R,
    adm_closureEq_iff_eq hr, ⟨admLevelEquiv hr⟩,
    fun _ _ _ T t hcomp R => admTransport_existsUnique T t hcomp R⟩

end NRRF707B

#print axioms NRRF707B.adm_factors
#print axioms NRRF707B.admEquivSetoid
#print axioms NRRF707B.adm_indistinguishable_iff_same_return
#print axioms NRRF707B.adm_strictly_richer
#print axioms NRRF707B.admission_level_stationary
#print axioms NRRF707B.admTransport_existsUnique
#print axioms NRRF707B.admission_resolution_ball_vs_hair
#print axioms NRRF707B.nrrf707_closes_the_admission_regress
