import Mathlib
import NRRF709TranslationalClosureHarnessBallHairUnistochasticStrictness
import NRRF710NaturalTranslationalEqualityPriorZeroInfinityClosure

/-!
# NRRF711 — Only translational proof can naturally universally close

The request for this module is the uniqueness statement that the previous rounds left implicit:

> **only translational proof can naturally universally close.**

NRRF709 proved that *if* two readings induce the same partition of occurrences then there is
exactly one invertible dictionary between their return languages; NRRF710 proved that natural
translational equality is prior to `0 ↔ ∞`, universality, probability and brightness.  Neither
proves that translational closure is the *only* way to close.  That is what is proved here.

## The formal shape of the claim

A candidate notion of closure is not a single relation: it must apply to *every* presentation, since
a criterion that only works on one chosen apparatus is not a criterion at all.  So a candidate is a
**uniform family**

`C : ∀ (A R : Type), (A → R) → A → A → Prop`,

assigning to every occurrence space `A` with return `r : A → R` a relation "`x` and `y` close".

Four conditions say that such a family *naturally universally closes*
(`NaturalUniversal`):

* `crefl`    — every occurrence closes with itself (it closes at all);
* `reparam`  — **naturality in the occurrences**: reparametrizing the occurrence space along
  `f : A' → A` and reading through `r ∘ f` gives the same verdict as reading `f x, f y` through `r`.
  The criterion may not consult the parametrization of the occurrences, only the reading;
* `relabel`  — **naturality in the return language**: relabelling the return along an *injective*
  `i : R → S` (a translation of the return language that loses nothing) does not change the verdict.
  The criterion may not consult the names of the returned values;
* `discerning` — the criterion is not vacuous: on the two-point presentation read by the identity,
  the two distinct occurrences do **not** close.

## The theorem

`kernel_of_naturalUniversal` : for every natural universal `C`, every presentation and all
occurrences,

`C A R r x y ↔ r x = r y`.

So a criterion satisfying the four conditions *is* the kernel of the return — the relation
"`x` and `y` are translationally equal at the resolution of `r`" — and nothing else.  Immediate
consequences:

* `naturalUniversal_unique` — any two natural universal criteria are equal;
* `kernelClosure_naturalUniversal` — the translational criterion does satisfy all four, so the
  notion is not empty: translational closure exists and is unique;
* `closure_is_equivalence` — a natural universal criterion is automatically an equivalence relation
  (closure is not assumed, it is forced);
* `closure_agree_iff_harness` and `unique_dictionary_of_closure_agree` — two readings receive the
  same closure verdicts exactly when they form an NRRF709 harness, in which case (for a surjective
  return) there is exactly one invertible translation `t` with `t ∘ r = e`, i.e. exactly one
  NRRF710 natural translational equality between the two return languages.  **Every proof of
  closure is a translation, and it is the only one.**

## Independence: each hypothesis is doing work

The four conditions are not padding — dropping any one admits a non-translational criterion
(`independence_of_the_four_conditions`):

* `botClosure` (nothing closes) satisfies `reparam`, `relabel`, `discerning`, not `crefl`;
* `topClosure` (everything closes) satisfies `crefl`, `reparam`, `relabel`, not `discerning`
  — this is absolute collapse, closure without distinction;
* `identityClosure` (only literally identical occurrences close) satisfies `crefl`, `relabel`,
  `discerning`, not `reparam` — it reduces closure to identity of representation;
* `labelSizeClosure` (close whenever the returns agree *or* the label type is infinite) satisfies
  `crefl`, `reparam`, `discerning`, not `relabel` — it reads the names in the return language
  rather than the relation the return makes.

Read backwards: reflexivity, invariance under reparametrization, invariance under relabelling and
non-vacuity are jointly exactly the content of "naturally universally closes", and the only
criterion meeting them is translational equality of returns.

## It cannot be correspondence

`Corresponds` is the informal comparison "the physical output matches the digital number", i.e.
numerical agreement after both readings are pushed into one scale.  It is *neither* sufficient
(`correspondence_not_sufficient`: the numbers agree at every occurrence while the partitions
differ) *nor* necessary (`correspondence_not_necessary`: the partitions agree — one forced
invertible dictionary — while the numbers differ at every occurrence), and unlike closure it is
destroyed by a lossless relabelling of a return language
(`correspondence_breaks_under_relabelling`).  So the physical and the digital reading cannot be
required to correspond; they have to be translationally equal.

## The empirical question: ellipse light in a dark silicon weave

`§7` answers it in the formal model.  With the frozen transducer `siliconEncode` writing each
traversal sense of the optical ellipse weave into a pair of dark-silicon gate states:

* `ellipse_dark_silicon_harness` — the optical ordered return and the silicon ordered return induce
  the same partition, in two languages with no shared coordinates;
* `ellipse_dark_silicon_unique_dictionary` — the dictionary between the two return languages is then
  forced, not chosen;
* `bright_corresponds` and `bright_not_harness` — the bright-port count and the gate count *do*
  correspond numerically, and that correspondence is worthless: brightness is not a harness for the
  ordered return.

So a dark silicon weave can carry the ellipse-light closure exactly when its return retains the
ordered hair, and the evidence for it can never be numerical agreement.

## Only translation admits existence

`closed_occurrences_are_admitted_alike` and `admission_separates_iff_not_closed`: at a given return
resolution, two occurrences are closed iff no admission whatsoever separates them.  Translational
equality is therefore precisely what naturally universally admits existence at that resolution.
-/

namespace NRRF711

open Function

/-! ## §1  Candidate closure criteria -/

/-- A **closure criterion**: a uniform family assigning, to each occurrence space `A` with a return
`r : A → R`, a relation on occurrences.  Universality is built into the quantifier: the criterion
must have a verdict for *every* presentation, not just a chosen one. -/
def ClosureCriterion : Type 1 := ∀ (A R : Type), (A → R) → A → A → Prop

/-- **Translational closure**: `x` and `y` close when the return does not distinguish them.  By
NRRF709 this is exactly the statement that the two occurrences are carried onto one another by the
unique translation of the returned language. -/
def kernelClosure : ClosureCriterion := fun _ _ r x y => r x = r y

/-- The four conditions defining "naturally universally closes". -/
structure NaturalUniversal (C : ClosureCriterion) : Prop where
  /-- It closes: every occurrence closes with itself. -/
  crefl : ∀ (A R : Type) (r : A → R) (x : A), C A R r x x
  /-- Natural in the occurrences: the criterion does not consult the parametrization. -/
  reparam : ∀ (A A' R : Type) (r : A → R) (f : A' → A) (x y : A'),
    C A' R (r ∘ f) x y ↔ C A R r (f x) (f y)
  /-- Natural in the return language: relabelling the return by a lossless (injective)
  translation does not change the verdict. -/
  relabel : ∀ (A R S : Type) (r : A → R) (i : R → S), Injective i → ∀ (x y : A),
    C A S (i ∘ r) x y ↔ C A R r x y
  /-- Not vacuous: on the two-point presentation read by the identity, the two distinct
  occurrences do not close. -/
  discerning : ¬ C Bool Bool id false true

/-! ## §2  The two-point probe -/

/-- The two-point probe `Bool → A` selecting the pair `(x, y)`. -/
private def probe {A : Type} (x y : A) : Bool → A := fun b => cond b y x

private theorem probe_false {A : Type} (x y : A) : probe x y false = x := rfl

private theorem probe_true {A : Type} (x y : A) : probe x y true = y := rfl

private theorem probe_read_injective {A R : Type} (r : A → R) {x y : A} (h : r x ≠ r y) :
    Injective (r ∘ probe x y) := by
  intro a b hab
  cases a <;> cases b <;> simp_all [probe]

/-! ## §3  The uniqueness theorem -/

/-- **Only translational proof can naturally universally close.**  Any criterion that closes, is
natural in the occurrences and in the return language, and is not vacuous, is *exactly* equality of
returns: closure is translational equality at the resolution of the return, and there is no other
possibility. -/
theorem kernel_of_naturalUniversal {C : ClosureCriterion} (hC : NaturalUniversal C)
    (A R : Type) (r : A → R) (x y : A) : C A R r x y ↔ r x = r y := by
  constructor
  · intro hxy
    by_contra hne
    have h1 : C Bool R (r ∘ probe x y) false true :=
      (hC.reparam A Bool R r (probe x y) false true).2 hxy
    have hinj : Injective (r ∘ probe x y) := probe_read_injective r hne
    have h2 := (hC.relabel Bool Bool R id (r ∘ probe x y) hinj false true).1
      (by simpa [Function.comp_def] using h1)
    exact hC.discerning h2
  · intro hxy
    have hconst : (r ∘ probe x y) ∘ (fun _ : Bool => false) = r ∘ probe x y := by
      funext b
      cases b <;> simp [Function.comp_def, probe, hxy]
    have h0 : C Bool R ((r ∘ probe x y) ∘ (fun _ : Bool => false)) false true :=
      (hC.reparam Bool Bool R (r ∘ probe x y) (fun _ => false) false true).2
        (hC.crefl Bool R (r ∘ probe x y) false)
    rw [hconst] at h0
    exact (hC.reparam A Bool R r (probe x y) false true).1 h0

/-- The translational criterion really does naturally universally close: the notion is inhabited. -/
theorem kernelClosure_naturalUniversal : NaturalUniversal kernelClosure where
  crefl := fun _ _ _ _ => rfl
  reparam := fun _ _ _ _ _ _ _ => Iff.rfl
  relabel := fun _ _ _ _ i hi _ _ => ⟨fun h => hi h, fun h => congrArg i h⟩
  discerning := by simp [kernelClosure]

/-- **Existence and uniqueness of the closing criterion.**  A criterion naturally universally
closes iff it is translational closure. -/
theorem naturalUniversal_iff_kernelClosure (C : ClosureCriterion) :
    NaturalUniversal C ↔ ∀ (A R : Type) (r : A → R) (x y : A), C A R r x y ↔ kernelClosure A R r x y := by
  constructor
  · intro hC A R r x y
    exact kernel_of_naturalUniversal hC A R r x y
  · intro h
    refine ⟨fun A R r x => (h A R r x x).2 rfl, ?_, ?_, ?_⟩
    · intro A A' R r f x y
      rw [h A' R (r ∘ f) x y, h A R r (f x) (f y)]
      exact Iff.rfl
    · intro A R S r i hi x y
      rw [h A S (i ∘ r) x y, h A R r x y]
      exact ⟨fun hxy => hi hxy, fun hxy => congrArg i hxy⟩
    · intro hbad
      exact kernelClosure_naturalUniversal.discerning ((h Bool Bool id false true).1 hbad)

/-- Any two criteria that naturally universally close coincide on every presentation: there is
**one** closing relation, not a choice of them. -/
theorem naturalUniversal_unique {C D : ClosureCriterion} (hC : NaturalUniversal C)
    (hD : NaturalUniversal D) (A R : Type) (r : A → R) (x y : A) :
    C A R r x y ↔ D A R r x y := by
  rw [kernel_of_naturalUniversal hC, kernel_of_naturalUniversal hD]

/-- Closure is not assumed of the criterion — being an equivalence relation is *forced* by
naturality, universality and non-vacuity. -/
theorem closure_is_equivalence {C : ClosureCriterion} (hC : NaturalUniversal C)
    (A R : Type) (r : A → R) : Equivalence (C A R r) where
  refl x := (kernel_of_naturalUniversal hC A R r x x).2 rfl
  symm {x y} h := (kernel_of_naturalUniversal hC A R r y x).2
    ((kernel_of_naturalUniversal hC A R r x y).1 h).symm
  trans {x y z} h₁ h₂ := (kernel_of_naturalUniversal hC A R r x z).2
    (((kernel_of_naturalUniversal hC A R r x y).1 h₁).trans
      ((kernel_of_naturalUniversal hC A R r y z).1 h₂))

/-! ## §4  Every proof of closure is a translation (bridge to NRRF709 / NRRF710) -/

/-- Two readings of the same occurrences receive the same closure verdicts exactly when they form
an NRRF709 **harness**: same induced partition of occurrences. -/
theorem closure_agree_iff_harness {C : ClosureCriterion} (hC : NaturalUniversal C)
    {A R S : Type} (r : A → R) (e : A → S) :
    (∀ x y, C A R r x y ↔ C A S e x y) ↔ NRRF709.Harness r e := by
  constructor
  · intro h x y
    rw [← kernel_of_naturalUniversal hC A R r x y, ← kernel_of_naturalUniversal hC A S e x y]
    exact h x y
  · intro h x y
    rw [kernel_of_naturalUniversal hC A R r x y, kernel_of_naturalUniversal hC A S e x y]
    exact h x y

/-- **The proof of closure is a unique translation.**  If a surjective physical return and a digital
evaluation are given the same closure verdicts by a natural universal criterion, then there is
exactly one dictionary `t` between their return languages, and it is the unique NRRF710 natural
translational equality `e = t ∘ r`. -/
theorem unique_dictionary_of_closure_agree {C : ClosureCriterion} (hC : NaturalUniversal C)
    {A R S : Type} {r : A → R} {e : A → S} (hr : Surjective r)
    (h : ∀ x y, C A R r x y ↔ C A S e x y) :
    ∃! t : R → S, NRRF710.NatEq r t e id id := by
  have hharn : NRRF709.Harness r e := (closure_agree_iff_harness hC r e).1 h
  obtain ⟨t, ht, huniq⟩ := NRRF709.harness_translation_existsUnique hr hharn
  refine ⟨t, ?_, ?_⟩
  · intro x; exact (ht x).symm
  · intro t' ht'
    exact huniq t' fun x => (ht' x).symm

/-- The unique dictionary is injective: the two return languages are mutually recoverable, so
neither is privileged. -/
theorem dictionary_injective_of_closure_agree {C : ClosureCriterion} (hC : NaturalUniversal C)
    {A R S : Type} {r : A → R} {e : A → S} {t : R → S} (hr : Surjective r)
    (h : ∀ x y, C A R r x y ↔ C A S e x y) (ht : ∀ x, t (r x) = e x) : Injective t :=
  NRRF709.harness_translation_injective hr ((closure_agree_iff_harness hC r e).1 h) ht

/-- Conversely, a translation of the return language never changes the closure: relabelling by any
injection, and reparametrizing the occurrences, leave every verdict intact.  Together with
`kernel_of_naturalUniversal` this is the two-sided statement: closure is invariant under
translation, and only translation-invariant closure exists. -/
theorem closure_translation_invariant {C : ClosureCriterion} (hC : NaturalUniversal C)
    {A A' R S : Type} (r : A → R) (i : R → S) (hi : Injective i) (f : A' → A) (x y : A') :
    C A' S ((i ∘ r) ∘ f) x y ↔ C A R r (f x) (f y) := by
  rw [kernel_of_naturalUniversal hC, kernel_of_naturalUniversal hC]
  exact ⟨fun h => hi h, fun h => congrArg i h⟩

/-! ## §5  Independence of the four conditions -/

/-- Nothing closes. -/
def botClosure : ClosureCriterion := fun _ _ _ _ _ => False

/-- Everything closes: absolute collapse. -/
def topClosure : ClosureCriterion := fun _ _ _ _ _ => True

/-- Only literally identical occurrences close: closure reduced to identity of representation. -/
def identityClosure : ClosureCriterion := fun _ _ _ x y => x = y

/-- Closure that reads the *names* in the return language: it closes whenever the returns agree, but
also closes everything as soon as the label type happens to be infinite. -/
def labelSizeClosure : ClosureCriterion := fun _ R r x y => r x = r y ∨ Infinite R

theorem botClosure_not_crefl : ¬ (∀ (A R : Type) (r : A → R) (x : A), botClosure A R r x x) :=
  fun h => h Unit Unit id ()

theorem botClosure_reparam (A A' R : Type) (r : A → R) (f : A' → A) (x y : A') :
    botClosure A' R (r ∘ f) x y ↔ botClosure A R r (f x) (f y) := Iff.rfl

theorem botClosure_relabel (A R S : Type) (r : A → R) (i : R → S) (_ : Injective i) (x y : A) :
    botClosure A S (i ∘ r) x y ↔ botClosure A R r x y := Iff.rfl

theorem botClosure_discerning : ¬ botClosure Bool Bool id false true := id

theorem topClosure_crefl (A R : Type) (r : A → R) (x : A) : topClosure A R r x x := trivial

theorem topClosure_reparam (A A' R : Type) (r : A → R) (f : A' → A) (x y : A') :
    topClosure A' R (r ∘ f) x y ↔ topClosure A R r (f x) (f y) := Iff.rfl

theorem topClosure_relabel (A R S : Type) (r : A → R) (i : R → S) (_ : Injective i) (x y : A) :
    topClosure A S (i ∘ r) x y ↔ topClosure A R r x y := Iff.rfl

theorem topClosure_not_discerning : topClosure Bool Bool id false true := trivial

theorem identityClosure_crefl (A R : Type) (r : A → R) (x : A) : identityClosure A R r x x := rfl

theorem identityClosure_relabel (A R S : Type) (r : A → R) (i : R → S) (_ : Injective i) (x y : A) :
    identityClosure A S (i ∘ r) x y ↔ identityClosure A R r x y := Iff.rfl

theorem identityClosure_discerning : ¬ identityClosure Bool Bool id false true := by
  simp [identityClosure]

theorem identityClosure_not_reparam :
    ¬ (∀ (A A' R : Type) (r : A → R) (f : A' → A) (x y : A'),
        identityClosure A' R (r ∘ f) x y ↔ identityClosure A R r (f x) (f y)) := by
  intro h
  have := (h Unit Bool Unit (fun _ => ()) (fun _ => ()) false true).2 rfl
  simp [identityClosure] at this

theorem labelSizeClosure_crefl (A R : Type) (r : A → R) (x : A) : labelSizeClosure A R r x x :=
  Or.inl rfl

theorem labelSizeClosure_reparam (A A' R : Type) (r : A → R) (f : A' → A) (x y : A') :
    labelSizeClosure A' R (r ∘ f) x y ↔ labelSizeClosure A R r (f x) (f y) := Iff.rfl

theorem labelSizeClosure_discerning : ¬ labelSizeClosure Bool Bool id false true := by
  intro h
  rcases h with h | h
  · exact Bool.noConfusion h
  · exact (not_finite Bool)

theorem labelSizeClosure_not_relabel :
    ¬ (∀ (A R S : Type) (r : A → R) (i : R → S), Injective i → ∀ (x y : A),
        labelSizeClosure A S (i ∘ r) x y ↔ labelSizeClosure A R r x y) := by
  intro h
  have hi : Injective (fun b : Bool => if b then 1 else 0 : Bool → ℕ) := by decide
  have := (h Bool Bool ℕ id _ hi false true).1 (Or.inr inferInstance)
  rcases this with h' | h'
  · exact Bool.noConfusion h'
  · exact (not_finite Bool)

/-- **Independence.**  Each of the four conditions rules out a genuinely different, non-translational
notion of closure; none of them may be dropped. -/
theorem independence_of_the_four_conditions :
    (¬ (∀ (A R : Type) (r : A → R) (x : A), botClosure A R r x x)) ∧
    (topClosure Bool Bool id false true) ∧
    (¬ (∀ (A A' R : Type) (r : A → R) (f : A' → A) (x y : A'),
        identityClosure A' R (r ∘ f) x y ↔ identityClosure A R r (f x) (f y))) ∧
    (¬ (∀ (A R S : Type) (r : A → R) (i : R → S), Injective i → ∀ (x y : A),
        labelSizeClosure A S (i ∘ r) x y ↔ labelSizeClosure A R r x y)) :=
  ⟨botClosure_not_crefl, topClosure_not_discerning, identityClosure_not_reparam,
    labelSizeClosure_not_relabel⟩

/-! ## §6  Correspondence is not closure

The empirical form of the claim is that a physical realization and a digital evaluation may **not**
be compared by *correspondence* — by pushing both into one scale and checking that the numbers
match.  Correspondence is neither sufficient nor necessary for closure, and unlike closure it is not
invariant under a lossless relabelling of either language. -/

section Correspondence

/-- **Numerical correspondence**: the two readings agree at every occurrence once pushed into a
common scale by chosen observables.  This is the informal "physical output corresponds to the
digital number". -/
def Corresponds {A R S : Type} (nu : R → ℝ) (nu' : S → ℝ) (r : A → R) (e : A → S) : Prop :=
  ∀ x, nu (r x) = nu' (e x)

/-- Correspondence is **not sufficient**: the two readings can agree numerically at *every*
occurrence while inducing different partitions, so no closure holds and no dictionary exists. -/
theorem correspondence_not_sufficient :
    Corresponds (fun _ : Bool => (0 : ℝ)) (fun _ : Unit => (0 : ℝ)) (id : Bool → Bool)
        (fun _ => ()) ∧
      ¬ NRRF709.Harness (id : Bool → Bool) (fun _ : Bool => ()) := by
  refine ⟨fun _ => rfl, fun h => ?_⟩
  exact Bool.noConfusion ((h false true).2 rfl)

/-- Correspondence is **not necessary**: two readings can close — same partition, hence exactly one
invertible dictionary — while their numerical values differ at every single occurrence.  This is the
precise sense in which the physical and digital returns *cannot* be required to correspond: they
must be translationally equal. -/
theorem correspondence_not_necessary :
    NRRF709.Harness (fun b : Bool => if b then (1 : ℕ) else 0) (fun b : Bool => if b then 3 else 2)
      ∧ ∀ b : Bool, (if b then (1 : ℕ) else 0) ≠ (if b then 3 else 2) := by
  constructor
  · intro x y; cases x <;> cases y <;> simp
  · intro b; cases b <;> simp

/-- Closure is invariant under a lossless relabelling of a return language; correspondence is not.
Relabelling the digital language by `n ↦ n + 1` destroys the numerical match and leaves the closure
untouched. -/
theorem correspondence_breaks_under_relabelling :
    NRRF709.Harness (fun b : Bool => if b then (1 : ℕ) else 0)
        ((fun n => n + 1) ∘ fun b : Bool => if b then (1 : ℕ) else 0) ∧
      ¬ Corresponds (fun n : ℕ => (n : ℝ)) (fun n : ℕ => (n : ℝ))
        (fun b : Bool => if b then (1 : ℕ) else 0)
        ((fun n => n + 1) ∘ fun b : Bool => if b then (1 : ℕ) else 0) := by
  constructor
  · intro x y; cases x <;> cases y <;> simp
  · intro h
    have := h false
    norm_num at this

end Correspondence

/-! ## §7  The empirical question: ellipse light in a dark silicon weave

Can a dark silicon weave realize the same closure as the optical ellipse weave, given that only
translation can naturally universally admit existence?  The answer the formalism gives is: **yes,
exactly when the silicon return retains the ordered hair, and never by numerical correspondence.**

* `ellipse_dark_silicon_harness` — the frozen transducer writing each traversal sense of the optical
  weave into a pair of silicon gate states makes the two returns one harness, in two different
  languages with no shared coordinates;
* `ellipse_dark_silicon_unique_dictionary` — the dictionary between the two return languages is then
  *forced*, not chosen;
* `bright_corresponds` together with `bright_not_harness` — the brightness reading of the optical
  weave and the gate-count reading of the silicon weave *do* correspond numerically, and that
  correspondence proves nothing: brightness is not a harness for the ordered return. -/

section DarkSilicon

/-- An optical ellipse weave: the ordered list of traversal senses (light/dark hair). -/
abbrev EllipseWeave := List Bool

/-- A dark silicon weave: the ordered list of gate states. -/
abbrev SiliconWeave := List (ℕ × ℕ)

/-- The **frozen** physical → digital transducer: each traversal sense of the optical ellipse weave
is written into the dark silicon weave as a pair of gate states.  It is fixed before any return is
read. -/
def siliconEncode : EllipseWeave → SiliconWeave :=
  List.map fun b => if b then (1, 0) else (0, 1)

theorem siliconEncode_injective : Injective siliconEncode := by
  apply List.map_injective_iff.2
  decide

/-- **The dark silicon weave closes with the ellipse light weave.**  The ordered silicon return and
the ordered optical return induce the same partition of occurrences, although their return languages
share no coordinates. -/
theorem ellipse_dark_silicon_harness :
    NRRF709.Harness (id : EllipseWeave → EllipseWeave)
      ((id : SiliconWeave → SiliconWeave) ∘ siliconEncode) := by
  intro x y
  constructor
  · intro h; exact congrArg _ h
  · intro h; exact siliconEncode_injective h

/-- The dictionary between the optical and the silicon return language is *forced* by the closure:
there is exactly one translation carrying the ellipse return onto the silicon return. -/
theorem ellipse_dark_silicon_unique_dictionary :
    ∃! t : EllipseWeave → SiliconWeave, ∀ w, t (id w) = siliconEncode w :=
  NRRF709.harness_translation_existsUnique (fun w => ⟨w, rfl⟩) ellipse_dark_silicon_harness

/-- The bright-port reading of the optical weave. -/
def opticBright (w : EllipseWeave) : ℕ := w.count true

/-- The corresponding gate-count reading of the silicon weave. -/
def siliconBright (s : SiliconWeave) : ℕ := s.count (1, 0)

/-- The two coarse readings **do** correspond numerically at every occurrence. -/
theorem bright_corresponds (w : EllipseWeave) : opticBright w = siliconBright (siliconEncode w) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
      cases b <;> simp [opticBright, siliconBright, siliconEncode] at ih ⊢ <;>
        omega

/-- …and that correspondence proves nothing: the brightness reading is **not** a harness for the
ordered return.  Two weaves with the same bright port carry different ordered hair. -/
theorem bright_not_harness :
    ¬ NRRF709.Harness (id : EllipseWeave → EllipseWeave) opticBright := by
  intro h
  have : ([true, false] : EllipseWeave) = [false, true] :=
    (h [true, false] [false, true]).2 (by decide)
  exact absurd this (by decide)

/-- **Answer to the empirical question.**  A dark silicon weave can realize the ellipse-light
closure — the two returns form one harness with a unique forced dictionary — while the numerical
bright-port correspondence between them, which does hold, is by itself no evidence of closure at
all: it is not even a harness for the ordered return.  Closure is translational equality of the
enriched returns, never numerical correspondence of their projections. -/
theorem ellipse_light_in_dark_silicon_weave :
    NRRF709.Harness (id : EllipseWeave → EllipseWeave)
        ((id : SiliconWeave → SiliconWeave) ∘ siliconEncode) ∧
      (∃! t : EllipseWeave → SiliconWeave, ∀ w, t (id w) = siliconEncode w) ∧
      (∀ w, opticBright w = siliconBright (siliconEncode w)) ∧
      ¬ NRRF709.Harness (id : EllipseWeave → EllipseWeave) opticBright :=
  ⟨ellipse_dark_silicon_harness, ellipse_dark_silicon_unique_dictionary, bright_corresponds,
    bright_not_harness⟩

end DarkSilicon

/-! ## §8  Only translation naturally universally admits existence -/

/-- An admission at the resolution of a return factors through that return; so once two occurrences
are closed, **no** admission at that resolution can treat them differently: closure is exactly what
admits existence at that resolution. -/
theorem closed_occurrences_are_admitted_alike {C : ClosureCriterion} (hC : NaturalUniversal C)
    {A R : Type} (r : A → R) (Ahat : R → R → Prop) {x y : A} (h : C A R r x y) :
    Ahat (r x) (r y) ↔ Ahat (r x) (r x) := by
  rw [(kernel_of_naturalUniversal hC A R r x y).1 h]

/-- Conversely, two occurrences that are *not* closed are separated by an admission at that
resolution.  Hence existence is admitted through translational equality and nothing else. -/
theorem admission_separates_iff_not_closed {C : ClosureCriterion} (hC : NaturalUniversal C)
    {A R : Type} (r : A → R) (x y : A) :
    (∃ Ahat : R → R → Prop, Ahat (r x) (r x) ∧ ¬ Ahat (r x) (r y)) ↔ ¬ C A R r x y := by
  constructor
  · rintro ⟨Ahat, hxx, hxy⟩ hclosed
    exact hxy ((closed_occurrences_are_admitted_alike hC r Ahat hclosed).2 hxx)
  · intro hnot
    refine ⟨fun a b => a = b, rfl, ?_⟩
    intro hEq
    exact hnot ((kernel_of_naturalUniversal hC A R r x y).2 hEq)

/-! ## §9  Capstone -/

/-- **Capstone.**  Translational closure naturally universally closes; it is the *only* criterion
that does; and whenever two independently presented readings of the same occurrences are closed by
it, that closure is witnessed by exactly one invertible translation between their return
languages — the natural translational equality of NRRF710.  Only translational proof can naturally
universally close. -/
theorem only_translational_proof_naturally_universally_closes :
    NaturalUniversal kernelClosure ∧
    (∀ C : ClosureCriterion, NaturalUniversal C →
      ∀ (A R : Type) (r : A → R) (x y : A), C A R r x y ↔ r x = r y) ∧
    (∀ {A R S : Type} {r : A → R} {e : A → S}, Surjective r →
      (∀ x y, kernelClosure A R r x y ↔ kernelClosure A S e x y) →
      ∃! t : R → S, NRRF710.NatEq r t e id id) := by
  refine ⟨kernelClosure_naturalUniversal,
    fun C hC A R r x y => kernel_of_naturalUniversal hC A R r x y, ?_⟩
  intro A R S r e hr h
  exact unique_dictionary_of_closure_agree kernelClosure_naturalUniversal hr h

/-- **Capstone, empirical form.**  Closure explicitly cannot be *correspondence*: numerical
agreement of the two readings is neither sufficient (`correspondence_not_sufficient`) nor necessary
(`correspondence_not_necessary`) for closure, and it is destroyed by a relabelling that leaves
closure intact (`correspondence_breaks_under_relabelling`).  What is required is translational
equality, and a dark silicon weave does realize it for the ellipse light weave exactly when its
return retains the ordered hair — its bright-port number, which does correspond, does not
(`ellipse_light_in_dark_silicon_weave`). -/
theorem closure_is_translational_equality_not_correspondence :
    (Corresponds (fun _ : Bool => (0 : ℝ)) (fun _ : Unit => (0 : ℝ)) (id : Bool → Bool)
        (fun _ => ()) ∧ ¬ NRRF709.Harness (id : Bool → Bool) (fun _ : Bool => ())) ∧
    (NRRF709.Harness (fun b : Bool => if b then (1 : ℕ) else 0)
        (fun b : Bool => if b then 3 else 2) ∧
      ∀ b : Bool, (if b then (1 : ℕ) else 0) ≠ (if b then 3 else 2)) ∧
    (NRRF709.Harness (id : EllipseWeave → EllipseWeave)
        ((id : SiliconWeave → SiliconWeave) ∘ siliconEncode) ∧
      (∃! t : EllipseWeave → SiliconWeave, ∀ w, t (id w) = siliconEncode w) ∧
      (∀ w, opticBright w = siliconBright (siliconEncode w)) ∧
      ¬ NRRF709.Harness (id : EllipseWeave → EllipseWeave) opticBright) :=
  ⟨correspondence_not_sufficient, correspondence_not_necessary,
    ellipse_light_in_dark_silicon_weave⟩

#print axioms kernel_of_naturalUniversal
#print axioms only_translational_proof_naturally_universally_closes
#print axioms closure_is_translational_equality_not_correspondence
#print axioms admission_separates_iff_not_closed

end NRRF711
