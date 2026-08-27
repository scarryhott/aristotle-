import Mathlib
import NRRF794ReunifiedTranslationalCompletenessQuantumGravity
import NRRF796SelfLimitInversionEqualityOneHairClosureBall

/-!
# NRRF798 — Unifying the full closure through translational truth

The instruction formalised here is the user's:

> Unify full closure through translational truth.

Nothing new is assumed.  The two halves of the closure that the earlier modules built — the
relational half (`LocalRel` with its scale reading `divg`, its hair reading `hair` and its neutral
sector) and the sensor half (the loop-sensor `State` with `gaugeClass`, `qgConfig`) — are here
placed under **one** notion, and the whole closure is recovered from it.

## The notion

For a translation relation `s` on a type of presentations, a truth `T : P → Prop` is
**translational** (`Translational`) when it is carried along every translation:
`s.r p q → (T p ↔ T q)`.  A reading is translational when translation does not move its value.

The general facts (§1), proved once and used three times:

* `truthEquiv` — the translational truths of `s` are **exactly** the truths of the closure
  `Quotient s`: an explicit equivalence `{T // Translational s T} ≃ (Quotient s → Prop)`.
* `related_iff_all_translational` — the closure is recovered from its truths: two presentations
  are translations of each other **iff** every translational truth agrees on them.  So
  translational truth is neither coarser nor finer than the closure.
* `translational_separates` — untranslated presentations are separated by a translational truth.
* `translational_not/and/or/imp/forall/exists` — the translational truths are closed under the
  whole propositional and quantificational apparatus: a *complete* Boolean, quantifier-closed
  algebra, not a fragment.
* `translational_iff_reading`, `quotEquivOfReading` — if a reading `f` decides translation
  (`s.r p q ↔ f p = f q`), then translational truth is exactly truth about `f`, and the closure is
  exactly the range of `f`.

## The two halves, and their union

* §2 the relational half: `relTr A B := Neutral (A - B)`, i.e. the translations are the neutral
  (shear) relations, which no reader sees.  `relTr_iff` — translation is exactly agreement of the
  scale and hair readings; `relQuotEquiv : Quotient relSetoid ≃ ℝ × (Fin 3 → ℝ)` — the relational
  closure **is** the ball–hair pair; `rel_truth_iff` — the translational truths of the relational
  half are exactly the truths about `(divg, hair)`.  `rel_closure_nontrivial` shows the quotient is
  genuine (the neutral sector is nonzero), and `relInv_descends` that the one inversion of NRRF796
  descends to the closure.
* §3 the sensor half: `stateTr k x y := gaugeClass k x = gaugeClass k y`.  `stateTr_iff_tests` —
  translation is exactly passing every loop test; `stateTr_iff_qgConfig` — and exactly equality of
  the geometric configuration `qgConfig`: sensors and geometry give the *same* translation
  relation.  `stateQuotEquiv : Quotient (stateSetoid k) ≃ ℤ × ZMod k`.
* §4 the union: `fullTr k` on `Full := LocalRel × State`.  `fullTr_iff_read`,
  `fullQuotEquiv`, `full_truth_iff` — the full closure is exactly the range of the one reading
  `fullRead k = ((divg, hair), gaugeClass k)`, and its truths are exactly the truths about that
  reading.  `rel_truth_embeds`, `state_truth_embeds`, `full_separated_by_sectors` — each half's
  translational truths sit inside the whole, and the two halves already separate everything the
  whole separates: no further sector is needed.

* §4b the link: `gravRel_morphism`, `embed_translational` — the sensor half sits inside the full
  closure along its own gravitational relation, and the embedding neither merges nor splits any
  translation class.  The halves are one theory read twice, not two theories side by side.

`nrrf798_unification` collects the clauses.  Everything is `sorry`-free and the axiom audit at the
end of the file is machine-checked.

As throughout this project, the physical words name the constructions defined here and in the
imported modules; every claim is a claim about those constructions.
-/

namespace NRRF798

open NRRF683 NRRF786 NRRF791 NRRF794 NRRF796

noncomputable section

/-! ## §1  Translational truth in general -/

section General

variable {P : Type*}

/-- A truth is **translational** for the translation relation `s` when translation carries it:
the truth of `T` is a truth about what the presentations have in common, not about the
presentation. -/
def Translational (s : Setoid P) (T : P → Prop) : Prop :=
  ∀ p q : P, s.r p q → (T p ↔ T q)

/-- A reading is **translational** when translation does not move its value. -/
def TranslationalReading {V : Type*} (s : Setoid P) (f : P → V) : Prop :=
  ∀ p q : P, s.r p q → f p = f q

/-- Any truth about the value of a translational reading is a translational truth. -/
theorem translational_of_reading {V : Type*} {s : Setoid P} {f : P → V}
    (hf : TranslationalReading s f) (g : V → Prop) : Translational s (fun p => g (f p)) :=
  fun p q h => by show g (f p) ↔ g (f q); rw [hf p q h]

theorem translational_const (s : Setoid P) (b : Prop) : Translational s (fun _ => b) :=
  fun _ _ _ => Iff.rfl

theorem translational_not {s : Setoid P} {T : P → Prop} (h : Translational s T) :
    Translational s (fun p => ¬ T p) :=
  fun p q hpq => not_congr (h p q hpq)

theorem translational_and {s : Setoid P} {T U : P → Prop} (hT : Translational s T)
    (hU : Translational s U) : Translational s (fun p => T p ∧ U p) :=
  fun p q hpq => and_congr (hT p q hpq) (hU p q hpq)

theorem translational_or {s : Setoid P} {T U : P → Prop} (hT : Translational s T)
    (hU : Translational s U) : Translational s (fun p => T p ∨ U p) :=
  fun p q hpq => or_congr (hT p q hpq) (hU p q hpq)

theorem translational_imp {s : Setoid P} {T U : P → Prop} (hT : Translational s T)
    (hU : Translational s U) : Translational s (fun p => T p → U p) :=
  fun p q hpq => imp_congr (hT p q hpq) (hU p q hpq)

theorem translational_forall {ι : Type*} {s : Setoid P} {T : ι → P → Prop}
    (hT : ∀ i, Translational s (T i)) : Translational s (fun p => ∀ i, T i p) :=
  fun p q hpq => forall_congr' fun i => hT i p q hpq

theorem translational_exists {ι : Type*} {s : Setoid P} {T : ι → P → Prop}
    (hT : ∀ i, Translational s (T i)) : Translational s (fun p => ∃ i, T i p) :=
  fun p q hpq => exists_congr fun i => hT i p q hpq

/-- Being a translation of a fixed presentation is itself a translational truth. -/
theorem translational_rel (s : Setoid P) (a : P) : Translational s (fun p => s.r p a) :=
  fun _ _ hpq => ⟨fun hp => s.trans (s.symm hpq) hp, fun hq => s.trans hpq hq⟩

/-- **Translational truths are exactly truths of the closure.**  A truth is translational iff it
factors through the quotient by translation. -/
theorem translational_iff_factors (s : Setoid P) (T : P → Prop) :
    Translational s T ↔ ∃ f : Quotient s → Prop, ∀ p, T p ↔ f (Quotient.mk s p) := by
  constructor
  · intro h
    refine ⟨fun c => Quotient.liftOn c T fun a b hab => propext (h a b hab), fun p => Iff.rfl⟩
  · rintro ⟨f, hf⟩ p q hpq
    rw [hf p, hf q, Quotient.sound hpq]

/-- **The unification, in its cleanest form.**  The translational truths of a translation relation
are in explicit bijection with the truths of its closure. -/
def truthEquiv (s : Setoid P) : {T : P → Prop // Translational s T} ≃ (Quotient s → Prop) where
  toFun T := fun c => Quotient.liftOn c T.1 fun a b hab => propext (T.2 a b hab)
  invFun f := ⟨fun p => f (Quotient.mk s p),
    fun p q hpq => by show f (Quotient.mk s p) ↔ f (Quotient.mk s q); rw [Quotient.sound hpq]⟩
  left_inv T := rfl
  right_inv f := by
    funext c
    induction c using Quotient.inductionOn
    rfl

/-- **Untranslated presentations are separated by a translational truth.** -/
theorem translational_separates {s : Setoid P} {p q : P} (h : ¬ s.r p q) :
    ∃ T : P → Prop, Translational s T ∧ T p ∧ ¬ T q :=
  ⟨fun x => s.r x p, translational_rel s p, s.refl p, fun hq => h (s.symm hq)⟩

/-- **The closure is recovered from its translational truths.**  Two presentations are translations
of one another exactly when no translational truth tells them apart. -/
theorem related_iff_all_translational (s : Setoid P) (p q : P) :
    s.r p q ↔ ∀ T : P → Prop, Translational s T → (T p ↔ T q) := by
  refine ⟨fun h T hT => hT p q h, fun h => ?_⟩
  by_contra hpq
  obtain ⟨T, hT, hTp, hTq⟩ := translational_separates hpq
  exact hTq ((h T hT).1 hTp)

/-- If a reading decides translation, translational truth is exactly truth about that reading. -/
theorem translational_iff_reading {V : Type*} (s : Setoid P) (f : P → V)
    (hf : ∀ p q, s.r p q ↔ f p = f q) (T : P → Prop) :
    Translational s T ↔ ∃ g : V → Prop, ∀ p, T p ↔ g (f p) := by
  constructor
  · intro h
    refine ⟨fun v => ∃ p, f p = v ∧ T p, fun p => ⟨fun hp => ⟨p, rfl, hp⟩, ?_⟩⟩
    rintro ⟨q, hq, hTq⟩
    exact (h q p ((hf q p).2 hq)).1 hTq
  · rintro ⟨g, hg⟩ p q hpq
    rw [hg p, hg q, (hf p q).1 hpq]

/-- If a surjective reading decides translation, the closure **is** the range of the reading. -/
def quotEquivOfReading {V : Type*} (s : Setoid P) (f : P → V)
    (hf : ∀ p q, s.r p q ↔ f p = f q) (hsurj : Function.Surjective f) : Quotient s ≃ V where
  toFun c := Quotient.liftOn c f fun a b hab => (hf a b).1 hab
  invFun v := Quotient.mk s (hsurj v).choose
  left_inv c := by
    induction c using Quotient.inductionOn with
    | h p =>
      exact Quotient.eq''.2 ((hf _ p).2 (hsurj (f p)).choose_spec)
  right_inv v := (hsurj v).choose_spec

end General

/-! ## §2  The relational half: translation by the neutral sector -/

theorem divg_sub (A B : LocalRel) : divg (A - B) = divg A - divg B := by
  simp [divg, Matrix.trace_sub]

theorem curl_sub (A B : LocalRel) : curl (A - B) = curl A - curl B := by
  funext i
  fin_cases i <;> simp [curl] <;> ring

theorem hair_sub (A B : LocalRel) : hair (A - B) = hair A - hair B := by
  funext i
  simp [hair, curl_sub]
  ring

/-- **Translation of local relations**: `A` translates to `B` when they differ by a neutral
relation — one that neither the scale reader nor the hair reader sees. -/
def relTr (A B : LocalRel) : Prop := Neutral (A - B)

/-- The relational readings: the ball (scale) reading and the hair reading. -/
def relRead (A : LocalRel) : ℝ × (Fin 3 → ℝ) := (divg A, hair A)

/-- **Translation is exactly agreement of the two forced readings.** -/
theorem relTr_iff {A B : LocalRel} : relTr A B ↔ relRead A = relRead B := by
  rw [relTr, neutral_iff_no_source_no_hair, divg_sub, hair_sub, relRead, relRead,
    Prod.ext_iff, sub_eq_zero, sub_eq_zero]

theorem relTr_equivalence : Equivalence relTr := by
  constructor
  · intro A; exact relTr_iff.2 rfl
  · intro A B h; exact relTr_iff.2 (relTr_iff.1 h).symm
  · intro A B C h h'; exact relTr_iff.2 ((relTr_iff.1 h).trans (relTr_iff.1 h'))

/-- The translation relation of the relational half of the closure. -/
def relSetoid : Setoid LocalRel := ⟨relTr, relTr_equivalence⟩

theorem relSetoid_iff {A B : LocalRel} : relSetoid.r A B ↔ relRead A = relRead B := relTr_iff

/-- The relational readings are translational, by construction. -/
theorem relRead_translational : TranslationalReading relSetoid relRead :=
  fun _ _ h => relSetoid_iff.1 h

/-- The relation put together from a scale value and a hair value. -/
def relRep (p : ℝ × (Fin 3 → ℝ)) : LocalRel := (p.1 / 3) • (1 : LocalRel) + axialMat p.2

theorem divg_relRep (p : ℝ × (Fin 3 → ℝ)) : divg (relRep p) = p.1 := by
  have hax : Matrix.trace (axialMat p.2) = 0 := trace_of_antisym (axialMat_antisym p.2)
  simp [relRep, divg, Matrix.trace_add, hax]

theorem hair_relRep (p : ℝ × (Fin 3 → ℝ)) : hair (relRep p) = p.2 := by
  have h1 : curl ((p.1 / 3) • (1 : LocalRel)) = 0 := by
    funext i
    fin_cases i <;> simp [curl]
  funext i
  simp [hair, relRep, curl_add, h1, curl_axialMat]

theorem relRead_relRep (p : ℝ × (Fin 3 → ℝ)) : relRead (relRep p) = p := by
  rw [relRead, divg_relRep, hair_relRep]

theorem relRead_surjective : Function.Surjective relRead := fun p => ⟨relRep p, relRead_relRep p⟩

/-- **The relational closure is exactly the ball–hair pair.** -/
def relQuotEquiv : Quotient relSetoid ≃ ℝ × (Fin 3 → ℝ) :=
  quotEquivOfReading relSetoid relRead (fun _ _ => relSetoid_iff) relRead_surjective

/-- **The translational truths of the relational half are exactly the truths about `(divg, hair)`.** -/
theorem rel_truth_iff (T : LocalRel → Prop) :
    Translational relSetoid T ↔ ∃ g : ℝ × (Fin 3 → ℝ) → Prop, ∀ A, T A ↔ g (relRead A) :=
  translational_iff_reading relSetoid relRead (fun _ _ => relSetoid_iff) T

/-- Adding a neutral relation is a translation: the neutral sector is invisible to truth. -/
theorem neutral_invisible {N : LocalRel} (hN : Neutral N) (A : LocalRel) :
    relSetoid.r (A + N) A := by
  have : A + N - A = N := by abel
  exact (show Neutral (A + N - A) by rw [this]; exact hN)

/-- The relational closure is a genuine quotient: distinct relations can be translations. -/
theorem rel_closure_nontrivial : ∃ A B : LocalRel, A ≠ B ∧ relSetoid.r A B := by
  obtain ⟨N, hN, hN0⟩ := neutral_nontrivial
  refine ⟨0 + N, 0, ?_, neutral_invisible hN 0⟩
  simpa using hN0

/-- **The one inversion descends to the closure**: it is a symmetry of translational truth. -/
theorem relInv_descends {A B : LocalRel} (h : relSetoid.r A B) :
    relSetoid.r (relInv A) (relInv B) := by
  obtain ⟨hd, hh⟩ := Prod.ext_iff.1 (relSetoid_iff.1 h)
  refine relSetoid_iff.2 (Prod.ext ?_ ?_)
  · simpa [relRead, divg_relInv] using congrArg Neg.neg hd
  · simpa [relRead, hair_relInv] using hh

/-! ## §3  The sensor half: translation by the gauge -/

/-- **Translation of loop-sensor states**: two states translate when their gauge classes agree. -/
def stateTr (k : ℕ) (x y : State) : Prop := gaugeClass k x = gaugeClass k y

theorem stateTr_equivalence (k : ℕ) : Equivalence (stateTr k) :=
  ⟨fun _ => rfl, fun h => h.symm, fun h h' => h.trans h'⟩

/-- The translation relation of the sensor half of the closure. -/
def stateSetoid (k : ℕ) : Setoid State := ⟨stateTr k, stateTr_equivalence k⟩

theorem stateSetoid_iff {k : ℕ} {x y : State} :
    (stateSetoid k).r x y ↔ gaugeClass k x = gaugeClass k y := Iff.rfl

/-- **Translation is exactly passing every loop test.** -/
theorem stateTr_iff_tests (k : ℕ) (x y : State) :
    (stateSetoid k).r x y ↔ ∀ n, 0 < n → Test k n x y :=
  (agree_iff_gaugeClass k x y).symm

/-- **Translation is exactly equality of the geometric configuration.**  The sensor picture and
the continuous relational picture define the *same* translation relation. -/
theorem stateTr_iff_qgConfig {k : ℕ} (hk : 0 < k) (x y : State) :
    (stateSetoid k).r x y ↔ qgConfig k x = qgConfig k y :=
  (stateTr_iff_tests k x y).trans (qgConfig_eq_iff_all_tests hk x y).symm

/-- Shifting the hair by its own period is a translation: the phase returns. -/
theorem hair_shift_invisible (k : ℕ) (x : State) :
    (stateSetoid k).r x (x.1, x.2 + (k : ℤ)) := by
  refine Prod.ext rfl ?_
  simp [gaugeClass, Int.cast_add]

/-- The sensor closure is a genuine quotient whenever the hair has a period. -/
theorem state_closure_nontrivial {k : ℕ} (hk : 0 < k) :
    ∃ x y : State, x ≠ y ∧ (stateSetoid k).r x y := by
  refine ⟨(0, 0), (0, (k : ℤ)), ?_, ?_⟩
  · intro hcon
    have h0 : (0 : ℤ) = (k : ℤ) := (Prod.ext_iff.1 hcon).2
    omega
  · simpa using hair_shift_invisible k (0, 0)

theorem gaugeClass_surjective (k : ℕ) : Function.Surjective (gaugeClass k) := by
  rintro ⟨m, a⟩
  obtain ⟨q, hq⟩ := ZMod.intCast_surjective (n := k) a
  exact ⟨(m, q), by simp [gaugeClass, hq]⟩

/-- **The sensor closure is exactly the gauge class space.** -/
def stateQuotEquiv (k : ℕ) : Quotient (stateSetoid k) ≃ ℤ × ZMod k :=
  quotEquivOfReading (stateSetoid k) (gaugeClass k) (fun _ _ => stateSetoid_iff)
    (gaugeClass_surjective k)

/-- **The translational truths of the sensor half are exactly the truths about the gauge class.** -/
theorem state_truth_iff (k : ℕ) (T : State → Prop) :
    Translational (stateSetoid k) T ↔ ∃ g : ℤ × ZMod k → Prop, ∀ x, T x ↔ g (gaugeClass k x) :=
  translational_iff_reading (stateSetoid k) (gaugeClass k) (fun _ _ => stateSetoid_iff) T

/-! ## §4  The full closure -/

/-- A **full presentation**: a local relation together with a loop-sensor state. -/
abbrev Full := LocalRel × State

/-- **Translation of full presentations**: translation in each half. -/
def fullTr (k : ℕ) (p q : Full) : Prop := relTr p.1 q.1 ∧ stateTr k p.2 q.2

/-- The single reading of the full closure. -/
def fullRead (k : ℕ) (p : Full) : (ℝ × (Fin 3 → ℝ)) × (ℤ × ZMod k) :=
  (relRead p.1, gaugeClass k p.2)

theorem fullTr_iff_read {k : ℕ} {p q : Full} : fullTr k p q ↔ fullRead k p = fullRead k q := by
  rw [fullTr, fullRead, fullRead, Prod.ext_iff, relTr_iff]
  rfl

theorem fullTr_equivalence (k : ℕ) : Equivalence (fullTr k) := by
  constructor
  · intro p; exact fullTr_iff_read.2 rfl
  · intro p q h; exact fullTr_iff_read.2 (fullTr_iff_read.1 h).symm
  · intro p q r h h'; exact fullTr_iff_read.2 ((fullTr_iff_read.1 h).trans (fullTr_iff_read.1 h'))

/-- The translation relation of the full closure. -/
def fullSetoid (k : ℕ) : Setoid Full := ⟨fullTr k, fullTr_equivalence k⟩

theorem fullSetoid_iff {k : ℕ} {p q : Full} :
    (fullSetoid k).r p q ↔ fullRead k p = fullRead k q := fullTr_iff_read

/-- **The two halves are jointly the whole**: full translation is translation in each half, and
nothing else. -/
theorem fullSetoid_iff_sectors {k : ℕ} {p q : Full} :
    (fullSetoid k).r p q ↔ relSetoid.r p.1 q.1 ∧ (stateSetoid k).r p.2 q.2 := Iff.rfl

theorem fullRead_surjective (k : ℕ) : Function.Surjective (fullRead k) := by
  rintro ⟨u, v⟩
  obtain ⟨A, hA⟩ := relRead_surjective u
  obtain ⟨x, hx⟩ := gaugeClass_surjective k v
  exact ⟨(A, x), by simp [fullRead, hA, hx]⟩

/-- **The full closure is exactly the range of the one reading**: ball, hair, and gauge class. -/
def fullQuotEquiv (k : ℕ) :
    Quotient (fullSetoid k) ≃ (ℝ × (Fin 3 → ℝ)) × (ℤ × ZMod k) :=
  quotEquivOfReading (fullSetoid k) (fullRead k) (fun _ _ => fullSetoid_iff)
    (fullRead_surjective k)

/-- **The translational truths of the full closure are exactly the truths about the one
reading.** -/
theorem full_truth_iff (k : ℕ) (T : Full → Prop) :
    Translational (fullSetoid k) T ↔
      ∃ g : (ℝ × (Fin 3 → ℝ)) × (ℤ × ZMod k) → Prop, ∀ p, T p ↔ g (fullRead k p) :=
  translational_iff_reading (fullSetoid k) (fullRead k) (fun _ _ => fullSetoid_iff) T

/-- Every relational translational truth is a translational truth of the whole. -/
theorem rel_truth_embeds {k : ℕ} {S : LocalRel → Prop} (hS : Translational relSetoid S) :
    Translational (fullSetoid k) (fun p => S p.1) :=
  fun p q hpq => hS p.1 q.1 hpq.1

/-- Every sensor translational truth is a translational truth of the whole. -/
theorem state_truth_embeds {k : ℕ} {S : State → Prop} (hS : Translational (stateSetoid k) S) :
    Translational (fullSetoid k) (fun p => S p.2) :=
  fun p q hpq => hS p.2 q.2 hpq.2

/-- **The two halves already separate everything the whole separates.**  Whenever two full
presentations are not translations of one another, a truth of one of the two halves — pulled back
to the whole — tells them apart.  No third sector is needed to close the theory. -/
theorem full_separated_by_sectors {k : ℕ} {p q : Full} (h : ¬ (fullSetoid k).r p q) :
    ∃ T : Full → Prop, Translational (fullSetoid k) T ∧ T p ∧ ¬ T q ∧
      ((∃ S : LocalRel → Prop, Translational relSetoid S ∧ T = fun z => S z.1) ∨
        (∃ S : State → Prop, Translational (stateSetoid k) S ∧ T = fun z => S z.2)) := by
  by_cases hrel : relSetoid.r p.1 q.1
  · have hst : ¬ (stateSetoid k).r p.2 q.2 := fun hst => h ⟨hrel, hst⟩
    refine ⟨fun z => (stateSetoid k).r z.2 p.2, state_truth_embeds (translational_rel _ p.2),
      (stateSetoid k).refl p.2, fun hq => hst ((stateSetoid k).symm hq), Or.inr ?_⟩
    exact ⟨fun x => (stateSetoid k).r x p.2, translational_rel _ p.2, rfl⟩
  · refine ⟨fun z => relSetoid.r z.1 p.1, rel_truth_embeds (translational_rel _ p.1),
      relSetoid.refl p.1, fun hq => hrel (relSetoid.symm hq), Or.inl ?_⟩
    exact ⟨fun A => relSetoid.r A p.1, translational_rel _ p.1, rfl⟩

/-! ## §4b  The two halves are linked, not merely juxtaposed -/

/-- The gravitational relation of a state is a **morphism of closures**: translated states have
translated relations. -/
theorem gravRel_morphism {k : ℕ} {x y : State} (h : (stateSetoid k).r x y) :
    relSetoid.r (gravRel x) (gravRel y) := by
  have hb : x.1 = y.1 := congrArg (fun p : ℤ × ZMod k => p.1) (stateSetoid_iff.1 h)
  exact relSetoid_iff.2 (by rw [gravRel, gravRel, hb])

/-- The sensor half sits inside the full closure along its own gravitational relation. -/
def embed (x : State) : Full := (gravRel x, x)

/-- **The embedding is faithful for translational truth**: a state translates to another exactly
when its full presentation does.  The two halves of the closure are one theory read twice. -/
theorem embed_translational (k : ℕ) (x y : State) :
    (stateSetoid k).r x y ↔ (fullSetoid k).r (embed x) (embed y) :=
  ⟨fun h => ⟨gravRel_morphism h, h⟩, fun h => h.2⟩

/-! ## §5  The unification -/

/-- **NRRF798 — the full closure, unified through translational truth.**

For every hair period `k > 0`:

1. the translational truths of the full closure are in explicit bijection with the truths of the
   closure itself — translational truth *is* the truth of the closure;
2. two full presentations are translations of one another exactly when no translational truth
   separates them, so the closure is recovered from its translational truths and nothing finer is
   hiding behind them;
3. a truth of the whole is translational exactly when it is a truth about the single reading
   `((divg, hair), gaugeClass k)`;
4. that reading is onto: every value of the closure is realised, so the unification is not
   vacuous;
5. the whole is the two halves and nothing more: full translation is relational translation
   together with sensor translation, and the two halves already separate everything;
6. on the sensor half translation is simultaneously "passes every loop test" and "has the same
   geometric configuration" — the discrete and continuous pictures give one relation;
7. both closures are genuine quotients: the neutral sector and the hair period are invisible to
   every translational truth while being nonzero moves of the presentation;
8. the halves are linked, not merely juxtaposed: a state translates to another exactly when its
   full presentation — the state together with its own gravitational relation — does. -/
theorem nrrf798_unification (k : ℕ) (hk : 0 < k) :
    (Nonempty ({T : Full → Prop // Translational (fullSetoid k) T} ≃ (Quotient (fullSetoid k) → Prop)))
      ∧ (∀ p q : Full, (fullSetoid k).r p q ↔
          ∀ T : Full → Prop, Translational (fullSetoid k) T → (T p ↔ T q))
      ∧ (∀ T : Full → Prop, Translational (fullSetoid k) T ↔
          ∃ g : (ℝ × (Fin 3 → ℝ)) × (ℤ × ZMod k) → Prop, ∀ p, T p ↔ g (fullRead k p))
      ∧ Function.Surjective (fullRead k)
      ∧ (∀ p q : Full, (fullSetoid k).r p q ↔
          relSetoid.r p.1 q.1 ∧ (stateSetoid k).r p.2 q.2)
      ∧ (∀ x y : State, (stateSetoid k).r x y ↔ (∀ n, 0 < n → Test k n x y))
      ∧ (∀ x y : State, (stateSetoid k).r x y ↔ qgConfig k x = qgConfig k y)
      ∧ (∃ A B : LocalRel, A ≠ B ∧ relSetoid.r A B)
      ∧ (∃ x y : State, x ≠ y ∧ (stateSetoid k).r x y)
      ∧ (∀ x y : State, (stateSetoid k).r x y ↔ (fullSetoid k).r (embed x) (embed y)) :=
  ⟨⟨truthEquiv (fullSetoid k)⟩,
    related_iff_all_translational (fullSetoid k),
    full_truth_iff k,
    fullRead_surjective k,
    fun _ _ => fullSetoid_iff_sectors,
    stateTr_iff_tests k,
    fun x y => stateTr_iff_qgConfig hk x y,
    rel_closure_nontrivial,
    state_closure_nontrivial hk,
    embed_translational k⟩

end

end NRRF798

/-! ## Axiom audit -/

#print axioms NRRF798.truthEquiv
#print axioms NRRF798.related_iff_all_translational
#print axioms NRRF798.relQuotEquiv
#print axioms NRRF798.rel_truth_iff
#print axioms NRRF798.stateQuotEquiv
#print axioms NRRF798.state_truth_iff
#print axioms NRRF798.fullQuotEquiv
#print axioms NRRF798.full_truth_iff
#print axioms NRRF798.full_separated_by_sectors
#print axioms NRRF798.nrrf798_unification
#print axioms NRRF798.embed_translational
