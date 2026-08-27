import Mathlib
import NRRF772LinearLayoutRelativeEqualityFunctionsCompleteness
import NRRF775NaturalFormSelectorUnifaceRelationalDeterminationUnitaryPathPartitionTraces

/-!
# NRRF781 — The unique closure independently resolves the need for renormalisation

The reading being formalised:

> Prove our unique closure independently resolves need for renormalization, using not ZFC but
> translational truth.

**What renormalisation is, as a relational statement.**  A regularised family is a collection of
amplitudes `a i n`, one for each member `i` of the family, each read at a cutoff `n`.  The classical
difficulty is that the individual amplitude has no value: `a i n` runs away as the cutoff is
removed.  The classical repair is *renormalisation*: choose a counterterm `c n`, subtract it, and
take the limit.  The repair is not free — it needs an external input (a "renormalisation
condition"), because the counterterm is only fixed up to a constant.

**What is proved here.**

* **§1 The classical repair and its ambiguity.**  A scheme is a counterterm together with the limits
  it produces (`SchemeValues`).  Shifting the counterterm by a constant is again a scheme
  (`shift_scheme`), and it moves *every* renormalised value (`renormalised_value_not_determined`).
  So no function of the raw regularised data returns the absolute renormalised value
  (`no_absolute_reading`): an external condition must be imported.  That import is the need for
  renormalisation.
* **§2 The relative reading is already determined.**  The differences of renormalised values are the
  same in every scheme (`difference_scheme_independent`), because they are the limit of a difference
  that never diverges.
* **§3 The closure needs no scheme, no limit and no cutoff removal.**  For a family whose divergence
  is common to its members (`CommonDivergence` — the universality of the divergent part), the
  relative reading is *literally constant in the cutoff* (`diff_cutoff_independent`), so it can be
  read off at any single finite cutoff; and what it reads there is exactly what any admissible
  renormalisation scheme would have produced in the limit (`rel_eq_scheme_diff`).  This is
  `closure_resolves_renormalization`: the closure reading is total, finite, scheme-free and
  limit-free, and it loses nothing, because the only thing it does not carry is the one thing the
  raw data never determined either.
* **§4 The closure is unique, and this part uses no analysis at all.**  On value assignments valued
  in *any* additive group — no real numbers, no completeness, no limits, no choice — the relative
  reading `relRead` is invariant under the scheme shift (`relRead_shiftInvariant`) and *every*
  shift-invariant reading is a translation of it (`shiftInvariant_iff_refines`), so it is the
  greatest determined content; anything with the same property is translationally equal to it in the
  sense of NRRF772 (`closure_unique`).  The absolute level is not recoverable
  (`relRead_not_complete`), exactly as §1 requires.
* **§5 A concrete log-divergent family.**  `logAmp` diverges member by member (`logAmp_diverges`,
  `logAmp_no_limit`), yet its closure reading is finite and available at cutoff `0`
  (`logAmp_rel`), and coincides with the limit of the minimal-subtraction scheme
  (`logAmp_scheme`).
* **§6 The closure as a natural form selection.**  The relative reading is the natural form selector
  of NRRF775 applied to the relation that the raw data itself determines (`relSel_eq`), and it is
  the unique such determination (`relSel_unique`): the closure is selected by the relation, not
  chosen by an agent.
* **§7 Not ZFC but translational truth.**  The resolution itself is not an analytic fact.  Its two
  load-bearing clauses — that the relation between members is the same at every cutoff
  (`diffG_cutoff_independent`) and that the relative reading is the unique greatest scheme-invariant
  reading (`relRead_shiftInvariant`, `shiftInvariant_iff_refines`, `closure_unique`) — are stated and
  proved for amplitudes valued in an arbitrary additive group, with no real numbers, no limit, no
  completion and no choice principle: the axiom audit in §8 shows them depending on `propext` and
  `Quot.sound` only.  The real-valued clauses invoke `Classical.choice`, but only through the
  construction of `ℝ` itself.  So what removes the need for renormalisation is not a set-theoretic
  or analytic device but a translation of truth between relative equality functions.

`nrrf781_answer` collects the clauses.
-/

namespace NRRF781

open Filter Topology

/-! ## §0 Regularised families -/

variable {ι : Type*}

/-- **Common divergence.**  The divergent part `f` of the family is universal: it does not depend on
which member of the family is being read.  Only the finite remainder `g` distinguishes members. -/
def CommonDivergence (a : ι → ℕ → ℝ) : Prop :=
  ∃ (f : ℕ → ℝ) (g : ι → ℝ), ∀ i n, a i n = f n + g i

/-- **A renormalisation scheme with its values.**  The counterterm `c` is subtracted from every
member and the cutoff is removed; `v i` is the finite value that member `i` is thereby assigned. -/
def SchemeValues (a : ι → ℕ → ℝ) (c : ℕ → ℝ) (v : ι → ℝ) : Prop :=
  ∀ i, Tendsto (fun n => a i n - c n) atTop (𝓝 (v i))

/-! ## §1 The classical repair and its ambiguity -/

/-- Shifting the counterterm by a constant is again an admissible scheme; every value moves by that
constant. -/
theorem shift_scheme {a : ι → ℕ → ℝ} {c : ℕ → ℝ} {v : ι → ℝ} (h : SchemeValues a c v) (k : ℝ) :
    SchemeValues a (fun n => c n + k) (fun i => v i - k) := by
  intro i
  have := (h i).sub_const k
  refine this.congr fun n => by ring

/-- **The renormalised value is not determined by the regularised data.**  Whatever scheme is used,
another scheme is available which assigns a different value to every member. -/
theorem renormalised_value_not_determined {a : ι → ℕ → ℝ} {c : ℕ → ℝ} {v : ι → ℝ}
    (h : SchemeValues a c v) :
    ∃ (c' : ℕ → ℝ) (v' : ι → ℝ), SchemeValues a c' v' ∧ ∀ i, v' i ≠ v i := by
  refine ⟨fun n => c n + 1, fun i => v i - 1, shift_scheme h 1, fun i => by intro hi; linarith [hi]⟩

/-- **No absolute reading exists.**  There is no assignment of values to members which is forced by
the regularised data alone: the two schemes above are equally admissible and disagree everywhere.
Hence the classical procedure must import an external renormalisation condition. -/
theorem no_absolute_reading {a : ι → ℕ → ℝ} {c : ℕ → ℝ} {v : ι → ℝ} (h : SchemeValues a c v)
    (i : ι) :
    ¬ ∃ w : ι → ℝ, ∀ c' v', SchemeValues a c' v' → v' i = w i := by
  rintro ⟨w, hw⟩
  obtain ⟨c', v', h', hne⟩ := renormalised_value_not_determined h
  exact hne i (((hw c' v' h').trans (hw c v h).symm))

/-! ## §2 The relative reading is already determined -/

/-- The difference of two members is scheme-free: the counterterm cancels before the cutoff is
removed. -/
theorem tendsto_diff {a : ι → ℕ → ℝ} {c : ℕ → ℝ} {v : ι → ℝ} (h : SchemeValues a c v) (i j : ι) :
    Tendsto (fun n => a i n - a j n) atTop (𝓝 (v i - v j)) := by
  have := (h i).sub (h j)
  exact this.congr fun n => by ring

/-- **Scheme independence of the relative reading.**  Any two admissible schemes agree on all
differences of values, even though they may disagree on every value. -/
theorem difference_scheme_independent {a : ι → ℕ → ℝ} {c c' : ℕ → ℝ} {v v' : ι → ℝ}
    (h : SchemeValues a c v) (h' : SchemeValues a c' v') (i j : ι) :
    v i - v j = v' i - v' j :=
  tendsto_nhds_unique (tendsto_diff h i j) (tendsto_diff h' i j)

/-! ## §3 The closure needs no scheme, no limit, no cutoff removal -/

/-- **The closure reading of a regularised family**, relative to a reference member: the relation
between members, read at a single finite cutoff.  No counterterm and no limit occur in it. -/
def relAmp (a : ι → ℕ → ℝ) (i₀ : ι) (n : ℕ) : ι → ℝ := fun i => a i n - a i₀ n

/-- Under common divergence the relation between two members does not depend on the cutoff: the
divergence is not part of the relation. -/
theorem diff_cutoff_independent {a : ι → ℕ → ℝ} (hcd : CommonDivergence a) (i j : ι) (n m : ℕ) :
    a i n - a j n = a i m - a j m := by
  obtain ⟨f, g, hfg⟩ := hcd
  simp only [hfg]
  ring

/-- The closure reading is the same at every cutoff. -/
theorem relAmp_cutoff_independent {a : ι → ℕ → ℝ} (hcd : CommonDivergence a) (i₀ : ι) (n m : ℕ) :
    relAmp a i₀ n = relAmp a i₀ m :=
  funext fun i => diff_cutoff_independent hcd i i₀ n m

/-- **What renormalisation would have produced, the closure reads off directly.**  For a family with
common divergence, the difference of the values of *any* admissible scheme is already the difference
of the raw amplitudes at any single finite cutoff. -/
theorem rel_eq_scheme_diff {a : ι → ℕ → ℝ} (hcd : CommonDivergence a) {c : ℕ → ℝ} {v : ι → ℝ}
    (h : SchemeValues a c v) (i j : ι) (n : ℕ) : v i - v j = a i n - a j n := by
  refine tendsto_nhds_unique (tendsto_diff h i j) ?_
  have : (fun m => a i m - a j m) = fun _ : ℕ => a i n - a j n :=
    funext fun m => diff_cutoff_independent hcd i j m n
  rw [this]
  exact tendsto_const_nhds

/-- **The closure resolves the need for renormalisation.**  For a regularised family whose
divergence is common to its members:

1. the closure reading is defined at every finite cutoff, with no counterterm and no limit, and is
   independent of the cutoff;
2. it reproduces exactly what any admissible renormalisation scheme produces in the limit;
3. and the only content it does not carry — the absolute level — was never determined by the
   regularised data in the first place, so nothing is lost by not computing it. -/
theorem closure_resolves_renormalization {a : ι → ℕ → ℝ} (hcd : CommonDivergence a) (i₀ : ι) :
    (∀ n m, relAmp a i₀ n = relAmp a i₀ m) ∧
    (∀ (c : ℕ → ℝ) (v : ι → ℝ), SchemeValues a c v → ∀ i n, v i - v i₀ = relAmp a i₀ n i) ∧
    (∀ (c : ℕ → ℝ) (v : ι → ℝ), SchemeValues a c v →
      ∃ (c' : ℕ → ℝ) (v' : ι → ℝ), SchemeValues a c' v' ∧ ∀ i, v' i ≠ v i) := by
  refine ⟨relAmp_cutoff_independent hcd i₀, ?_, fun c v h => renormalised_value_not_determined h⟩
  intro c v h i n
  exact rel_eq_scheme_diff hcd h i i₀ n

/-! ## §4 Uniqueness of the closure — with no analysis, no limits and no choice

Everything in this section holds for value assignments in an arbitrary additive group.  No
completeness of the reals, no limit, and no choice principle is used: the resolution is a
translation between relative equality functions. -/

section Group

variable {G : Type*} [AddCommGroup G] {W : Type*}

/-- **The scheme freedom**, as an action on value assignments: a change of scheme shifts every value
by one and the same constant. -/
def ShiftInvariant (s : (ι → G) → W) : Prop := ∀ (v : ι → G) (k : G), s (fun i => v i + k) = s v

/-- **The closure reading on value assignments**: what the values say relative to a reference. -/
def relRead (i₀ : ι) (v : ι → G) : ι → G := fun i => v i - v i₀

/-- The closure reading is invariant under the scheme freedom. -/
theorem relRead_shiftInvariant (i₀ : ι) : ShiftInvariant (relRead (G := G) i₀) := by
  intro v k
  funext i
  show v i + k - (v i₀ + k) = v i - v i₀
  abel

/-- **The closure is the greatest determined content.**  A reading of the values is invariant under
change of scheme exactly when it is a translation of the closure reading — so the closure reading
carries every scheme-independent fact and nothing else. -/
theorem shiftInvariant_iff_refines (i₀ : ι) (s : (ι → G) → W) :
    ShiftInvariant s ↔ NRRF772.Refines (relRead (G := G) i₀) s := by
  constructor
  · intro hs
    refine ⟨s, fun v => ?_⟩
    have h : relRead (G := G) i₀ v = fun i => v i + (-(v i₀)) := by
      funext i; simp [relRead, sub_eq_add_neg]
    rw [h, hs v (-(v i₀))]
  · rintro ⟨t, ht⟩ v k
    have h : relRead (G := G) i₀ (fun i => v i + k) = relRead (G := G) i₀ v := by
      funext i; show v i + k - (v i₀ + k) = v i - v i₀; abel
    rw [← ht (fun i => v i + k), ← ht v, h]

/-- **Uniqueness of the closure.**  Any reading which is scheme-invariant and from which the closure
reading can itself be recovered is translationally equal to the closure reading: there is only one
closure, up to translation. -/
theorem closure_unique (i₀ : ι) (s : (ι → G) → W) (hs : ShiftInvariant s)
    (hback : NRRF772.Refines s (relRead (G := G) i₀)) :
    NRRF772.TransEq (relRead (G := G) i₀) s :=
  ⟨(shiftInvariant_iff_refines i₀ s).1 hs, hback⟩

/-- The closure reading does not determine the values themselves: the absolute level is exactly what
it drops. -/
theorem relRead_not_complete [Nontrivial G] (i₀ : ι) :
    ¬ Function.Injective (relRead (G := G) i₀) := by
  intro h
  obtain ⟨k, hk⟩ := exists_ne (0 : G)
  have : (fun _ : ι => (0 : G)) = fun _ : ι => k := by
    refine h ?_
    funext i
    simp [relRead]
  have := congrFun this i₀
  exact hk this.symm

/-- **Common divergence, with no real numbers in sight.**  The same hypothesis, for amplitudes
valued in an arbitrary additive group. -/
def CommonDivergenceG (a : ι → ℕ → G) : Prop :=
  ∃ (f : ℕ → G) (g : ι → G), ∀ i n, a i n = f n + g i

/-- **The cutoff-free relation, choice-free and analysis-free.**  Under common divergence the
relation between two members is the same at every cutoff — the statement of §3 needs neither the
real numbers, nor a limit, nor a choice principle. -/
theorem diffG_cutoff_independent {a : ι → ℕ → G} (hcd : CommonDivergenceG a) (i j : ι) (n m : ℕ) :
    a i n - a j n = a i m - a j m := by
  obtain ⟨f, g, hfg⟩ := hcd
  rw [hfg i n, hfg j n, hfg i m, hfg j m]
  abel

/-- The closure reading is idempotent: reading relations of relations adds nothing. -/
theorem relRead_idem (i₀ : ι) (v : ι → G) :
    relRead i₀ (relRead i₀ v) = relRead i₀ v := by
  funext i
  simp [relRead]

end Group

/-! ## §5 A concrete log-divergent family -/

/-- A log-divergent regularised family: a universal divergent part with a finite member-dependent
remainder. -/
noncomputable def logAmp (g : ι → ℝ) : ι → ℕ → ℝ := fun i n => Real.log (n + 1) + g i

theorem logAmp_commonDivergence (g : ι → ℝ) : CommonDivergence (logAmp g) :=
  ⟨fun n => Real.log (n + 1), g, fun _ _ => rfl⟩

theorem tendsto_log_succ_atTop :
    Tendsto (fun n : ℕ => Real.log (n + 1)) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)

/-- Every member of the family diverges: individually, none of these amplitudes has a value. -/
theorem logAmp_diverges (g : ι → ℝ) (i : ι) : Tendsto (logAmp g i) atTop atTop :=
  tendsto_atTop_add_const_right _ (g i) tendsto_log_succ_atTop

theorem logAmp_no_limit (g : ι → ℝ) (i : ι) : ¬ ∃ L : ℝ, Tendsto (logAmp g i) atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  exact not_tendsto_nhds_of_tendsto_atTop (logAmp_diverges g i) L hL

/-- Minimal subtraction is an admissible scheme for the family, with values the finite remainders. -/
theorem logAmp_scheme (g : ι → ℝ) :
    SchemeValues (logAmp g) (fun n => Real.log (n + 1)) g := by
  intro i
  have : (fun n : ℕ => logAmp g i n - Real.log (n + 1)) = fun _ : ℕ => g i := by
    funext n; simp [logAmp]
  rw [this]
  exact tendsto_const_nhds

/-- The closure reading of the divergent family is finite and available at cutoff `0`, with no
subtraction of infinities. -/
theorem logAmp_rel (g : ι → ℝ) (i₀ i : ι) (n : ℕ) : relAmp (logAmp g) i₀ n i = g i - g i₀ := by
  simp only [relAmp, logAmp]
  ring

/-- And it is exactly the relation between the renormalised values of the minimal subtraction
scheme — obtained without performing the subtraction. -/
theorem logAmp_closure_eq_renormalised (g : ι → ℝ) (i₀ i : ι) (n : ℕ) :
    g i - g i₀ = relAmp (logAmp g) i₀ n i :=
  (logAmp_rel g i₀ i n).symm

/-! ## §6 The closure as a natural form selection -/

open NRRF775 (Constraint Rigid sel sel_admissible determination_unique)

/-- **The relation the raw data determines.**  At the site `n` of an enumeration of members, the
admissible symbol is the relation of that member to the reference — nothing else is admitted. -/
def relRel (a : ι → ℕ → ℝ) (idx : ℕ → ι) (i₀ : ι) : Constraint ℝ :=
  fun n x => x = a (idx n) 0 - a i₀ 0

theorem relRel_rigid (a : ι → ℕ → ℝ) (idx : ℕ → ι) (i₀ : ι) : Rigid (relRel a idx i₀) :=
  fun n => ⟨a (idx n) 0 - a i₀ 0, rfl, fun _ hy => hy⟩

/-- The natural form selector returns the closure reading: the closure is *selected by the
relation*, not chosen by an agent, and no external condition enters. -/
theorem relSel_eq (a : ι → ℕ → ℝ) (idx : ℕ → ι) (i₀ : ι) (n : ℕ) :
    sel (relRel a idx i₀) (relRel_rigid a idx i₀) n = relAmp a i₀ 0 (idx n) :=
  sel_admissible (relRel a idx i₀) (relRel_rigid a idx i₀) n

/-- The determination is unique: any assignment admitted by the relation is the closure reading. -/
theorem relSel_unique (a : ι → ℕ → ℝ) (idx : ℕ → ι) (i₀ : ι) {t : ℕ → ℝ}
    (ht : ∀ n, relRel a idx i₀ n (t n)) (n : ℕ) : t n = relAmp a i₀ 0 (idx n) :=
  ht n

/-! ## §7 The collected answer -/

/-- **NRRF781.**  For a regularised family whose divergence is common to its members, and a
reference member:

* the classical repair is ambiguous — for every admissible scheme there is another admissible scheme
  disagreeing at every member, so the absolute renormalised value is not determined by the data;
* all schemes nevertheless agree on the relation between members;
* the closure reading of the raw data is cutoff-independent, needs no counterterm and no limit, and
  already equals that agreed relation;
* and (in the group-valued form, proved without any analysis) it is the unique greatest
  scheme-invariant reading. -/
theorem nrrf781_answer {a : ι → ℕ → ℝ} (hcd : CommonDivergence a) (i₀ : ι) :
    (∀ (c : ℕ → ℝ) (v : ι → ℝ), SchemeValues a c v →
        ∃ (c' : ℕ → ℝ) (v' : ι → ℝ), SchemeValues a c' v' ∧ ∀ i, v' i ≠ v i) ∧
    (∀ (c c' : ℕ → ℝ) (v v' : ι → ℝ), SchemeValues a c v → SchemeValues a c' v' →
        ∀ i j, v i - v j = v' i - v' j) ∧
    (∀ n m, relAmp a i₀ n = relAmp a i₀ m) ∧
    (∀ (c : ℕ → ℝ) (v : ι → ℝ), SchemeValues a c v → ∀ i n, v i - v i₀ = relAmp a i₀ n i) ∧
    ShiftInvariant (relRead (G := ℝ) i₀) ∧
    (∀ (W : Type) (s : (ι → ℝ) → W),
        ShiftInvariant s ↔ NRRF772.Refines (relRead (G := ℝ) i₀) s) := by
  obtain ⟨h1, h2, h3⟩ := closure_resolves_renormalization hcd i₀
  exact ⟨h3, fun c c' v v' h h' i j => difference_scheme_independent h h' i j, h1, h2,
    relRead_shiftInvariant i₀, fun W s => shiftInvariant_iff_refines i₀ s⟩

end NRRF781

/-! ## §8 Axiom audit -/

section Audit
open NRRF781

#print axioms NRRF781.renormalised_value_not_determined
#print axioms NRRF781.difference_scheme_independent
#print axioms NRRF781.diff_cutoff_independent
#print axioms NRRF781.relAmp_cutoff_independent
#print axioms NRRF781.rel_eq_scheme_diff
#print axioms NRRF781.closure_resolves_renormalization
#print axioms NRRF781.diffG_cutoff_independent
#print axioms NRRF781.relRead_shiftInvariant
#print axioms NRRF781.shiftInvariant_iff_refines
#print axioms NRRF781.closure_unique
#print axioms NRRF781.relRead_not_complete
#print axioms NRRF781.logAmp_no_limit
#print axioms NRRF781.nrrf781_answer

end Audit
