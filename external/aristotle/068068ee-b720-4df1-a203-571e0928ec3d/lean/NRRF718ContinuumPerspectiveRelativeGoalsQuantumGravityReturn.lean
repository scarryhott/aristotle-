import Mathlib

/-!
# NRRF718 — The continuum as perspective-relativity, quantum gravity as a relative return, and the relative diagonal as a unified topology

Three statements are instantiated here, and they turn out to be *one* structure.

**(A) "Behind a certain perspective, continuum is that short and long-term goals are relative to
perspective."**  A *perspective* is a positive horizon `h`; a *goal* is a time `t`.  The naive
reading calls a goal short-term or long-term as if that were a property of the goal.  It is not:
the only perspective-independent datum is the **ratio** `t / h`, and the short/long verdict is a
single cut of that ratio at `1` (`term_eq_ratio_le_one`, `term_respects_ratio`).  The continuum is
exactly what remains once the verdict is seen as relative:

* every positive ratio is realised by some perspective on a fixed goal
  (`ratio_image_eq_pos`), so no goal carries an absolute term (`term_not_absolute`);
* the classification is invariant under joint rescaling of goal and horizon
  (`ratio_rescale`, `term_rescale`) — there is no absolute unit, only relative position;
* the flip point is itself a perspective, not an external boundary (`boundary_is_a_perspective`),
  and it is unique (`boundary_unique`);
* the perspective-relative reading is the *complete* one: a reading of goal/perspective pairs
  factors through the continuum coordinate iff it respects the ratio (`factors_iff_respects`,
  instantiated by `reading_factors_iff_respects_ratio`), while the naive absolute reading
  "`t ≤ 1`" does not factor (`absolute_reading_not_factorable`).

**(B) "Quantum gravity is not an isolated particle but a return of GR relative to an origin of
QM."**  With constants `G, ħ, c`, the general-relativistic length of a mass is its Schwarzschild
radius `r_s(m) = 2Gm/c²` and its quantum length is the Compton length `λ(m) = ħ/(mc)`.  Then:

* `gr_qm_product` : `r_s(m) · λ(m) = 2 ħG/c³` — the joint return is **independent of the mass**,
  while neither factor is (`schwarzschild_not_constant`, `compton_not_constant`).  So the returned
  quantity belongs to no particle: `qg_not_isolated` proves the return is not supported at any
  single mass, and `qg_product_not_injective` that it cannot separate particles at all.
* `qgRatio_eq_relative_mass_sq` : `r_s(m)/λ(m) = (m / m_P)²` where `m_P = √(ħc/(2G))` is the mass at
  which the QM length equals the GR length (`schwarzschild_eq_compton_iff`, `qgRatio_planckMass`).
  Quantum gravity is therefore literally *GR returned relative to a QM origin*: a pure ratio to the
  origin `m_P`, and the origin moves with the constants (`planckMass_eq_one_iff`).
* the regime is relative in exactly the sense of (A): `qg_regime_is_perspective_term` identifies
  "quantum-dominant" with "short-term seen from the Planck perspective", and
  `regime_relative_to_constants` shows that any fixed particle is gravity-dominant for one choice
  of constants and quantum-dominant for another.  There is no absolute quantum-gravity particle.
  `qgRatio_eq_perspective_ratio_sq` is the bridge: the quantum-gravity coordinate is the square of
  the continuum coordinate of (A) taken at the Planck perspective.

**(C) "The relative diagonal of truth and translation is itself a form of unified definitional and
operational topology."**  For a return (truth) map `r : X → S` the **relative diagonal** is
`relDiag r = {(x,y) | r x = r y}` — the diagonal *relative to* what truth can see.  §5 shows this
relation is literally a topology, presented in two ways that coincide:

* *definitional*: `Saturated r U`, "U is a union of truth-fibres";
* *operational*: `OpInvariant r U`, "U is unchanged by every translation", a translation being a
  relabelling of occurrences that preserves truth.

`saturated_iff_opInvariant` unifies the two, `truthTopology` is the resulting topology, and
`inseparable_iff_truth_eq` shows the relative diagonal *is* the indistinguishability relation of
that topology (`relDiag_eq_inseparable`).  Continuity into a discrete presentation is exactly
respect for truth (`continuous_iff_respects`), so the universal property of §1 and the topology of
§5 are one statement (`relative_diagonal_is_unified_topology`).  §6 instantiates it: the
perspective verdict is continuous while the absolute reading is not
(`term_continuous`, `absolute_reading_not_continuous`), and in the quantum-gravity return every
two particles are topologically indistinguishable (`all_particles_inseparable_in_qg_return`).

`nrrf718_answer` collects the headline conjunction.
-/

namespace NRRF718

/-! ## §1  The derived Closure relations, in general form

The abstract skeleton: a return map `r : X → S`, its quotient, and the universal property that
makes "respecting the return" the same as "factoring through the returned identity". -/

section General

variable {X S Y : Type*}

/-- The Closure relation of a return map: two occurrences are Closure-equal when they return the
same identity. -/
def closureSetoid (r : X → S) : Setoid X := Setoid.ker r

/-- The Closure language `Ω_𝒞 = X / ∼_𝒞`. -/
abbrev Omega (r : X → S) : Type _ := Quotient (closureSetoid r)

/-- The Closure quotient map. -/
def cq (r : X → S) : X → Omega r := Quotient.mk _

/-- A reading `f : X → Y` **respects the return** when it cannot separate two occurrences with the
same returned identity. -/
def Respects (r : X → S) (f : X → Y) : Prop := ∀ x y, r x = r y → f x = f y

theorem cq_eq_iff (r : X → S) (x y : X) : cq r x = cq r y ↔ r x = r y := by
  simp [cq, Quotient.eq, closureSetoid, Setoid.ker, Function.onFun]

/-- **Universal property of the Closure language.**  A reading factors uniquely through the
returned identity exactly when it respects it. -/
theorem factors_iff_respects (r : X → S) (f : X → Y) :
    (∃! g : Omega r → Y, f = g ∘ cq r) ↔ Respects r f := by
  constructor
  · rintro ⟨g, hg, -⟩ x y hxy
    have h := (cq_eq_iff r x y).2 hxy
    simp [hg, h]
  · intro h
    refine ⟨Quotient.lift f h, rfl, ?_⟩
    intro g hg
    funext w
    induction w using Quotient.ind with
    | _ x => simpa [cq] using (congrFun hg x).symm

/-- A reading that separates two occurrences with the same returned identity cannot factor. -/
theorem not_factorable_of_not_respects (r : X → S) (f : X → Y) (h : ¬ Respects r f) :
    ¬ ∃ g : Omega r → Y, f = g ∘ cq r := by
  rintro ⟨g, hg⟩
  exact h (fun x y hxy => by simp [hg, (cq_eq_iff r x y).2 hxy])

/-- The return induced on the Closure language. -/
def rBar (r : X → S) : Omega r → S := Quotient.lift r (fun _ _ h => h)

theorem rBar_cq (r : X → S) (x : X) : rBar r (cq r x) = r x := rfl

theorem rBar_injective (r : X → S) : Function.Injective (rBar r) := by
  intro a b hab
  induction a using Quotient.ind
  induction b using Quotient.ind
  exact (cq_eq_iff r _ _).2 hab

/-- **Closure of Closure is stationary**: on the Closure language the return is literal equality. -/
theorem second_return_is_equality (r : X → S) (a b : Omega r) :
    rBar r a = rBar r b ↔ a = b :=
  ⟨fun h => rBar_injective r h, fun h => by rw [h]⟩

end General

/-! ## §2  Perspectives, goals and the short/long verdict -/

/-- A **perspective** is a positive horizon: the time-scale against which goals are read. -/
structure Perspective where
  horizon : ℝ
  pos : 0 < horizon

/-- The verdict a perspective can return about a goal. -/
inductive Term
  | short | long
  deriving DecidableEq, Repr

/-- The **continuum coordinate**: the goal's time measured in units of the perspective's horizon.
This is the only perspective-independent datum. -/
noncomputable def ratio (p : Perspective) (t : ℝ) : ℝ := t / p.horizon

/-- The naive verdict: a goal is short-term when it fits inside the horizon. -/
noncomputable def term (p : Perspective) (t : ℝ) : Term :=
  if t ≤ p.horizon then Term.short else Term.long

/-- The verdict is a single cut of the continuum coordinate at `1`. -/
theorem term_eq_ratio_le_one (p : Perspective) (t : ℝ) :
    term p t = Term.short ↔ ratio p t ≤ 1 := by
  unfold term ratio
  rw [div_le_one p.pos]
  split <;> simp_all

/-- Two occurrences with the same continuum coordinate receive the same verdict: the verdict is a
function of the ratio, not of the goal. -/
theorem term_of_ratio_eq {p q : Perspective} {t s : ℝ} (h : ratio p t = ratio q s) :
    term p t = term q s := by
  have h1 : (term p t = Term.short) ↔ (term q s = Term.short) := by
    rw [term_eq_ratio_le_one, term_eq_ratio_le_one, h]
  cases hp : term p t <;> cases hq : term q s <;> simp_all

/-- Packaged as a Closure statement: the verdict respects the continuum return. -/
theorem term_respects_ratio :
    Respects (fun x : Perspective × ℝ => ratio x.1 x.2) (fun x : Perspective × ℝ => term x.1 x.2) :=
  fun _ _ h => term_of_ratio_eq h

/-- Every positive continuum coordinate is realised by some perspective on a fixed positive goal:
the family of perspectives sweeps the whole positive continuum. -/
theorem ratio_image_eq_pos {t : ℝ} (ht : 0 < t) :
    Set.range (fun p : Perspective => ratio p t) = Set.Ioi (0 : ℝ) := by
  ext r
  constructor
  · rintro ⟨p, rfl⟩
    exact div_pos ht p.pos
  · intro hr
    have hr' : r ≠ 0 := ne_of_gt hr
    have ht' : t ≠ 0 := ne_of_gt ht
    refine ⟨⟨t / r, div_pos ht hr⟩, ?_⟩
    show t / (t / r) = r
    field_simp

/-- **Short and long term are relative to perspective.**  No goal carries an absolute verdict:
for every goal there is a perspective calling it short-term and another calling it long-term. -/
theorem term_not_absolute {t : ℝ} (ht : 0 < t) :
    ∃ p q : Perspective, term p t = Term.short ∧ term q t = Term.long := by
  refine ⟨⟨t, ht⟩, ⟨t / 2, by positivity⟩, ?_, ?_⟩
  · simp [term]
  · have : ¬ t ≤ t / 2 := by linarith
    simp [term, this]

/-- The continuum coordinate is invariant under joint rescaling of goal and horizon: there is no
absolute unit, only relative position. -/
theorem ratio_rescale (p : Perspective) (t : ℝ) {lam : ℝ} (hl : 0 < lam) :
    ratio ⟨lam * p.horizon, mul_pos hl p.pos⟩ (lam * t) = ratio p t := by
  have hl' : lam ≠ 0 := ne_of_gt hl
  have hp : p.horizon ≠ 0 := ne_of_gt p.pos
  show (lam * t) / (lam * p.horizon) = t / p.horizon
  field_simp

/-- Consequently the verdict, too, is scale-free. -/
theorem term_rescale (p : Perspective) (t : ℝ) {lam : ℝ} (hl : 0 < lam) :
    term ⟨lam * p.horizon, mul_pos hl p.pos⟩ (lam * t) = term p t :=
  term_of_ratio_eq (ratio_rescale p t hl)

/-- **The boundary is itself a perspective.**  The place where the verdict flips is not imposed
from outside the continuum: it is the perspective whose horizon is the goal itself. -/
theorem boundary_is_a_perspective {t : ℝ} (ht : 0 < t) :
    ratio ⟨t, ht⟩ t = 1 ∧
      (∀ p : Perspective, t < p.horizon → term p t = Term.short) ∧
      (∀ p : Perspective, p.horizon < t → term p t = Term.long) := by
  refine ⟨?_, fun p hp => ?_, fun p hp => ?_⟩
  · show t / t = 1
    exact div_self (ne_of_gt ht)
  · simp [term, le_of_lt hp]
  · have : ¬ t ≤ p.horizon := not_le.2 hp
    simp [term, this]

/-- The flip point is unique: exactly one horizon puts the goal on the boundary. -/
theorem boundary_unique {t : ℝ} (ht : 0 < t) :
    ∃! h : ℝ, 0 < h ∧ t / h = 1 := by
  refine ⟨t, ⟨ht, by field_simp⟩, ?_⟩
  rintro h ⟨hh, hth⟩
  exact ((div_eq_one_iff_eq (ne_of_gt hh)).1 hth).symm

/-- The perspective-relative reading is complete: a reading of goal/perspective pairs factors
through the continuum coordinate exactly when it respects that coordinate. -/
theorem reading_factors_iff_respects_ratio {Y : Type} (f : Perspective × ℝ → Y) :
    (∃! g : Omega (fun x : Perspective × ℝ => ratio x.1 x.2) → Y,
        f = g ∘ cq (fun x : Perspective × ℝ => ratio x.1 x.2)) ↔
      Respects (fun x : Perspective × ℝ => ratio x.1 x.2) f :=
  factors_iff_respects _ f

/-- The **absolute** reading calls a goal short-term by its raw duration and ignores the
perspective.  It does not respect the continuum coordinate. -/
theorem absolute_reading_not_respects :
    ¬ Respects (fun x : Perspective × ℝ => ratio x.1 x.2)
        (fun x : Perspective × ℝ => decide (x.2 ≤ 1)) := by
  intro h
  have hr : ratio ⟨1, one_pos⟩ 1 = ratio ⟨2, two_pos⟩ 2 := by
    show (1:ℝ) / 1 = 2 / 2
    norm_num
  have hcontra := h (⟨1, one_pos⟩, 1) (⟨2, two_pos⟩, 2) hr
  simp at hcontra

/-- Hence the absolute reading does not factor through the continuum: it separates occurrences
with the same relative position. -/
theorem absolute_reading_not_factorable :
    ¬ ∃ g : Omega (fun x : Perspective × ℝ => ratio x.1 x.2) → Bool,
        (fun x : Perspective × ℝ => decide (x.2 ≤ 1)) =
          g ∘ cq (fun x : Perspective × ℝ => ratio x.1 x.2) :=
  not_factorable_of_not_respects _ _ absolute_reading_not_respects

/-! ## §3  Quantum gravity as a return of GR relative to an origin of QM -/

/-- The constants fixing a physical frame. -/
structure Constants where
  G : ℝ
  hbar : ℝ
  c : ℝ
  hG : 0 < G
  hh : 0 < hbar
  hc : 0 < c

variable (K : Constants)

/-- The **general-relativistic length** of a mass: its Schwarzschild radius `2Gm/c²`. -/
noncomputable def schwarzschild (K : Constants) (m : ℝ) : ℝ := 2 * K.G * m / K.c ^ 2

/-- The **quantum length** of a mass: its Compton wavelength `ħ/(mc)`. -/
noncomputable def compton (K : Constants) (m : ℝ) : ℝ := K.hbar / (m * K.c)

/-- The squared Planck length `ħG/c³`. -/
noncomputable def planckLengthSq (K : Constants) : ℝ := K.hbar * K.G / K.c ^ 3

theorem planckLengthSq_pos : 0 < planckLengthSq K := by
  have := K.hh; have := K.hG; have := K.hc
  unfold planckLengthSq; positivity

theorem compton_pos {m : ℝ} (hm : 0 < m) : 0 < compton K m := by
  have := K.hh; have := K.hc
  unfold compton; positivity

/-- **The joint return is mass-independent.**  `r_s(m) · λ(m) = 2 ħG/c³` for every particle: the
quantum-gravitational scale is not attached to any one mass. -/
theorem gr_qm_product {m : ℝ} (hm : m ≠ 0) :
    schwarzschild K m * compton K m = 2 * planckLengthSq K := by
  have hc := ne_of_gt K.hc
  unfold schwarzschild compton planckLengthSq
  field_simp

/-- The GR factor alone *does* depend on the particle. -/
theorem schwarzschild_not_constant : ∃ m m' : ℝ, 0 < m ∧ 0 < m' ∧
    schwarzschild K m ≠ schwarzschild K m' := by
  refine ⟨1, 2, one_pos, two_pos, ?_⟩
  have hG := K.hG
  have hc : (0:ℝ) < K.c ^ 2 := by have := K.hc; positivity
  unfold schwarzschild
  intro h
  rw [div_eq_div_iff (ne_of_gt hc) (ne_of_gt hc)] at h
  nlinarith

/-- The QM factor alone *does* depend on the particle. -/
theorem compton_not_constant : ∃ m m' : ℝ, 0 < m ∧ 0 < m' ∧ compton K m ≠ compton K m' := by
  refine ⟨1, 2, one_pos, two_pos, ?_⟩
  have hh := K.hh
  have hc := K.hc
  unfold compton
  intro h
  rw [div_eq_div_iff (by positivity) (by positivity)] at h
  nlinarith

/-- A quantity is **isolated at a particle** when it is supported at exactly one mass. -/
def IsolatedAt (F : ℝ → ℝ) : Prop := ∃ m₀ : ℝ, 0 < m₀ ∧ ∀ m, 0 < m → (F m ≠ 0 ↔ m = m₀)

/-- **Quantum gravity is not an isolated particle.**  The joint GR–QM return is a nonzero constant
across all masses, so it is supported at no single particle. -/
theorem qg_not_isolated : ¬ IsolatedAt (fun m => schwarzschild K m * compton K m) := by
  rintro ⟨m₀, hm₀, h⟩
  have hpos : 0 < m₀ + 1 := by linarith
  have hne : schwarzschild K (m₀ + 1) * compton K (m₀ + 1) ≠ 0 := by
    rw [gr_qm_product K (ne_of_gt hpos)]
    have := planckLengthSq_pos K
    positivity
  have := (h (m₀ + 1) hpos).1 hne
  linarith

/-- Nor can the joint return distinguish particles at all: it is constant on the positive masses. -/
theorem qg_product_not_injective {m m' : ℝ} (hm : 0 < m) (hm' : 0 < m') :
    schwarzschild K m * compton K m = schwarzschild K m' * compton K m' := by
  rw [gr_qm_product K (ne_of_gt hm), gr_qm_product K (ne_of_gt hm')]

/-- The **quantum-gravity coordinate**: the GR length returned relative to the QM length. -/
noncomputable def qgRatio (K : Constants) (m : ℝ) : ℝ := schwarzschild K m / compton K m

/-- The **origin of QM**: the mass at which the quantum length equals the gravitational length. -/
noncomputable def planckMass (K : Constants) : ℝ := Real.sqrt (K.hbar * K.c / (2 * K.G))

theorem planckMass_pos : 0 < planckMass K := by
  have := K.hh; have := K.hG; have := K.hc
  unfold planckMass
  exact Real.sqrt_pos.2 (by positivity)

theorem planckMass_sq : planckMass K ^ 2 = K.hbar * K.c / (2 * K.G) := by
  have := K.hh; have := K.hG; have := K.hc
  unfold planckMass
  exact Real.sq_sqrt (by positivity)

theorem qgRatio_eq {m : ℝ} (hm : 0 < m) : qgRatio K m = 2 * K.G * m ^ 2 / (K.hbar * K.c) := by
  have hc := ne_of_gt K.hc
  have hh := ne_of_gt K.hh
  have hm' := ne_of_gt hm
  unfold qgRatio schwarzschild compton
  rw [div_div_div_eq]
  field_simp

/-- **Quantum gravity is a return of GR relative to an origin of QM.**  The coordinate is exactly
the squared mass ratio to the Planck mass: nothing absolute, only a relative position. -/
theorem qgRatio_eq_relative_mass_sq {m : ℝ} (hm : 0 < m) :
    qgRatio K m = (m / planckMass K) ^ 2 := by
  have hP := planckMass_pos K
  have hh := ne_of_gt K.hh
  have hc := ne_of_gt K.hc
  have hG := ne_of_gt K.hG
  rw [qgRatio_eq K hm, div_pow, planckMass_sq]
  field_simp

/-- At the origin the return is `1`. -/
theorem qgRatio_planckMass : qgRatio K (planckMass K) = 1 := by
  rw [qgRatio_eq_relative_mass_sq K (planckMass_pos K), div_self (ne_of_gt (planckMass_pos K))]
  norm_num

/-- The Planck mass is the *unique* particle whose gravitational length equals its quantum length —
so the crossing is a returned identity, not a particle picked out in advance. -/
theorem schwarzschild_eq_compton_iff {m : ℝ} (hm : 0 < m) :
    schwarzschild K m = compton K m ↔ m = planckMass K := by
  have hP := planckMass_pos K
  have hcpos := compton_pos K hm
  constructor
  · intro h
    have hr : qgRatio K m = 1 := by
      unfold qgRatio; rw [h, div_self (ne_of_gt hcpos)]
    rw [qgRatio_eq_relative_mass_sq K hm] at hr
    have hpos : 0 < m / planckMass K := div_pos hm hP
    have h1 : m / planckMass K = 1 := by nlinarith
    field_simp at h1
    exact h1
  · rintro rfl
    have hr : qgRatio K (planckMass K) = 1 := qgRatio_planckMass K
    have hcpos' := compton_pos K hP
    unfold qgRatio at hr
    rw [div_eq_one_iff_eq (ne_of_gt hcpos')] at hr
    exact hr

/-- The coordinate is strictly increasing in the mass: the quantum-gravity return is a faithful
continuum coordinate on particles, not a discrete label. -/
theorem qgRatio_strictMonoOn : StrictMonoOn (qgRatio K) (Set.Ioi (0:ℝ)) := by
  intro a ha b hb hab
  have ha' : 0 < a := ha
  have hb' : 0 < b := hb
  rw [qgRatio_eq K ha', qgRatio_eq K hb']
  have hpos : 0 < K.hbar * K.c := by have := K.hh; have := K.hc; positivity
  have hG := K.hG
  rw [div_lt_div_iff₀ hpos hpos]
  have hsq : a ^ 2 < b ^ 2 := by nlinarith
  have hc2 : 0 < 2 * K.G * (K.hbar * K.c) := by positivity
  nlinarith [mul_pos hc2 (sub_pos.2 hsq)]

/-- The origin of QM moves with the constants: it is fixed by `ħ`, `c` and `G`, not by any
particle. -/
theorem planckMass_eq_one_iff : planckMass K = 1 ↔ K.hbar * K.c = 2 * K.G := by
  have hP := planckMass_pos K
  have hG := K.hG
  constructor
  · intro h
    have hsq := planckMass_sq K
    rw [h] at hsq
    field_simp at hsq
    linarith
  · intro h
    have hsq : planckMass K ^ 2 = 1 := by
      rw [planckMass_sq K, h]
      field_simp
    nlinarith

/-! ## §4  The bridge: the quantum-gravity regime is a perspective cut -/

/-- The perspective whose horizon is the QM origin. -/
noncomputable def planckPerspective (K : Constants) : Perspective :=
  ⟨planckMass K, planckMass_pos K⟩

/-- **The two pictures are one.**  The quantum-gravity coordinate is the square of the continuum
coordinate of §2 taken at the Planck perspective. -/
theorem qgRatio_eq_perspective_ratio_sq {m : ℝ} (hm : 0 < m) :
    qgRatio K m = (ratio (planckPerspective K) m) ^ 2 :=
  qgRatio_eq_relative_mass_sq K hm

/-- The quantum-dominant regime is exactly the cut `r_s/λ ≤ 1` of the quantum-gravity
coordinate. -/
theorem regime_iff_qgRatio_le_one {m : ℝ} (hm : 0 < m) :
    schwarzschild K m ≤ compton K m ↔ qgRatio K m ≤ 1 := by
  have hcpos := compton_pos K hm
  unfold qgRatio
  rw [div_le_one hcpos]

/-- "Quantum-dominant" is literally "short-term, seen from the Planck perspective". -/
theorem qg_regime_is_perspective_term {m : ℝ} (hm : 0 < m) :
    term (planckPerspective K) m = Term.short ↔ schwarzschild K m ≤ compton K m := by
  have hP := planckMass_pos K
  have hpos : 0 < m / planckMass K := div_pos hm hP
  rw [term_eq_ratio_le_one, regime_iff_qgRatio_le_one K hm,
    qgRatio_eq_perspective_ratio_sq K hm]
  have hratio : ratio (planckPerspective K) m = m / planckMass K := rfl
  rw [hratio]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **The regime is relative, not intrinsic.**  Any fixed particle is quantum-dominant in one
frame and gravity-dominant in another: there is no isolated quantum-gravity particle. -/
theorem regime_relative_to_constants {m : ℝ} (hm : 0 < m) :
    ∃ K K' : Constants,
      schwarzschild K m < compton K m ∧ compton K' m < schwarzschild K' m := by
  have hm2 : 0 < m ^ 2 := by positivity
  refine ⟨⟨1 / (4 * m ^ 2), 1, 1, by positivity, one_pos, one_pos⟩,
          ⟨1 / m ^ 2, 1, 1, by positivity, one_pos, one_pos⟩, ?_, ?_⟩
  · unfold schwarzschild compton
    rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
    have hkey : 2 * (1 / (4 * m ^ 2)) * m * (m * 1) = 1 / 2 := by field_simp; ring
    rw [hkey]
    norm_num
  · unfold schwarzschild compton
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    have hkey : 2 * (1 / m ^ 2) * m * (m * 1) = 2 := by field_simp
    rw [hkey]
    norm_num

/-! ## §5  The relative diagonal of truth and translation as one topology

The **relative diagonal** of a truth map `r : X → S` is the set of pairs it cannot separate.  Read
*definitionally* it produces the saturated sets (unions of truth-fibres); read *operationally* it
produces the sets invariant under every truth-preserving translation.  The two readings coincide,
they form a topology, and the relative diagonal is precisely the indistinguishability relation of
that topology. -/

section Diagonal

variable {X S Y : Type*}

/-- The **relative diagonal of truth**: the pairs of occurrences the return cannot separate. -/
def relDiag (r : X → S) : Set (X × X) := {p | r p.1 = r p.2}

theorem relDiag_refl (r : X → S) (x : X) : (x, x) ∈ relDiag r := rfl

/-- The *definitional* reading: a set is a union of truth-fibres. -/
def Saturated (r : X → S) (U : Set X) : Prop := ∀ x y, r x = r y → (x ∈ U ↔ y ∈ U)

/-- A **translation** is a relabelling of the occurrences that preserves truth. -/
def Translation (r : X → S) : Type _ := {e : Equiv.Perm X // ∀ x, r (e x) = r x}

/-- The *operational* reading: a set is unchanged by every translation. -/
def OpInvariant (r : X → S) (U : Set X) : Prop := ∀ e : Translation r, ∀ x, x ∈ U ↔ e.1 x ∈ U

/-- **Definitional = operational.**  Being a union of truth-fibres is the same as being invariant
under every truth-preserving translation. -/
theorem saturated_iff_opInvariant (r : X → S) (U : Set X) : Saturated r U ↔ OpInvariant r U := by
  classical
  constructor
  · intro h e x
    exact h x (e.1 x) (e.2 x).symm
  · intro h x y hxy
    have he : ∀ z, r (Equiv.swap x y z) = r z := by
      intro z
      rcases eq_or_ne z x with rfl | hzx
      · simp [Equiv.swap_apply_left, hxy]
      · rcases eq_or_ne z y with rfl | hzy
        · simp [Equiv.swap_apply_right, hxy]
        · simp [Equiv.swap_apply_of_ne_of_ne hzx hzy]
    have := h ⟨Equiv.swap x y, he⟩ x
    simpa [Equiv.swap_apply_left] using this

/-- **The relative diagonal is a topology.**  Its open sets are the saturated — equivalently, the
translation-invariant — sets. -/
def truthTopology (r : X → S) : TopologicalSpace X where
  IsOpen U := Saturated r U
  isOpen_univ := by intro x y _; simp
  isOpen_inter := by
    intro s t hs ht x y hxy
    simp [Set.mem_inter_iff, hs x y hxy, ht x y hxy]
  isOpen_sUnion := by
    intro C hC x y hxy
    constructor
    · rintro ⟨u, hu, hxu⟩; exact ⟨u, hu, (hC u hu x y hxy).1 hxu⟩
    · rintro ⟨u, hu, hyu⟩; exact ⟨u, hu, (hC u hu x y hxy).2 hyu⟩

theorem truth_isOpen_iff (r : X → S) (U : Set X) :
    @IsOpen X (truthTopology r) U ↔ Saturated r U := Iff.rfl

/-- Truth-fibres are open. -/
theorem fiber_isOpen (r : X → S) (s : S) : @IsOpen X (truthTopology r) {x | r x = s} := by
  intro x y hxy; simp [Set.mem_setOf_eq, hxy]

/-- Truth-fibres are closed: the topology of the relative diagonal is a partition topology. -/
theorem fiber_isClosed (r : X → S) (s : S) : @IsClosed X (truthTopology r) {x | r x = s} := by
  rw [← @isOpen_compl_iff X {x | r x = s} (truthTopology r)]
  intro x y hxy
  simp [Set.mem_compl_iff, Set.mem_setOf_eq, hxy]

/-- **The relative diagonal is the indistinguishability relation of its own topology.** -/
theorem inseparable_iff_truth_eq (r : X → S) (x y : X) :
    @Inseparable X (truthTopology r) x y ↔ r x = r y := by
  constructor
  · intro h
    have := (@inseparable_iff_forall_isOpen X (truthTopology r) x y).1 h {z | r z = r x}
      (fiber_isOpen r (r x))
    simpa [eq_comm] using this.1 rfl
  · intro h
    rw [@inseparable_iff_forall_isOpen X (truthTopology r)]
    intro U hU
    exact hU x y h

theorem relDiag_eq_inseparable (r : X → S) :
    relDiag r = {p : X × X | @Inseparable X (truthTopology r) p.1 p.2} := by
  ext p
  exact (inseparable_iff_truth_eq r p.1 p.2).symm

/-- **Definitional factoring is operational continuity.**  A reading into a discrete presentation
is continuous for the topology of the relative diagonal exactly when it respects truth — the
universal property of §1 and the topology of §5 are the same statement. -/
theorem continuous_iff_respects (r : X → S) (f : X → Y) :
    @Continuous X Y (truthTopology r) ⊥ f ↔ Respects r f := by
  constructor
  · intro hc x y hxy
    have hopen : @IsOpen Y ⊥ {f x} := trivial
    have hsat := (@continuous_def X Y (truthTopology r) ⊥ f).1 hc _ hopen
    exact ((hsat x y hxy).1 rfl).symm
  · intro h
    rw [@continuous_def X Y (truthTopology r) ⊥ f]
    intro V _ x y hxy
    simp [Set.mem_preimage, h x y hxy]

/-- **The relative diagonal of truth and translation is a unified definitional and operational
topology**: it is the indistinguishability relation of a topology whose opens admit both the
definitional description (unions of truth-fibres) and the operational one (invariance under all
translations), and whose continuous discrete readings are exactly the truth-respecting ones. -/
theorem relative_diagonal_is_unified_topology (r : X → S) :
    relDiag r = {p : X × X | @Inseparable X (truthTopology r) p.1 p.2} ∧
      (∀ U : Set X, (@IsOpen X (truthTopology r) U ↔ Saturated r U) ∧
        (Saturated r U ↔ OpInvariant r U)) ∧
      (∀ f : X → Y, @Continuous X Y (truthTopology r) ⊥ f ↔ Respects r f) :=
  ⟨relDiag_eq_inseparable r,
   fun U => ⟨truth_isOpen_iff r U, saturated_iff_opInvariant r U⟩,
   fun f => continuous_iff_respects r f⟩

end Diagonal

/-! ## §6  The two instantiations inside the diagonal topology -/

/-- The topology of the continuum: occurrences are goal/perspective pairs, truth is the ratio. -/
noncomputable def continuumTopology : TopologicalSpace (Perspective × ℝ) :=
  truthTopology (fun x : Perspective × ℝ => ratio x.1 x.2)

/-- The perspective-relative verdict is continuous for the diagonal topology. -/
theorem term_continuous :
    @Continuous (Perspective × ℝ) Term continuumTopology ⊥ (fun x => term x.1 x.2) :=
  (continuous_iff_respects _ _).2 term_respects_ratio

/-- The absolute reading is *not* continuous: reading "short-term" off the raw duration breaks the
translation-invariance of the continuum. -/
theorem absolute_reading_not_continuous :
    ¬ @Continuous (Perspective × ℝ) Bool continuumTopology ⊥ (fun x => decide (x.2 ≤ 1)) := by
  intro h
  exact absolute_reading_not_respects ((continuous_iff_respects _ _).1 h)

/-- Particles, as the occurrences of the quantum-gravity return. -/
def PosMass : Type := {m : ℝ // 0 < m}

/-- The topology of the quantum-gravity return `r_s · λ`. -/
noncomputable def qgTopology (K : Constants) : TopologicalSpace PosMass :=
  truthTopology (fun m : PosMass => schwarzschild K m.1 * compton K m.1)

/-- **Quantum gravity is not an isolated particle**, topologically: in the quantum-gravity return
every two particles are indistinguishable, so no particle is separated out by it. -/
theorem all_particles_inseparable_in_qg_return (m m' : PosMass) :
    @Inseparable PosMass (qgTopology K) m m' :=
  (inseparable_iff_truth_eq _ m m').2 (qg_product_not_injective K m.2 m'.2)

/-- The quantum-dominant/gravity-dominant reading *is* continuous for the finer topology of the
relative coordinate `r_s/λ`: the regime is a function of the relative return, not of the
particle. -/
theorem regime_continuous :
    @Continuous PosMass Bool (truthTopology (fun m : PosMass => qgRatio K m.1)) ⊥
      (fun m : PosMass => decide (schwarzschild K m.1 ≤ compton K m.1)) := by
  refine (continuous_iff_respects _ _).2 ?_
  intro x y hxy
  have hx := (regime_iff_qgRatio_le_one K x.2)
  have hy := (regime_iff_qgRatio_le_one K y.2)
  have hxy' : qgRatio K x.1 = qgRatio K y.1 := hxy
  have hiff : (schwarzschild K x.1 ≤ compton K x.1) ↔ (schwarzschild K y.1 ≤ compton K y.1) := by
    rw [hx, hy, hxy']
  simp [hiff]

/-! ## §7  Headline -/

/-- **NRRF718.**

1. the short/long verdict is a single cut of the continuum coordinate, and is invariant under
   joint rescaling — only relative position exists;
2. no goal carries an absolute verdict: for every goal one perspective calls it short-term and
   another calls it long-term;
3. the naive absolute reading does not factor through the continuum, whereas the relative one
   does;
4. the GR–QM joint return `r_s · λ = 2ħG/c³` is mass-independent although neither factor is, so
   quantum gravity is supported at no isolated particle;
5. the quantum-gravity coordinate is exactly the squared ratio of the mass to the QM origin `m_P`,
   i.e. GR returned relative to an origin of QM;
6. the quantum-dominant regime is the short-term verdict of the Planck perspective, and it is
   frame-relative;
7. the relative diagonal of truth and translation is the indistinguishability relation of one
   topology whose opens are simultaneously the definitional (fibre-saturated) and the operational
   (translation-invariant) sets, and whose continuous discrete readings are exactly the
   truth-respecting ones. -/
theorem nrrf718_answer :
    (∀ (p : Perspective) (t : ℝ), term p t = Term.short ↔ ratio p t ≤ 1) ∧
    (∀ (p : Perspective) (t lam : ℝ) (hl : 0 < lam),
      term ⟨lam * p.horizon, mul_pos hl p.pos⟩ (lam * t) = term p t) ∧
    (∀ t : ℝ, 0 < t → ∃ p q : Perspective, term p t = Term.short ∧ term q t = Term.long) ∧
    (¬ ∃ g : Omega (fun x : Perspective × ℝ => ratio x.1 x.2) → Bool,
        (fun x : Perspective × ℝ => decide (x.2 ≤ 1)) =
          g ∘ cq (fun x : Perspective × ℝ => ratio x.1 x.2)) ∧
    (∀ (K : Constants) (m : ℝ), m ≠ 0 →
      schwarzschild K m * compton K m = 2 * planckLengthSq K) ∧
    (∀ K : Constants, ¬ IsolatedAt (fun m => schwarzschild K m * compton K m)) ∧
    (∀ (K : Constants) (m : ℝ), 0 < m → qgRatio K m = (m / planckMass K) ^ 2) ∧
    (∀ (K : Constants) (m : ℝ), 0 < m →
      (term (planckPerspective K) m = Term.short ↔ schwarzschild K m ≤ compton K m)) ∧
    (∀ m : ℝ, 0 < m → ∃ K K' : Constants,
      schwarzschild K m < compton K m ∧ compton K' m < schwarzschild K' m) ∧
    (∀ (X S : Type) (r : X → S),
      relDiag r = {p : X × X | @Inseparable X (truthTopology r) p.1 p.2} ∧
      (∀ U : Set X, (@IsOpen X (truthTopology r) U ↔ Saturated r U) ∧
        (Saturated r U ↔ OpInvariant r U)) ∧
      (∀ f : X → Bool, @Continuous X Bool (truthTopology r) ⊥ f ↔ Respects r f)) :=
  ⟨term_eq_ratio_le_one,
   fun p t _ hl => term_rescale p t hl,
   fun _ ht => term_not_absolute ht,
   absolute_reading_not_factorable,
   fun K _ hm => gr_qm_product K hm,
   qg_not_isolated,
   fun K _ hm => qgRatio_eq_relative_mass_sq K hm,
   fun K _ hm => qg_regime_is_perspective_term K hm,
   fun _ hm => regime_relative_to_constants hm,
   fun _ _ r => relative_diagonal_is_unified_topology r⟩

end NRRF718
