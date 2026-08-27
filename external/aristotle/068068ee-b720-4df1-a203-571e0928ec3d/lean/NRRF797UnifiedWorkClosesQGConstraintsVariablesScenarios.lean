import Mathlib
import NRRF794ReunifiedTranslationalCompletenessQuantumGravity
import NRRF796SelfLimitInversionEqualityOneHairClosureBall

/-!
# NRRF797 — How the unified work closes specific constraints, variables and scenarios of quantum gravity

The instruction formalised here is the user's:

> Show how the existing unified work closes specific constraints, variables and scenarios of QG.

Nothing new is assumed.  Everything below is stated in the already-built objects: the local
relation `LocalRel` of `NRRF683` with its scale reading `divg`, hair reading `hair = curl / 2` and
neutral (shear) sector `shearPart`; the seam field of `NRRF791`; the loop-sensor state space,
`gravRel` and `phase` of `NRRF786`/`NRRF794`; and the inversion `relInv`, the self limit, the
commutator `entangle` and the `Demon` of `NRRF796`.  The point of the module is to name the
*specific* items — one variable set, three constraints, seven scenarios — and to show, one theorem
each, that the existing unified machinery already closes them.

## §1  The variables

`qgVars A = (divg A, hair A, shearPart A)`: the scale variable, the hair variable and the neutral
variable.

* `qgVars_injective` — the three variables **fix the relation**: there is no hidden fourth datum.
* `qgRel`, `qgVars_qgRel`, `qgVars_surjective` — and they are **free**: every admissible triple
  (arbitrary scale, arbitrary hair, any neutral relation) is realised, so the variable set is
  neither redundant nor over-constrained.  `qgVars_independent` records that each of the three can
  be moved with the other two held fixed.
* `qgVars_relInv` — the variables transform under the one inversion by `(−, +, −)`.

## §2  The constraints

The three constraint functions are the three readings themselves:
`hamiltonianConstraint = divg` (scale/source), `gaussConstraint = hair` (rotation),
`diffeoConstraint = shearPart` (neutral).  All are linear (`constraints_linear`).

* Solution sectors, one constraint at a time: `ham_solution_iff`, `gauss_solution_iff`,
  `diffeo_solution_iff`; pairwise: `ham_gauss_solution_iff` (exactly the neutral field),
  `gauss_diffeo_solution_iff` (exactly pure scale), `ham_diffeo_solution_iff` (exactly pure hair).
* `constraints_closed` — **the joint constraint surface is the single point `0`**, and this is
  precisely the self limit of `NRRF796`: `divg A ^ 2 / 3 + (∑ i, curl A i ^ 2) / 2 +
  nrm2 (shearPart A) = nrm2 A` leaves no room.  `constraint_surfaces_nontrivial` shows the three
  are nonetheless genuine, independent constraints: none is vacuous and none is empty.
* Constraint algebra: `ham_entangle` (a bracket carries no source), `entangle_neutral_pure_gauss`
  (the bracket of two neutral relations is pure hair: brackets of the neutral constraint close on
  the Gauss sector), `entangle_scale_central` (the scale sector is central, so it brackets to
  nothing), and `constraint_algebra_closes` collecting them.  `constraints_relInv` records that
  the whole constraint set is carried to itself by the one inversion.

## §3  The scenarios

Seven named scenarios, each closed by the existing machinery:

1. *Pure gravity* (`scenario_pure_gravity`): the gravitational relation solves the Gauss and the
   neutral constraint identically and its Hamiltonian constraint value **is** the ball
   translation, which the value recovers exactly (`scenario_pure_gravity_absolute`).
2. *Quantum phase* (`scenario_phase_returns`, `scenario_ball_does_not_return`): the hair sector
   returns after one loop, the ball sector never does.
3. *Approach to a singularity* (`scenario_singularity_unbounded`): along the seam field both
   readings leave every bound, while the hair keeps to the single direction `v`.
4. *At the seam* (`scenario_seam_all_constraints`): at `tan (π/2)` the scale and Gauss constraints
   hold and only the neutral variable is left — nonzero whenever the background carries shear.
   The seam is where the constraint surface is reached, not where the relation disappears.
5. *Entanglement* (`scenario_entanglement`): the order defect of two translations is sourceless
   pure hair, antisymmetric in the pair, zero exactly on commuting pairs, and genuinely nonzero.
6. *Superposition and demons* (`scenario_superposition`, `scenario_demon`): the hair variable is
   linear, interference leaves a neutral residue, and a hair-preserving demon gains no source.
7. *Finite observation* (`scenario_finite_observation`): every finite battery of loop tests fails
   to fix the state, the whole family fixes it exactly, and the geometric configuration
   `qgConfig` makes the same identifications as the sensors.

`nrrf797_closure` collects the clauses.  Everything is `sorry`-free and the axiom audit at the end
of the file is machine-checked.

As throughout this project, the physical words name the constructions defined here and in the
imported modules; every claim is a claim about those constructions.
-/

namespace NRRF797

open NRRF683 NRRF786 NRRF791 NRRF794 NRRF796 Matrix Real Filter Topology

noncomputable section

/-! ## §0  Small algebraic facts about the sectors -/

theorem divg_add (A B : LocalRel) : divg (A + B) = divg A + divg B := by
  simp [divg, Matrix.trace_add]

theorem dilPart_add (A B : LocalRel) : dilPart (A + B) = dilPart A + dilPart B := by
  simp [dilPart, Matrix.trace_add, add_div, add_smul]

theorem shearPart_add (A B : LocalRel) : shearPart (A + B) = shearPart A + shearPart B := by
  simp [shearPart, symPart_add, dilPart_add]
  abel

theorem shearPart_smul (c : ℝ) (A : LocalRel) : shearPart (c • A) = c • shearPart A := by
  ext i j
  simp only [Matrix.smul_apply, shearPart_apply, Matrix.trace_smul, smul_eq_mul]
  by_cases h : i = j <;> simp [h] <;> ring

theorem shearPart_eq_sub (A : LocalRel) : shearPart A = A - dilPart A - rotPart A := by
  have h := rel_decompose A
  ext i j
  have hij := congrFun (congrFun h i) j
  simp only [Matrix.add_apply, Matrix.sub_apply] at hij ⊢
  linarith

theorem dilPart_smul_one (c : ℝ) :
    dilPart ((c : ℝ) • (1 : LocalRel)) = (c : ℝ) • (1 : LocalRel) := by
  rw [dilPart, trace_smul_one]
  norm_num

theorem rotPart_smul_one (c : ℝ) : rotPart ((c : ℝ) • (1 : LocalRel)) = 0 :=
  rotPart_of_sym (transpose_smul_one c)

theorem shearPart_smul_one (c : ℝ) : shearPart ((c : ℝ) • (1 : LocalRel)) = 0 := by
  rw [shearPart_eq_sub, dilPart_smul_one, rotPart_smul_one]
  simp

theorem shearPart_of_antisym {X : LocalRel} (hX : Xᵀ = -X) : shearPart X = 0 := by
  rw [shearPart, symPart_of_antisym hX, dilPart, trace_of_antisym hX]
  simp

theorem shearPart_axialMat (v : Fin 3 → ℝ) : shearPart (axialMat v) = 0 :=
  shearPart_of_antisym (axialMat_antisym v)

theorem divg_axialMat (v : Fin 3 → ℝ) : divg (axialMat v) = 0 :=
  trace_of_antisym (axialMat_antisym v)

theorem curl_one : curl (1 : LocalRel) = 0 := by
  funext i; fin_cases i <;> simp [curl]

theorem divg_smul_one (c : ℝ) : divg ((c : ℝ) • (1 : LocalRel)) = 3 * c := trace_smul_one c

theorem curl_eq_of_hair_eq {A B : LocalRel} (h : hair A = hair B) : curl A = curl B := by
  funext i
  have := congrFun h i
  simp [hair] at this
  linarith

theorem hair_axialMat (v : Fin 3 → ℝ) : hair (axialMat v) = v := by
  funext i
  simp [hair, curl_axialMat]

theorem shearPart_of_neutral {N : LocalRel} (hN : Neutral N) : shearPart N = N :=
  neutral_iff_shearPart_eq_self.1 hN

theorem shearPart_zero : shearPart (0 : LocalRel) = 0 := by
  simpa using shearPart_smul_one 0

theorem hair_zero : hair (0 : LocalRel) = 0 := hair_eq_zero_iff.2 curl_zero

theorem divg_zero : divg (0 : LocalRel) = 0 := by simp [divg]

/-! ## §1  The variables of the closure's quantum gravity -/

/-- **The variables.**  The scale variable, the hair variable and the neutral variable of a local
relation: exactly the readings the unified work forces, and nothing else. -/
def qgVars (A : LocalRel) : ℝ × (Fin 3 → ℝ) × LocalRel := (divg A, hair A, shearPart A)

/-- **The variables fix the relation.**  There is no hidden fourth datum: this is
`NRRF794.local_readings_complete`. -/
theorem qgVars_injective : Function.Injective qgVars := by
  intro A B h
  have hd : divg A = divg B := congrArg Prod.fst h
  have hh : hair A = hair B := congrArg (fun p => p.2.1) h
  have hs : shearPart A = shearPart B := congrArg (fun p => p.2.2) h
  exact local_readings_complete hd (curl_eq_of_hair_eq hh) hs

/-- The relation built from a prescribed value of each variable. -/
def qgRel (s : ℝ) (h : Fin 3 → ℝ) (N : LocalRel) : LocalRel :=
  (s / 3) • (1 : LocalRel) + axialMat h + N

theorem divg_qgRel (s : ℝ) (h : Fin 3 → ℝ) {N : LocalRel} (hN : Neutral N) :
    divg (qgRel s h N) = s := by
  rw [qgRel, divg_add, divg_add, divg_smul_one, divg_axialMat, hN.1]
  ring

theorem hair_qgRel (s : ℝ) (h : Fin 3 → ℝ) {N : LocalRel} (hN : Neutral N) :
    hair (qgRel s h N) = h := by
  rw [qgRel]
  funext i
  have hc : curl ((s / 3) • (1 : LocalRel) + axialMat h + N) i = 2 * h i := by
    rw [curl_add, curl_add, curl_smul, curl_one, hN.2, curl_axialMat]
    simp
  simp [hair, hc]

theorem shearPart_qgRel (s : ℝ) (h : Fin 3 → ℝ) {N : LocalRel} (hN : Neutral N) :
    shearPart (qgRel s h N) = N := by
  rw [qgRel, shearPart_add, shearPart_add, shearPart_smul_one, shearPart_axialMat,
    shearPart_of_neutral hN]
  simp

/-- The variables of the prescribed relation are the prescribed values. -/
theorem qgVars_qgRel (s : ℝ) (h : Fin 3 → ℝ) {N : LocalRel} (hN : Neutral N) :
    qgVars (qgRel s h N) = (s, h, N) := by
  rw [qgVars, divg_qgRel s h hN, hair_qgRel s h hN, shearPart_qgRel s h hN]

/-- **The variables are free.**  Every admissible triple — arbitrary scale, arbitrary hair, any
neutral relation — is the variable triple of an actual local relation. -/
theorem qgVars_surjective (s : ℝ) (h : Fin 3 → ℝ) {N : LocalRel} (hN : Neutral N) :
    ∃ A : LocalRel, qgVars A = (s, h, N) :=
  ⟨qgRel s h N, qgVars_qgRel s h hN⟩

/-- **The three variables are independent**: each can be moved with the other two held fixed. -/
theorem qgVars_independent (s s' : ℝ) (h h' : Fin 3 → ℝ) {N N' : LocalRel}
    (hN : Neutral N) (hN' : Neutral N') :
    qgVars (qgRel s h N) = (s, h, N) ∧ qgVars (qgRel s' h N) = (s', h, N) ∧
      qgVars (qgRel s h' N) = (s, h', N) ∧ qgVars (qgRel s h N') = (s, h, N') :=
  ⟨qgVars_qgRel s h hN, qgVars_qgRel s' h hN, qgVars_qgRel s h' hN, qgVars_qgRel s h hN'⟩

/-- The neutral variable is inversion-odd. -/
theorem shearPart_relInv (A : LocalRel) : shearPart (relInv A) = -shearPart A := by
  have h : relInv A = -Aᵀ := rfl
  rw [shearPart, shearPart, h]
  have hs : symPart (-Aᵀ) = -symPart A := by
    ext i j; simp [symPart_apply]; ring
  have hd : dilPart (-Aᵀ) = -dilPart A := by
    simp [dilPart, Matrix.trace_transpose, neg_div]
  rw [hs, hd]
  abel

/-- **The variables under the one inversion**: scale reverses, hair is preserved, the neutral
variable reverses. -/
theorem qgVars_relInv (A : LocalRel) :
    qgVars (relInv A) = (-divg A, hair A, -shearPart A) := by
  rw [qgVars, divg_relInv, hair_relInv, shearPart_relInv]

/-! ## §2  The constraints -/

/-- **The scale (Hamiltonian) constraint**: the source read at the point. -/
def hamiltonianConstraint (A : LocalRel) : ℝ := divg A

/-- **The rotation (Gauss) constraint**: the hair read at the point. -/
def gaussConstraint (A : LocalRel) : Fin 3 → ℝ := hair A

/-- **The neutral (diffeomorphism) constraint**: the shear sector at the point. -/
def diffeoConstraint (A : LocalRel) : LocalRel := shearPart A

@[simp] theorem hamiltonianConstraint_eq (A : LocalRel) : hamiltonianConstraint A = divg A := rfl

@[simp] theorem gaussConstraint_eq (A : LocalRel) : gaussConstraint A = hair A := rfl

@[simp] theorem diffeoConstraint_eq (A : LocalRel) : diffeoConstraint A = shearPart A := rfl

theorem constraints_linear (A B : LocalRel) (c : ℝ) :
    (hamiltonianConstraint (A + B) = hamiltonianConstraint A + hamiltonianConstraint B ∧
      hamiltonianConstraint (c • A) = c * hamiltonianConstraint A) ∧
    (gaussConstraint (A + B) = gaussConstraint A + gaussConstraint B ∧
      gaussConstraint (c • A) = c • gaussConstraint A) ∧
    (diffeoConstraint (A + B) = diffeoConstraint A + diffeoConstraint B ∧
      diffeoConstraint (c • A) = c • diffeoConstraint A) :=
  ⟨⟨divg_add A B, by simp [divg]⟩, ⟨hair_add A B, hair_smul c A⟩,
    ⟨shearPart_add A B, shearPart_smul c A⟩⟩

/-- The scale constraint holds exactly on the relations with no dilation sector. -/
theorem ham_solution_iff {A : LocalRel} : hamiltonianConstraint A = 0 ↔ dilPart A = 0 := by
  constructor
  · exact dilPart_eq_zero_of_divg_eq_zero
  · intro h
    have ht := congrArg Matrix.trace h
    rw [dilPart, Matrix.trace_smul, Matrix.trace_one] at ht
    simp only [hamiltonianConstraint, divg]
    simp only [Matrix.trace_zero, smul_eq_mul, Fintype.card_fin] at ht
    push_cast at ht
    linarith

/-- The Gauss constraint holds exactly on the relations with no hair sector. -/
theorem gauss_solution_iff {A : LocalRel} : gaussConstraint A = 0 ↔ rotPart A = 0 := by
  constructor
  · intro h
    exact rotPart_eq_zero_of_curl_eq_zero (hair_eq_zero_iff.1 h)
  · intro h
    have hc : curl A = 0 := by rw [← curl_rotPart, h, curl_zero]
    exact hair_eq_zero_iff.2 hc

/-- The neutral constraint holds exactly on the relations that are scale plus hair. -/
theorem diffeo_solution_iff {A : LocalRel} :
    diffeoConstraint A = 0 ↔ A = dilPart A + rotPart A := by
  have hd := rel_decompose A
  constructor
  · intro h
    rw [diffeoConstraint_eq] at h
    rw [h, add_zero] at hd
    exact hd.symm
  · intro h
    rw [diffeoConstraint_eq]
    rw [← h] at hd
    simpa using hd

/-- Scale and Gauss together: exactly the neutral field. -/
theorem ham_gauss_solution_iff {A : LocalRel} :
    (hamiltonianConstraint A = 0 ∧ gaussConstraint A = 0) ↔ Neutral A :=
  neutral_iff_no_source_no_hair.symm

/-- Gauss and neutral together: exactly the pure scale relations. -/
theorem gauss_diffeo_solution_iff {A : LocalRel} :
    (gaussConstraint A = 0 ∧ diffeoConstraint A = 0) ↔ A = (divg A / 3) • (1 : LocalRel) := by
  have hd := rel_decompose A
  constructor
  · rintro ⟨hg, hs⟩
    rw [diffeoConstraint_eq] at hs
    rw [gauss_solution_iff.1 hg, hs, add_zero, add_zero] at hd
    conv_lhs => rw [← hd]
    rfl
  · intro h
    have hg : gaussConstraint A = 0 := by
      refine gauss_solution_iff.2 ?_
      rw [h]
      exact rotPart_smul_one _
    refine ⟨hg, ?_⟩
    rw [diffeoConstraint_eq]
    nth_rewrite 1 [h]
    exact shearPart_smul_one _

/-- Scale and neutral together: exactly the pure hair relations. -/
theorem ham_diffeo_solution_iff {A : LocalRel} :
    (hamiltonianConstraint A = 0 ∧ diffeoConstraint A = 0) ↔ A = axialMat (hair A) := by
  have hd := rel_decompose A
  constructor
  · rintro ⟨hh, hs⟩
    rw [diffeoConstraint_eq] at hs
    rw [ham_solution_iff.1 hh, hs, zero_add, add_zero] at hd
    rw [axialMat_hair, hd]
  · intro h
    refine ⟨?_, ?_⟩
    · rw [hamiltonianConstraint_eq]
      nth_rewrite 1 [h]
      exact divg_axialMat _
    · rw [diffeoConstraint_eq]
      nth_rewrite 1 [h]
      exact shearPart_axialMat _

/-- **The joint constraint surface is the single point `0`.**  This is exactly the self limit of
`NRRF796`: the three readings already exhaust the relation's translational content. -/
theorem constraints_closed {A : LocalRel} :
    (hamiltonianConstraint A = 0 ∧ gaussConstraint A = 0 ∧ diffeoConstraint A = 0) ↔ A = 0 := by
  constructor
  · rintro ⟨hh, hg, hs⟩
    rw [hamiltonianConstraint_eq] at hh
    rw [diffeoConstraint_eq] at hs
    have hc : curl A = 0 := hair_eq_zero_iff.1 hg
    have hz : nrm2 (0 : LocalRel) = 0 := (nrm2_eq_zero_iff 0).2 rfl
    have hlim := self_limit_equality A
    rw [hh, hc, hs, hz] at hlim
    have h0 : nrm2 A = 0 := by simpa using hlim.symm
    exact (nrm2_eq_zero_iff A).1 h0
  · rintro rfl
    exact ⟨divg_zero, hair_zero, shearPart_zero⟩

/-- None of the three constraints is vacuous, and none is empty: each has nonzero solutions, and
each is violated by some relation. -/
theorem constraint_surfaces_nontrivial :
    (∃ A : LocalRel, A ≠ 0 ∧ hamiltonianConstraint A = 0) ∧
    (∃ A : LocalRel, A ≠ 0 ∧ gaussConstraint A = 0) ∧
    (∃ A : LocalRel, A ≠ 0 ∧ diffeoConstraint A = 0) ∧
    (∃ A : LocalRel, hamiltonianConstraint A ≠ 0) ∧
    (∃ A : LocalRel, gaussConstraint A ≠ 0) ∧
    (∃ A : LocalRel, diffeoConstraint A ≠ 0) := by
  have hone : ((1 : ℝ) • (1 : LocalRel)) ≠ 0 := by
    intro h
    have := congrFun (congrFun h 0) 0
    simp at this
  have hax : axialMat ![1, 0, 0] ≠ 0 := by
    intro h
    have := congrFun (congrFun h 2) 1
    simp [axialMat] at this
  obtain ⟨N, hN, hN0⟩ := neutral_nontrivial
  refine ⟨⟨axialMat ![1, 0, 0], hax, divg_axialMat _⟩,
    ⟨(1 : ℝ) • (1 : LocalRel), hone, ?_⟩,
    ⟨(1 : ℝ) • (1 : LocalRel), hone, ?_⟩,
    ⟨(1 : ℝ) • (1 : LocalRel), ?_⟩,
    ⟨axialMat ![1, 0, 0], ?_⟩,
    ⟨N, ?_⟩⟩
  · exact gauss_solution_iff.2 (rotPart_smul_one 1)
  · exact shearPart_smul_one 1
  · rw [hamiltonianConstraint_eq, divg_smul_one]
    norm_num
  · rw [gaussConstraint_eq, hair_axialMat]
    intro h
    have := congrFun h 0
    simp at this
  · rw [diffeoConstraint_eq, shearPart_of_neutral hN]
    exact hN0

/-- **The constraint set is carried to itself by the one inversion.** -/
theorem constraints_relInv (A : LocalRel) :
    hamiltonianConstraint (relInv A) = -hamiltonianConstraint A ∧
    gaussConstraint (relInv A) = gaussConstraint A ∧
    diffeoConstraint (relInv A) = -diffeoConstraint A :=
  ⟨divg_relInv A, hair_relInv A, shearPart_relInv A⟩

/-- A bracket of two translations carries no source: the scale constraint holds on every
bracket. -/
theorem ham_entangle (A B : LocalRel) : hamiltonianConstraint (entangle A B) = 0 :=
  divg_entangle A B

/-- The order defect of two symmetric relations is antisymmetric. -/
theorem entangle_antisym_of_sym {A B : LocalRel} (hA : Aᵀ = A) (hB : Bᵀ = B) :
    (entangle A B)ᵀ = -entangle A B := by
  rw [entangle, Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul, hA, hB]
  abel

/-- **The brackets of the neutral sector close on the Gauss sector**: the order defect of two
neutral relations has no source and no shear — it is pure hair. -/
theorem entangle_neutral_pure_gauss {A B : LocalRel} (hA : Neutral A) (hB : Neutral B) :
    hamiltonianConstraint (entangle A B) = 0 ∧ diffeoConstraint (entangle A B) = 0 ∧
      entangle A B = axialMat (gaussConstraint (entangle A B)) := by
  have hAs : Aᵀ = A := (neutral_iff_symmetric_traceless.1 hA).1
  have hBs : Bᵀ = B := (neutral_iff_symmetric_traceless.1 hB).1
  have hanti : (entangle A B)ᵀ = -entangle A B := entangle_antisym_of_sym hAs hBs
  refine ⟨ham_entangle A B, shearPart_of_antisym hanti, ?_⟩
  rw [gaussConstraint_eq, axialMat_hair, rotPart_of_antisym hanti]

/-- **The scale sector is central**: a pure scale relation brackets to nothing. -/
theorem entangle_scale_central (c : ℝ) (B : LocalRel) :
    entangle ((c : ℝ) • (1 : LocalRel)) B = 0 := by
  simp [entangle]

/-- **The constraint algebra closes.** -/
theorem constraint_algebra_closes :
    (∀ A B : LocalRel, hamiltonianConstraint (entangle A B) = 0) ∧
    (∀ A B : LocalRel, Neutral A → Neutral B →
      diffeoConstraint (entangle A B) = 0 ∧ hamiltonianConstraint (entangle A B) = 0) ∧
    (∀ (c : ℝ) (B : LocalRel), entangle ((c : ℝ) • (1 : LocalRel)) B = 0) ∧
    (∀ A B : LocalRel, entangle A B = 0 ↔ A * B = B * A) :=
  ⟨ham_entangle,
   fun A B hA hB => ⟨(entangle_neutral_pure_gauss hA hB).2.1, ham_entangle A B⟩,
   entangle_scale_central,
   fun _ _ => entangle_eq_zero_iff⟩

/-! ## §3  The scenarios -/

/-- **Scenario 1 — pure gravity.**  The gravitational relation of a state solves the Gauss and the
neutral constraint identically, and its scale-constraint value is the ball translation itself. -/
theorem scenario_pure_gravity (x : State) :
    gaussConstraint (gravRel x) = 0 ∧ diffeoConstraint (gravRel x) = 0 ∧
      hamiltonianConstraint (gravRel x) = (x.1 : ℝ) := by
  refine ⟨hair_eq_zero_iff.2 (curl_gravRel x), ?_, divg_gravRel x⟩
  rw [diffeoConstraint_eq, gravRel]
  exact shearPart_smul_one _

/-- Pure gravity is absolute: the scale-constraint value recovers the state's ball translation. -/
theorem scenario_pure_gravity_absolute {x y : State}
    (h : hamiltonianConstraint (gravRel x) = hamiltonianConstraint (gravRel y)) : x.1 = y.1 := by
  rw [hamiltonianConstraint_eq, hamiltonianConstraint_eq, divg_gravRel, divg_gravRel] at h
  exact_mod_cast h

/-- **Scenario 2 — the quantum phase returns.** -/
theorem scenario_phase_returns {k : ℕ} (hk : 0 < k) (x : State) : (phase k x) ^ k = 1 :=
  phase_pow_eq_one hk x

/-- ... while the ball sector never returns. -/
theorem scenario_ball_does_not_return (x : State) {m : ℤ} (hm : m ≠ 0) :
    gravRel (x.1 + m, x.2) ≠ gravRel x := by
  intro h
  have := gravRel_injective h
  simp at this
  exact hm this

/-- **Scenario 3 — approach to a singularity.**  Along the seam field the hair keeps to the one
direction `v`, and both readings leave every bound as the seam is approached. -/
theorem scenario_singularity_unbounded (S : LocalRel) {v : Fin 3 → ℝ} {i : Fin 3} (hv : 0 < v i) :
    (∀ t : ℝ, gaussConstraint (seamField S v t) = Real.tan t • v) ∧
    Tendsto (fun t => hamiltonianConstraint (seamField S v t)) (𝓝[<] (π / 2)) atTop ∧
    Tendsto (fun t => curl (seamField S v t) i) (𝓝[<] (π / 2)) atTop :=
  ⟨fun t => singularity_one_direction S v t, divg_seamField_atTop S v,
    curl_seamField_atTop S hv⟩

/-- **Scenario 4 — at the seam.**  At `tan (π/2)` the scale and Gauss constraints hold, only the
neutral variable is left, and the relation itself is not zero when the background carries shear. -/
theorem scenario_seam_all_constraints {S : LocalRel} (hS : shearPart S ≠ 0) (v : Fin 3 → ℝ) :
    hamiltonianConstraint (seamField S v (π / 2)) = 0 ∧
    gaussConstraint (seamField S v (π / 2)) = 0 ∧
    diffeoConstraint (seamField S v (π / 2)) ≠ 0 ∧
    seamField S v (π / 2) ≠ 0 := by
  refine ⟨(neutral_seamField_pi_div_two S v).1, hair_seamField_pi_div_two S v, ?_,
    seamField_pi_div_two_ne_zero hS v⟩
  rw [diffeoConstraint_eq, seamField_pi_div_two, shearPart_idem]
  exact hS

/-- **Scenario 5 — entanglement.**  The order defect of two translations is sourceless pure hair,
antisymmetric in the pair, zero exactly on commuting pairs, and genuinely nonzero. -/
theorem scenario_entanglement :
    (∀ A B : LocalRel, hamiltonianConstraint (entangle A B) = 0) ∧
    (∀ A B : LocalRel, gaussConstraint (entangle A B) = -gaussConstraint (entangle B A)) ∧
    (∀ A B : LocalRel, entangle A B = 0 ↔ A * B = B * A) ∧
    (∃ A B : LocalRel, gaussConstraint (entangle A B) ≠ 0) :=
  ⟨ham_entangle, fun A B => hair_entangle_comm A B, fun _ _ => entangle_eq_zero_iff,
    entangle_hair_nontrivial⟩

/-- **Scenario 6a — superposition.**  The hair variable is linear, and destructive interference
leaves a nonzero neutral residue. -/
theorem scenario_superposition :
    (∀ (c : ℝ) (A B : LocalRel), gaussConstraint (A + B) = gaussConstraint A + gaussConstraint B ∧
      gaussConstraint (c • A) = c • gaussConstraint A) ∧
    (∃ A B : LocalRel, gaussConstraint A ≠ 0 ∧ gaussConstraint B ≠ 0 ∧
      gaussConstraint (A + B) = 0 ∧ Neutral (A + B) ∧ A + B ≠ 0) :=
  ⟨fun c A B => ⟨hair_add A B, hair_smul c A⟩, hair_interference⟩

/-- **Scenario 6b — the demon.**  A linear demon that leaves the hair alone and never loses source
on the neutral field gains no source there at all, and keeps the neutral field neutral. -/
theorem scenario_demon (D : Demon) {A : LocalRel} (hA : Neutral A) :
    hamiltonianConstraint (D.act A) = 0 ∧ Neutral (D.act A) :=
  ⟨demon_no_free_source D hA, demon_preserves_neutral D hA⟩

/-- **Scenario 7 — finite observation.**  No finite battery of loop tests fixes the state, the
whole family fixes it exactly, and the geometric configuration makes precisely the sensors'
identifications. -/
theorem scenario_finite_observation (k : ℕ) (hk : 0 < k) :
    (∀ R : Finset ℕ, (∀ n ∈ R, 0 < n) → ¬ TranslationallyComplete k (R : Set ℕ)) ∧
    TranslationallyComplete k {n | 0 < n} ∧
    (∀ x y : State, qgConfig k x = qgConfig k y ↔ ∀ n, 0 < n → Test k n x y) :=
  ⟨fun R hR => not_complete_of_finite k R hR, complete_all_resolutions k,
    fun x y => qgConfig_eq_iff_all_tests hk x y⟩

/-! ## §4  The answer -/

/-- **NRRF797.**  The unified work closes the named constraints, variables and scenarios of the
closure's quantum gravity: the three variables fix the relation and are freely realised; the three
constraints are linear, their pairwise surfaces are exactly the three sectors, their joint surface
is the single point `0`, and their algebra closes; and each named scenario is a theorem about the
same objects. -/
theorem nrrf797_closure (k : ℕ) (hk : 0 < k) :
    -- variables
    Function.Injective qgVars ∧
    (∀ (s : ℝ) (h : Fin 3 → ℝ) (N : LocalRel), Neutral N → ∃ A : LocalRel, qgVars A = (s, h, N)) ∧
    (∀ A : LocalRel, qgVars (relInv A) = (-divg A, hair A, -shearPart A)) ∧
    -- constraints
    (∀ A : LocalRel,
      (hamiltonianConstraint A = 0 ∧ gaussConstraint A = 0 ∧ diffeoConstraint A = 0) ↔ A = 0) ∧
    (∀ A : LocalRel, (hamiltonianConstraint A = 0 ∧ gaussConstraint A = 0) ↔ Neutral A) ∧
    (∀ A : LocalRel,
      (gaussConstraint A = 0 ∧ diffeoConstraint A = 0) ↔ A = (divg A / 3) • (1 : LocalRel)) ∧
    (∀ A : LocalRel, (hamiltonianConstraint A = 0 ∧ diffeoConstraint A = 0) ↔
      A = axialMat (hair A)) ∧
    (∀ A B : LocalRel, hamiltonianConstraint (entangle A B) = 0) ∧
    (∀ A B : LocalRel, Neutral A → Neutral B → diffeoConstraint (entangle A B) = 0) ∧
    -- scenarios
    (∀ x : State, gaussConstraint (gravRel x) = 0 ∧ diffeoConstraint (gravRel x) = 0 ∧
      hamiltonianConstraint (gravRel x) = (x.1 : ℝ)) ∧
    (∀ x : State, (phase k x) ^ k = 1) ∧
    (∀ (S : LocalRel) (v : Fin 3 → ℝ) (t : ℝ), gaussConstraint (seamField S v t) = tan t • v) ∧
    (∀ (S : LocalRel) (v : Fin 3 → ℝ), shearPart S ≠ 0 →
      hamiltonianConstraint (seamField S v (π / 2)) = 0 ∧
      gaussConstraint (seamField S v (π / 2)) = 0 ∧ seamField S v (π / 2) ≠ 0) ∧
    (∃ A B : LocalRel, gaussConstraint (entangle A B) ≠ 0) ∧
    (∀ (D : Demon) (A : LocalRel), Neutral A → hamiltonianConstraint (D.act A) = 0) ∧
    (∀ R : Finset ℕ, (∀ n ∈ R, 0 < n) → ¬ TranslationallyComplete k (R : Set ℕ)) ∧
    TranslationallyComplete k {n | 0 < n} :=
  ⟨qgVars_injective,
   fun s h _ hN => qgVars_surjective s h hN,
   qgVars_relInv,
   fun _ => constraints_closed,
   fun _ => ham_gauss_solution_iff,
   fun _ => gauss_diffeo_solution_iff,
   fun _ => ham_diffeo_solution_iff,
   ham_entangle,
   fun _ _ hA hB => (entangle_neutral_pure_gauss hA hB).2.1,
   scenario_pure_gravity,
   fun x => phase_pow_eq_one hk x,
   fun S v t => singularity_one_direction S v t,
   fun _S v hS => ⟨(scenario_seam_all_constraints hS v).1,
     (scenario_seam_all_constraints hS v).2.1, (scenario_seam_all_constraints hS v).2.2.2⟩,
   entangle_hair_nontrivial,
   fun D _ hA => demon_no_free_source D hA,
   fun R hR => not_complete_of_finite k R hR,
   complete_all_resolutions k⟩

end

end NRRF797

/-! ## Audit -/

section Audit

/-- info: 'NRRF797.qgVars_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF797.qgVars_injective

/-- info: 'NRRF797.qgVars_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF797.qgVars_surjective

/-- info: 'NRRF797.constraints_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF797.constraints_closed

/-- info: 'NRRF797.constraint_algebra_closes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF797.constraint_algebra_closes

/-- info: 'NRRF797.scenario_seam_all_constraints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF797.scenario_seam_all_constraints

/-- info: 'NRRF797.nrrf797_closure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF797.nrrf797_closure

end Audit
