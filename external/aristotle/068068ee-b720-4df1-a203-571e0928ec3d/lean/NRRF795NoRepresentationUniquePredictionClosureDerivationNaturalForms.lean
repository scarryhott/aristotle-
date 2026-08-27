import Mathlib
import NRRF791TanPiHalfDivCurlNeutralFieldBallHair
import NRRF793ClosureNativeTanFoldForcedReadingsNoAssumedPieces

/-!
# NRRF795 — No representation is needed: the unique prediction *is* the closure derivation of the natural forms

The correction being formalised:

> We don't need a representation; instead the unique prediction is precisely the closure
> derivation of natural forms.

Two things have to be proved for that reading to be a statement rather than a slogan.

* **The derivation is unique.**  Bundle the closure conditions — order-blindness and
  normalisation for the scale reading, return-blindness and ball-normalisation for the hair
  reading — into a single object, a `ClosureDerivation`.  Then that object *exists* and there is
  exactly one of it (`closureDerivation_exists`, `closureDerivation_unique`,
  `unique_prediction`).  Its two readings are the divergence and the curl
  (`ClosureDerivation.scale_eq`, `ClosureDerivation.hairRead_eq`).  So the closure has one
  prediction, not a family of them.

* **A representation adds nothing and is not determined.**  A *representation* here is any
  faithful linear encoding of the local relations into an ambient carrier, with the readings
  performed downstream of the encoding (`RepDerivation`).  Whatever the carrier and whatever the
  encoding, the readings obtained are again the divergence and the curl
  (`repDerivation_scale_eq`, `repDerivation_hairRead_eq`), so any two representations, over any
  two carriers, predict the same thing (`prediction_representation_independent`).  Conversely the
  prediction does not fix the representation: rescaling an encoding gives a different
  representation with the identical prediction (`representation_underdetermined`), and carriers
  of strictly larger dimension carry representations too (`representation_surplus_carrier`).  The
  representation is surplus structure; the derivation is the content.

* **Nothing is lost by dropping the representation.**  A local relation is reconstructed from its
  own natural forms and its neutral residue, with no encoding anywhere
  (`state_from_natural_forms`, `state_determined_by_forms`), the forms are jointly realisable so
  the prediction is not empty talk (`forms_realizable`), and the residue the forms do not see is
  exactly the neutral field, which is nonzero (`residue_is_neutral`).

`nrrf795_answer` collects the clauses.

Nothing here is claimed about any physical representation theory; "representation" always means
the faithful linear encoding defined in §2, and "forced"/"unique" always mean relative to the
closure conditions written into the structures below.
-/

namespace NRRF795

open NRRF683 NRRF791 NRRF793 Matrix

noncomputable section

/-! ## §1  The closure derivation, bundled -/

/-- The divergence as a linear reading. -/
def divgLin : LocalRel →ₗ[ℝ] ℝ where
  toFun := divg
  map_add' A B := by simp [divg, Matrix.trace_add]
  map_smul' c A := by simp [divg, Matrix.trace_smul]

/-- The curl as a linear reading. -/
def curlLin : LocalRel →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun := curl
  map_add' A B := by
    funext i
    fin_cases i <;> simp [curl] <;> ring
  map_smul' c A := by
    funext i
    fin_cases i <;> simp [curl] <;> ring

@[simp] theorem divgLin_apply (A : LocalRel) : divgLin A = divg A := rfl

@[simp] theorem curlLin_apply (A : LocalRel) : curlLin A = curl A := rfl

/-- **The closure derivation.**  A pair of linear readings of the local relations subject only to
the closure's own conditions: the scalar reading is blind to the order in which two translations
compose and is normalised on the identity relation; the vector reading returns nothing on the
return-symmetric sector and reads a ball direction faithfully.  No form, no sector and no
representation is posited. -/
structure ClosureDerivation where
  /-- The scalar (scale) reading. -/
  scale : LocalRel →ₗ[ℝ] ℝ
  /-- The vector (hair) reading. -/
  hairRead : LocalRel →ₗ[ℝ] (Fin 3 → ℝ)
  /-- The scale reading is blind to the order in which two translations compose. -/
  orderBlind : ∀ A B : LocalRel, scale (A * B) = scale (B * A)
  /-- The scale reading is normalised on the identity relation. -/
  scaleNorm : scale 1 = 3
  /-- The hair reading returns nothing on the return-symmetric sector. -/
  returnBlind : ∀ X : LocalRel, Xᵀ = X → hairRead X = 0
  /-- The hair reading reads a ball direction faithfully. -/
  ballNorm : ∀ v : Fin 3 → ℝ, hairRead (axialMat v) = fun i => 2 * v i

/-- The curl returns nothing on the return-symmetric sector. -/
theorem curl_of_sym {X : LocalRel} (hX : Xᵀ = X) : curl X = 0 := by
  have h : curl (symPart X) = 0 := curl_symPart X
  rwa [symPart_of_sym hX] at h

/-- The derivation the closure itself performs: divergence and curl. -/
def theDerivation : ClosureDerivation where
  scale := divgLin
  hairRead := curlLin
  orderBlind A B := Matrix.trace_mul_comm A B
  scaleNorm := by simp [divg]
  returnBlind X hX := curl_of_sym hX
  ballNorm v := by simpa using curl_axialMat v

/-- There is a closure derivation. -/
theorem closureDerivation_exists : Nonempty ClosureDerivation := ⟨theDerivation⟩

/-- The scale reading of *any* closure derivation is the divergence. -/
theorem ClosureDerivation.scale_eq (D : ClosureDerivation) (A : LocalRel) :
    D.scale A = divg A :=
  divg_forced_normalized D.scale D.orderBlind D.scaleNorm A

/-- The hair reading of *any* closure derivation is the curl. -/
theorem ClosureDerivation.hairRead_eq (D : ClosureDerivation) (A : LocalRel) :
    D.hairRead A = curl A :=
  curl_forced D.hairRead D.returnBlind D.ballNorm A

/-- **There is only one closure derivation.**  The closure conditions do not leave a family of
admissible derivations to choose a representative from: they leave one object. -/
theorem closureDerivation_unique (D E : ClosureDerivation) : D = E := by
  have hs : D.scale = E.scale :=
    LinearMap.ext fun A => by rw [D.scale_eq, E.scale_eq]
  have hh : D.hairRead = E.hairRead :=
    LinearMap.ext fun A => by rw [D.hairRead_eq, E.hairRead_eq]
  cases D; cases E
  simp_all

instance : Subsingleton ClosureDerivation := ⟨closureDerivation_unique⟩

/-- **The unique prediction.**  There is exactly one pair of readings meeting the closure
conditions, and it is the pair of natural forms — the divergence and the curl. -/
theorem unique_prediction :
    ∃! p : (LocalRel →ₗ[ℝ] ℝ) × (LocalRel →ₗ[ℝ] (Fin 3 → ℝ)),
      (∀ A B : LocalRel, p.1 (A * B) = p.1 (B * A)) ∧ p.1 1 = 3 ∧
        (∀ X : LocalRel, Xᵀ = X → p.2 X = 0) ∧
        (∀ v : Fin 3 → ℝ, p.2 (axialMat v) = fun i => 2 * v i) := by
  refine ⟨(divgLin, curlLin),
    ⟨theDerivation.orderBlind, theDerivation.scaleNorm, theDerivation.returnBlind,
      theDerivation.ballNorm⟩, ?_⟩
  rintro ⟨f, L⟩ ⟨h1, h2, h3, h4⟩
  have hf : f = divgLin :=
    LinearMap.ext fun A => by
      simpa using divg_forced_normalized f h1 h2 A
  have hL : L = curlLin :=
    LinearMap.ext fun A => by
      simpa using curl_forced L h3 h4 A
  simp [hf, hL]

/-! ## §2  Representations, and why they are not needed -/

/-- A **representation**: a faithful linear encoding of the local relations into some ambient
carrier.  This is the structure the reading says we do *not* need. -/
structure Representation (W : Type) [AddCommGroup W] [Module ℝ W] where
  /-- The encoding map. -/
  encode : LocalRel →ₗ[ℝ] W
  /-- The encoding is faithful. -/
  faithful : Function.Injective encode

/-- A **derivation performed through a representation**: the readings live on the carrier and are
applied to encoded relations, and the closure conditions are imposed there. -/
structure RepDerivation (W : Type) [AddCommGroup W] [Module ℝ W] extends Representation W where
  /-- The scalar reading, on the carrier. -/
  scale : W →ₗ[ℝ] ℝ
  /-- The vector reading, on the carrier. -/
  hairRead : W →ₗ[ℝ] (Fin 3 → ℝ)
  /-- Order-blindness, imposed downstream of the encoding. -/
  orderBlind : ∀ A B : LocalRel, scale (encode (A * B)) = scale (encode (B * A))
  /-- Normalisation, imposed downstream of the encoding. -/
  scaleNorm : scale (encode 1) = 3
  /-- Return-blindness, imposed downstream of the encoding. -/
  returnBlind : ∀ X : LocalRel, Xᵀ = X → hairRead (encode X) = 0
  /-- Ball-normalisation, imposed downstream of the encoding. -/
  ballNorm : ∀ v : Fin 3 → ℝ, hairRead (encode (axialMat v)) = fun i => 2 * v i

variable {W : Type} [AddCommGroup W] [Module ℝ W]

/-- Every representation-mediated derivation collapses to a bare closure derivation: the
representation is transparent. -/
def RepDerivation.toClosureDerivation (R : RepDerivation W) : ClosureDerivation where
  scale := R.scale ∘ₗ R.encode
  hairRead := R.hairRead ∘ₗ R.encode
  orderBlind := R.orderBlind
  scaleNorm := R.scaleNorm
  returnBlind := R.returnBlind
  ballNorm := R.ballNorm

/-- **Whatever the representation, the scale reading is the divergence.** -/
theorem repDerivation_scale_eq (R : RepDerivation W) (A : LocalRel) :
    R.scale (R.encode A) = divg A :=
  R.toClosureDerivation.scale_eq A

/-- **Whatever the representation, the hair reading is the curl.** -/
theorem repDerivation_hairRead_eq (R : RepDerivation W) (A : LocalRel) :
    R.hairRead (R.encode A) = curl A :=
  R.toClosureDerivation.hairRead_eq A

/-- **The prediction does not depend on the representation.**  Two derivations performed through
arbitrary representations, over arbitrary carriers, return the same readings on every local
relation — the ones the bare closure derivation returns. -/
theorem prediction_representation_independent
    {W₁ W₂ : Type} [AddCommGroup W₁] [Module ℝ W₁] [AddCommGroup W₂] [Module ℝ W₂]
    (R₁ : RepDerivation W₁) (R₂ : RepDerivation W₂) (A : LocalRel) :
    R₁.scale (R₁.encode A) = R₂.scale (R₂.encode A) ∧
      R₁.hairRead (R₁.encode A) = R₂.hairRead (R₂.encode A) :=
  ⟨by rw [repDerivation_scale_eq, repDerivation_scale_eq],
   by rw [repDerivation_hairRead_eq, repDerivation_hairRead_eq]⟩

/-- The bare closure derivation is itself representation-mediated, via the identity encoding: the
representation-free reading is not a special case that has been excluded. -/
def idRepDerivation : RepDerivation LocalRel where
  encode := LinearMap.id
  faithful := fun _ _ h => h
  scale := divgLin
  hairRead := curlLin
  orderBlind := theDerivation.orderBlind
  scaleNorm := theDerivation.scaleNorm
  returnBlind := theDerivation.returnBlind
  ballNorm := theDerivation.ballNorm

/-- Rescaling a faithful encoding by a nonzero factor is again a faithful encoding. -/
def Representation.rescale (ρ : Representation W) {c : ℝ} (hc : c ≠ 0) : Representation W where
  encode := c • ρ.encode
  faithful := by
    intro A B h
    apply ρ.faithful
    have : c • ρ.encode A = c • ρ.encode B := h
    exact smul_right_injective W hc this

/-- Reading the doubled encoding with the compensating normalisation returns the divergence. -/
theorem double_scale (X : LocalRel) :
    ((2 : ℝ)⁻¹ • divgLin) (((2 : ℝ) • (LinearMap.id : LocalRel →ₗ[ℝ] LocalRel)) X) = divg X := by
  show (2 : ℝ)⁻¹ * divg ((2 : ℝ) • X) = divg X
  rw [divg, divg, Matrix.trace_smul, smul_eq_mul]
  ring

/-- Reading the doubled encoding with the compensating normalisation returns the curl. -/
theorem double_hair (X : LocalRel) :
    ((2 : ℝ)⁻¹ • curlLin) (((2 : ℝ) • (LinearMap.id : LocalRel →ₗ[ℝ] LocalRel)) X) = curl X := by
  funext i
  show (2 : ℝ)⁻¹ * curl ((2 : ℝ) • X) i = curl X i
  fin_cases i <;> simp [curl] <;> ring

/-- A second, genuinely different representation of the same relations: the doubled encoding, with
the readings renormalised on the carrier. -/
def doubleRepDerivation : RepDerivation LocalRel where
  encode := (2 : ℝ) • (LinearMap.id : LocalRel →ₗ[ℝ] LocalRel)
  faithful := by
    intro A B h
    have h2 : (2 : ℝ) • A = (2 : ℝ) • B := h
    exact smul_right_injective LocalRel (by norm_num) h2
  scale := (2 : ℝ)⁻¹ • divgLin
  hairRead := (2 : ℝ)⁻¹ • curlLin
  orderBlind A B := by rw [double_scale, double_scale]; exact Matrix.trace_mul_comm A B
  scaleNorm := by rw [double_scale]; simp [divg]
  returnBlind X hX := by rw [double_hair]; exact curl_of_sym hX
  ballNorm v := by rw [double_hair]; simpa using curl_axialMat v

/-- **The prediction does not fix the representation.**  There are two genuinely different
faithful encodings of the local relations whose derivations make exactly the same prediction on
every relation.  So a representation carries structure the prediction never sees; it cannot be
what the closure predicts. -/
theorem representation_underdetermined :
    ∃ R S : RepDerivation LocalRel,
      R.encode ≠ S.encode ∧
        ∀ A : LocalRel, R.scale (R.encode A) = S.scale (S.encode A) ∧
          R.hairRead (R.encode A) = S.hairRead (S.encode A) := by
  refine ⟨idRepDerivation, doubleRepDerivation, ?_, ?_⟩
  · intro h
    have h1 : idRepDerivation.encode (1 : LocalRel) 0 0
        = doubleRepDerivation.encode (1 : LocalRel) 0 0 := by rw [h]
    have hl : idRepDerivation.encode (1 : LocalRel) 0 0 = 1 := by
      simp [idRepDerivation]
    have hr : doubleRepDerivation.encode (1 : LocalRel) 0 0 = 2 := by
      simp [doubleRepDerivation]
    rw [hl, hr] at h1
    norm_num at h1
  · intro A
    exact ⟨by rw [repDerivation_scale_eq, repDerivation_scale_eq],
      by rw [repDerivation_hairRead_eq, repDerivation_hairRead_eq]⟩

/-- **Representations can be carried by arbitrarily larger carriers.**  The local relations embed
faithfully into a strictly larger space, on which the derivation still returns the same forms; the
extra room is surplus. -/
theorem representation_surplus_carrier :
    ∃ R : RepDerivation (LocalRel × ℝ), ∀ A : LocalRel,
      R.scale (R.encode A) = divg A ∧ R.hairRead (R.encode A) = curl A := by
  refine ⟨{ encode := LinearMap.inl ℝ LocalRel ℝ
            faithful := by
              intro A B h
              simpa using congrArg Prod.fst h
            scale := divgLin ∘ₗ LinearMap.fst ℝ LocalRel ℝ
            hairRead := curlLin ∘ₗ LinearMap.fst ℝ LocalRel ℝ
            orderBlind := by intro A B; exact Matrix.trace_mul_comm A B
            scaleNorm := by simp [divg]
            returnBlind := by intro X hX; exact curl_of_sym hX
            ballNorm := by intro v; simpa using curl_axialMat v }, ?_⟩
  intro A
  exact ⟨repDerivation_scale_eq _ A, repDerivation_hairRead_eq _ A⟩

/-! ## §3  Nothing is lost by dropping the representation -/

/-- **A relation is rebuilt from its own natural forms.**  Scale form, hair form (through the ball
direction the curl reads) and the neutral residue reassemble the relation, with no encoding
anywhere in the statement. -/
theorem state_from_natural_forms (A : LocalRel) :
    (divg A / 3) • (1 : LocalRel) + axialMat (hair A) + shearPart A = A := by
  rw [axialMat_hair]
  have : (divg A / 3) • (1 : LocalRel) = dilPart A := by rw [dilPart, divg]
  rw [this, rel_decompose]

/-- **The forms plus the residue determine the relation.**  No further datum — in particular no
representation — is needed to tell two relations apart. -/
theorem state_determined_by_forms {A B : LocalRel} (hd : divg A = divg B) (hc : curl A = curl B)
    (hs : shearPart A = shearPart B) : A = B := by
  have hA := state_from_natural_forms A
  have hB := state_from_natural_forms B
  have hh : hair A = hair B := by
    funext i; rw [hair, hair, hc]
  rw [← hA, ← hB, hd, hh, hs]

/-- **The prediction is not empty**: every pair (scale value, ball direction) is the pair of
readings of an actual relation. -/
theorem forms_realizable (r : ℝ) (v : Fin 3 → ℝ) :
    ∃ A : LocalRel, divg A = r ∧ curl A = v := by
  refine ⟨(r / 3) • (1 : LocalRel) + axialMat (fun i => v i / 2), ?_, ?_⟩
  · have hax : Matrix.trace (axialMat fun i => v i / 2) = 0 :=
      trace_of_antisym (axialMat_antisym _)
    rw [divg, Matrix.trace_add, hax, add_zero, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
    norm_num
  · funext i
    fin_cases i <;> simp [curl, axialMat]

/-- **What the prediction does not see is exactly the neutral field**, and that field is not
zero — so the derivation is a prediction about the readable sectors, honestly bounded. -/
theorem residue_is_neutral (A : LocalRel) :
    (divg A = 0 ∧ curl A = 0) ↔ shearPart A = A :=
  NRRF791.neutral_iff_shearPart_eq_self

/-! ## §4  The answer -/

/-- **We don't need a representation: the unique prediction is precisely the closure derivation of
the natural forms.**

1. a closure derivation exists, and there is exactly one — its readings are the divergence and the
   curl (`unique_prediction`);
2. any derivation performed through any faithful encoding into any carrier returns those same two
   readings, so the prediction is representation-independent;
3. the prediction does not fix a representation: distinct encodings predict identically, and
   larger carriers carry representations too — the representation is surplus;
4. dropping it loses nothing: a relation is rebuilt from its forms and its residue, the forms are
   jointly realisable, and what they miss is exactly the neutral field, which is nonzero. -/
theorem nrrf795_answer :
    (∃! p : (LocalRel →ₗ[ℝ] ℝ) × (LocalRel →ₗ[ℝ] (Fin 3 → ℝ)),
        (∀ A B : LocalRel, p.1 (A * B) = p.1 (B * A)) ∧ p.1 1 = 3 ∧
          (∀ X : LocalRel, Xᵀ = X → p.2 X = 0) ∧
          (∀ v : Fin 3 → ℝ, p.2 (axialMat v) = fun i => 2 * v i)) ∧
    (∀ D E : ClosureDerivation, D = E) ∧
    (∀ D : ClosureDerivation, ∀ A : LocalRel, D.scale A = divg A ∧ D.hairRead A = curl A) ∧
    (∀ {W : Type} [AddCommGroup W] [Module ℝ W] (R : RepDerivation W) (A : LocalRel),
        R.scale (R.encode A) = divg A ∧ R.hairRead (R.encode A) = curl A) ∧
    (∃ R S : RepDerivation LocalRel, R.encode ≠ S.encode ∧
        ∀ A : LocalRel, R.scale (R.encode A) = S.scale (S.encode A) ∧
          R.hairRead (R.encode A) = S.hairRead (S.encode A)) ∧
    (∃ R : RepDerivation (LocalRel × ℝ), ∀ A : LocalRel,
        R.scale (R.encode A) = divg A ∧ R.hairRead (R.encode A) = curl A) ∧
    (∀ A : LocalRel, (divg A / 3) • (1 : LocalRel) + axialMat (hair A) + shearPart A = A) ∧
    (∀ A B : LocalRel, divg A = divg B → curl A = curl B → shearPart A = shearPart B → A = B) ∧
    (∀ (r : ℝ) (v : Fin 3 → ℝ), ∃ A : LocalRel, divg A = r ∧ curl A = v) ∧
    (∀ A : LocalRel, (divg A = 0 ∧ curl A = 0) ↔ shearPart A = A) ∧
    (∃ A : LocalRel, Neutral A ∧ A ≠ 0) :=
  ⟨unique_prediction,
   closureDerivation_unique,
   fun D A => ⟨D.scale_eq A, D.hairRead_eq A⟩,
   fun R A => ⟨repDerivation_scale_eq R A, repDerivation_hairRead_eq R A⟩,
   representation_underdetermined,
   representation_surplus_carrier,
   state_from_natural_forms,
   fun _ _ hd hc hs => state_determined_by_forms hd hc hs,
   forms_realizable,
   residue_is_neutral,
   NRRF791.neutral_nontrivial⟩

end

end NRRF795

/-! ## Audit -/

section Audit

/-- info: 'NRRF795.unique_prediction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF795.unique_prediction

/-- info: 'NRRF795.closureDerivation_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF795.closureDerivation_unique

/-- info: 'NRRF795.repDerivation_scale_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF795.repDerivation_scale_eq

/-- info: 'NRRF795.prediction_representation_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF795.prediction_representation_independent

/-- info: 'NRRF795.representation_underdetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF795.representation_underdetermined

/-- info: 'NRRF795.state_determined_by_forms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF795.state_determined_by_forms

/-- info: 'NRRF795.nrrf795_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF795.nrrf795_answer

end Audit
