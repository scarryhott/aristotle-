import NRRFTradingDeltaDerivedCostTranslationalClosure

/-!
# Trading full closure — representation-free natural form and translational truth

This module is the active-build integration of the retained NRRF795 and NRRF798 interfaces.
It uses no price representation or optimisation metric. A temporal trade is translated by a common
change of every local price level. Its natural form is the same trade translated until its entry
mark is zero. The file proves that this form is the unique normalized member of the translation
orbit, and that derived cost, relative potential, net P&L, and profit are truths of that orbit.
-/

namespace NRRFTradingFullClosure

open NRRFTradingDelta

/-! ## The translation action -/

@[simp] theorem shiftBall_zero (b : InfPriceBall) : shiftBall 0 b = b := by
  cases b
  simp [shiftBall]

theorem shiftBall_add (c d : ℚ) (b : InfPriceBall) :
    shiftBall d (shiftBall c b) = shiftBall (c + d) b := by
  cases b
  simp [shiftBall, add_assoc]

@[simp] theorem shiftTrade_zero (t : ClosedLocalTrade) : shiftTrade 0 t = t := by
  cases t with
  | mk ball side fill closes =>
      cases ball with
      | mk qty bid ask mark fee =>
          cases side <;> simp [shiftTrade, shiftBall]

theorem shiftTrade_add (c d : ℚ) (t : ClosedLocalTrade) :
    shiftTrade d (shiftTrade c t) = shiftTrade (c + d) t := by
  cases t with
  | mk ball side fill closes =>
      cases ball with
      | mk qty bid ask mark fee =>
          cases side <;> simp [shiftTrade, shiftBall, add_assoc]

namespace TemporalClosure

@[simp] theorem shift_zero (t : TemporalClosure) : t.shift 0 = t := by
  cases t with
  | mk qty entryMark exitMark legs =>
      change TemporalClosure.mk qty (entryMark + 0) (exitMark + 0)
          (legs.map (shiftTrade 0)) =
        TemporalClosure.mk qty entryMark exitMark legs
      have hlegs : legs.map (shiftTrade 0) = legs := by
        induction legs with
        | nil => rfl
        | cons leg rest ih =>
            rw [List.map_cons, shiftTrade_zero, ih]
      rw [add_zero, add_zero, hlegs]

theorem shift_add (c d : ℚ) (t : TemporalClosure) :
    (t.shift c).shift d = t.shift (c + d) := by
  cases t
  simp [NRRFTradingDelta.TemporalClosure.shift, List.map_map, shiftTrade_add, add_assoc]

end TemporalClosure

/-! ## Translation and its uniquely derived natural form -/

/-- Two temporal trades are translationally true when one is a common price translation of the
other. -/
def Translates (t u : TemporalClosure) : Prop :=
  ∃ c : ℚ, u = t.shift c

theorem translates_refl (t : TemporalClosure) : Translates t t :=
  ⟨0, (TemporalClosure.shift_zero t).symm⟩

theorem translates_symm {t u : TemporalClosure} (h : Translates t u) : Translates u t := by
  obtain ⟨c, rfl⟩ := h
  refine ⟨-c, ?_⟩
  rw [TemporalClosure.shift_add]
  have hzero : c + -c = 0 := by ring
  rw [hzero, TemporalClosure.shift_zero]

theorem translates_trans {t u v : TemporalClosure}
    (htu : Translates t u) (huv : Translates u v) : Translates t v := by
  obtain ⟨c, rfl⟩ := htu
  obtain ⟨d, rfl⟩ := huv
  exact ⟨c + d, TemporalClosure.shift_add c d t⟩

/-- Translation equivalence as a setoid. -/
def translationSetoid : Setoid TemporalClosure where
  r := Translates
  iseqv := ⟨translates_refl, translates_symm, translates_trans⟩

/-- The representation-free natural form: translate the entry mark to the neutral level. -/
def naturalForm (t : TemporalClosure) : TemporalClosure :=
  t.shift (-t.entryMark)

@[simp] theorem naturalForm_entryMark (t : TemporalClosure) :
    (naturalForm t).entryMark = 0 := by
  simp [naturalForm, TemporalClosure.shift]

/-- A trade is recovered exactly by translating its natural form back to its original entry
level. -/
theorem naturalForm_restore (t : TemporalClosure) :
    (naturalForm t).shift t.entryMark = t := by
  rw [naturalForm, TemporalClosure.shift_add]
  have hzero : -t.entryMark + t.entryMark = 0 := by ring
  rw [hzero, TemporalClosure.shift_zero]

/-- The natural form is blind to the level at which the trade was presented. -/
@[simp] theorem naturalForm_shift (c : ℚ) (t : TemporalClosure) :
    naturalForm (t.shift c) = naturalForm t := by
  rw [naturalForm, naturalForm, TemporalClosure.shift_add]
  change t.shift (c + -(t.entryMark + c)) = t.shift (-t.entryMark)
  congr 1
  ring

@[simp] theorem naturalForm_idem (t : TemporalClosure) :
    naturalForm (naturalForm t) = naturalForm t := by
  rw [naturalForm]
  simp only [naturalForm_entryMark, neg_zero, TemporalClosure.shift_zero]

theorem naturalForm_eq_self_of_entry_zero {t : TemporalClosure} (h : t.entryMark = 0) :
    naturalForm t = t := by
  rw [naturalForm, h, neg_zero, TemporalClosure.shift_zero]

/-- The natural form is complete for translation: equal natural forms are exactly one common
price-level orbit. -/
theorem translates_iff_naturalForm_eq {t u : TemporalClosure} :
    Translates t u ↔ naturalForm t = naturalForm u := by
  constructor
  · rintro ⟨c, rfl⟩
    exact (naturalForm_shift c t).symm
  · intro h
    refine ⟨u.entryMark - t.entryMark, ?_⟩
    calc
      u = (naturalForm u).shift u.entryMark := (naturalForm_restore u).symm
      _ = (naturalForm t).shift u.entryMark := by rw [h]
      _ = ((naturalForm t).shift t.entryMark).shift (u.entryMark - t.entryMark) := by
        rw [TemporalClosure.shift_add]
        congr 1
        ring
      _ = t.shift (u.entryMark - t.entryMark) := by rw [naturalForm_restore]

/-! ## The unique closure derivation -/

/-- A derivation is constrained only to return a translation of its input and to normalize the
entry level. -/
structure ClosureDerivation where
  derive : TemporalClosure → TemporalClosure
  translated : ∀ t, Translates t (derive t)
  normalized : ∀ t, (derive t).entryMark = 0

/-- The closure itself supplies such a derivation. -/
def theDerivation : ClosureDerivation where
  derive := naturalForm
  translated := fun t => ⟨-t.entryMark, rfl⟩
  normalized := naturalForm_entryMark

/-- Every admissible derivation is forced to be the representation-free natural form. -/
theorem ClosureDerivation.derive_eq (D : ClosureDerivation) (t : TemporalClosure) :
    D.derive t = naturalForm t := by
  have hforms : naturalForm t = naturalForm (D.derive t) :=
    (translates_iff_naturalForm_eq.mp (D.translated t))
  rw [naturalForm_eq_self_of_entry_zero (D.normalized t)] at hforms
  exact hforms.symm

theorem closureDerivation_unique (D E : ClosureDerivation) : D = E := by
  cases D with
  | mk d dtranslated dnormalized =>
      cases E with
      | mk e etranslated enormalized =>
          have hde : d = e := by
            funext t
            exact
              (ClosureDerivation.derive_eq ⟨d, dtranslated, dnormalized⟩ t).trans
                (ClosureDerivation.derive_eq ⟨e, etranslated, enormalized⟩ t).symm
          subst hde
          rfl

instance : Subsingleton ClosureDerivation := ⟨closureDerivation_unique⟩

/-! ## Derived trading quantities descend to the natural form -/

@[simp] theorem accumulatedHair_naturalForm (t : TemporalClosure) :
    (naturalForm t).accumulatedHair = t.accumulatedHair :=
  TemporalClosure.accumulatedHair_shift _ _

@[simp] theorem relativePotential_naturalForm (t : TemporalClosure) :
    relativePotential (naturalForm t).entryMark (naturalForm t).exitMark =
      relativePotential t.entryMark t.exitMark :=
  relativePotential_shift _ _ _

@[simp] theorem net_naturalForm (t : TemporalClosure) :
    (naturalForm t).net = t.net :=
  TemporalClosure.net_shift _ _

/-! ## Translational truth of the trading closure -/

/-- A predicate is a translational truth when it is constant on translation orbits. -/
def Translational (P : TemporalClosure → Prop) : Prop :=
  ∀ ⦃t u⦄, Translates t u → (P t ↔ P u)

theorem translational_of_naturalForm
    (P : TemporalClosure → Prop) :
    Translational (fun t => P (naturalForm t)) := by
  intro t u h
  rw [translates_iff_naturalForm_eq] at h
  change P (naturalForm t) ↔ P (naturalForm u)
  rw [h]

theorem profit_translational : Translational (fun t => 0 < t.net) := by
  rintro t u ⟨c, rfl⟩
  change 0 < t.net ↔ 0 < (t.shift c).net
  rw [TemporalClosure.net_shift]

theorem accumulatedHair_translational (k : ℚ) :
    Translational (fun t => t.accumulatedHair = k) := by
  rintro t u ⟨c, rfl⟩
  change t.accumulatedHair = k ↔ (t.shift c).accumulatedHair = k
  rw [TemporalClosure.accumulatedHair_shift]

theorem orbit_truth (t : TemporalClosure) : Translational (fun u => Translates t u) := by
  intro u v huv
  constructor
  · intro htu
    exact translates_trans htu huv
  · intro htv
    exact translates_trans htv (translates_symm huv)

/-- Translational truths recover the closure relation: the logical reading is neither weaker nor
stronger than the orbit. -/
theorem translates_iff_all_translational (t u : TemporalClosure) :
    Translates t u ↔
      ∀ P : TemporalClosure → Prop, Translational P → (P t ↔ P u) := by
  constructor
  · intro h P hP
    exact hP h
  · intro h
    have horbit := h (fun x => Translates t x) (orbit_truth t)
    exact horbit.mp (translates_refl t)

/-! ## Collected integration -/

theorem full_trading_closure
    (D : ClosureDerivation) (t : TemporalClosure) :
    D.derive t = naturalForm t ∧
    (naturalForm t).entryMark = 0 ∧
    (naturalForm t).accumulatedHair = t.accumulatedHair ∧
    (naturalForm t).net = t.net ∧
    (0 < (naturalForm t).net ↔
      (naturalForm t).accumulatedHair <
        (naturalForm t).qty *
          relativePotential (naturalForm t).entryMark (naturalForm t).exitMark) ∧
    (Translates t (naturalForm t)) ∧
    (∀ u, Translates t u ↔ naturalForm t = naturalForm u) :=
  ⟨D.derive_eq t,
    naturalForm_entryMark t,
    accumulatedHair_naturalForm t,
    net_naturalForm t,
    (naturalForm t).profitable_iff_potential_exceeds_hair,
    theDerivation.translated t,
    fun _ => translates_iff_naturalForm_eq⟩

#print axioms NRRFTradingFullClosure.translates_iff_naturalForm_eq
#print axioms NRRFTradingFullClosure.closureDerivation_unique
#print axioms NRRFTradingFullClosure.profit_translational
#print axioms NRRFTradingFullClosure.translates_iff_all_translational
#print axioms NRRFTradingFullClosure.full_trading_closure

end NRRFTradingFullClosure
