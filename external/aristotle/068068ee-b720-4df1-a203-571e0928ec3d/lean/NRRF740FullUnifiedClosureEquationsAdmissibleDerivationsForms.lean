import Mathlib
import NRRF718ContinuumPerspectiveRelativeGoalsQuantumGravityReturn
import NRRF723PhysicalConsciousnessFieldIdentificationRelativeNotStrictDiagonal
import NRRF725ReunifiedClosureSourceOfExistenceTruthTopology
import NRRF728ReunifiedFullIntendedOperations
import NRRF739LoopSensorClosureFourfoldTopologyFusionLevel

/-!
# NRRF740 — The full unified closure equations, their admissible derivations, and their forms

The complaint answered here is that the development's own **unified closure equations** — the
equations every earlier module has in fact been solving — were not being carried through all the
material as *one* system with *one* notion of admissible derivation and *one* stock of forms.  This
module states the system once and shows that the vocabulary used across the documents is that one
system read in different places.

## §1  The equations

For a pair of translations `encode : A → B` (recursion, the self-limit that returns) and
`eval : B → A` (fixed, the inversion that holds), with `hold = encode ∘ eval`:

```
(U1)  eval ∘ encode = id_A          the return equation
(U2)  hold ∘ hold  = hold           the holding equation
(U3)  encode ∘ eval = id_B          the closing equation
```

`(U1)` is the whole content of a closure (`NRRF739.Closure`); `(U2)` is *derived* from it, never
postulated (`unified_hold_idem`); `(U3)` is the one equation that may fail, and its failure is the
closure's level.  `unified_closing_readings` proves that on finite carriers the closing equation,
transparency, bijectivity of the encoding, uniqueness of the admissible encoding, and vanishing of
the level are one and the same statement — five readings of `(U3)`.

## §2  Admissible pairs and the completeness of the form

`Admissible e v` is `(U1)` written for a bare pair of maps.  `admissible_iff_closure` : admissible
pairs are exactly the closures.  `forms_are_exactly_idempotents` : the maps `B → B` arising as the
hold of *some* solution are exactly the idempotent maps — the equation system has no other forms.
`source_rule_complete` : every solution is the *source form* of §3, so a single derivation rule
already generates all of them.

## §3  The forms already in the documents are solutions of the same equations

* **Reading with a source of existence** (NRRF723/NRRF725).  `ofSource` turns a source of existence
  into a closure and `ret_eq_hold` shows the return through the source *is* the hold.  `toSource`
  goes back and `ofSource_toSource` is an identity: the two vocabularies are one.
* **Saturation** (NRRF725/NRRF728).  `satClosure r` is the closure whose encoded part is exactly
  the saturated sets (`sat_fixed_iff_saturated`) and whose hold is exactly the reunified operation
  `sat r` (`satClosure_hold`).  So NRRF728's unique intended operation is the hold of a solution of
  the same equations, and it closes (`(U3)`) exactly when the reading is injective
  (`satClosure_transparent_iff_injective`).
* **Relations and motions** (NRRF728).  For any closure the relative diagonal of its evaluation is
  the kernel of its hold (`relDiag_eval_eq_ker_hold`), its neutral field is the field of motions
  the hold cannot see (`neutralField_eval_eq`), and NRRF728's collections of intended operations,
  relations and fields are singletons determined by the hold (`intended_levels_of_closure`).
* **The fourfold** (NRRF739).  Point, line, loop and closure are the identity form, the identity
  form on the line, the loop form and a non-closing form; they are separated inside the one system
  by `(U3)` and by the level.

## §4  Admissible derivations

`Deriv` is the inductive derivation system whose rules are exactly the forms the documents use:
identity, source, saturation (fold), loop, twist, and composition.  `Deriv.realize` sends a
derivation to a closure, so **every derivation is admissible** (`deriv_admissible`): the equations
are preserved by every rule, by construction rather than by inspection.  Levels add along a
derivation (`deriv_level_comp`), closing is preserved by composition (`deriv_closes_comp`), and the
concrete objects of NRRF739 are literally realizations of derivations
(`realize_lineDeriv`, `realize_loopDeriv`, `realize_twistDeriv`, `realize_fusionLoopDeriv`).

`nrrf740_answer` collects the headline statements.
-/

namespace NRRF740

open NRRF739 NRRF739.Closure

universe u v w

/-! ## §1  The unified closure equations -/

section Equations

variable {A : Type u} {B : Type v} {C : Type w}

/-- **(U1)**, the return equation, written as an equation of maps.  This is the single equation a
closure is required to satisfy. -/
theorem unified_return (c : Closure A B) : c.eval ∘ c.encode = id :=
  funext c.eval_encode

/-- **(U2)**, the holding equation.  It is *derived* from `(U1)`, not postulated. -/
theorem unified_hold_idem (c : Closure A B) : c.hold ∘ c.hold = c.hold :=
  funext (fun b => c.hold_idem b)

/-- **(U3)**, the closing equation: the half of the double inverse that a closure does *not*
demand. -/
def Closes (c : Closure A B) : Prop := c.encode ∘ c.eval = id

/-- The closing equation is transparency. -/
theorem closes_iff_transparent (c : Closure A B) : Closes c ↔ c.Transparent := by
  constructor
  · intro h b; exact congrFun h b
  · intro h; exact funext h

/-- The hold is the left-hand side of the closing equation. -/
theorem hold_eq_encode_comp_eval (c : Closure A B) : c.hold = c.encode ∘ c.eval := rfl

/-- **The closing equation has five equivalent readings.**  On finite carriers, `(U3)` holds iff the
closure is transparent, iff its encoding is a bijection, iff its evaluation is injective, iff it
admits exactly one admissible encoding, iff its level is zero. -/
theorem unified_closing_readings (c : Closure A B) [Fintype A] [Fintype B] :
    (Closes c ↔ c.Transparent) ∧
    (Closes c ↔ Function.Bijective c.encode) ∧
    (Closes c ↔ Function.Injective c.eval) ∧
    (Closes c ↔ ∀ e : A → B, c.IsSection e → e = c.encode) ∧
    (Closes c ↔ c.level = 0) := by
  have h := closes_iff_transparent c
  refine ⟨h, ?_, ?_, ?_, ?_⟩
  · rw [h]; exact c.transparent_iff_bijective
  · rw [h]; exact c.transparent_iff_eval_injective
  · rw [h]; exact (c.unique_section_iff_transparent).symm
  · rw [h]; exact (c.level_eq_zero_iff_transparent).symm

end Equations

/-! ## §2  Admissible pairs, and the completeness of the form -/

section Admissible

variable {A : Type u} {B : Type v}

/-- A pair of translations is **admissible** when it solves the return equation `(U1)`. -/
def Admissible (e : A → B) (v : B → A) : Prop := ∀ a, v (e a) = a

/-- Admissible pairs are exactly the closures: the equation *is* the object. -/
theorem admissible_iff_closure (e : A → B) (v : B → A) :
    Admissible e v ↔ ∃ c : Closure A B, c.encode = e ∧ c.eval = v := by
  constructor
  · intro h; exact ⟨⟨e, v, h⟩, rfl, rfl⟩
  · rintro ⟨c, rfl, rfl⟩; exact c.eval_encode

/-- The closure attached to an admissible pair. -/
def ofAdmissible {e : A → B} {v : B → A} (h : Admissible e v) : Closure A B := ⟨e, v, h⟩

/-- The identity form: the closure that closes at once. -/
def idClosure (A : Type u) : Closure A A := ⟨id, id, fun _ => rfl⟩

theorem idClosure_transparent (A : Type u) : (idClosure A).Transparent := fun _ => rfl

/-- Every idempotent map is the hold of a solution: the solution on its own fixed points. -/
def idemClosure (h : B → B) (hh : ∀ b, h (h b) = h b) : Closure {b : B // h b = b} B where
  encode := Subtype.val
  eval := fun b => ⟨h b, hh b⟩
  eval_encode := by rintro ⟨b, hb⟩; exact Subtype.ext hb

@[simp] theorem idemClosure_hold (h : B → B) (hh : ∀ b, h (h b) = h b) :
    (idemClosure h hh).hold = h := rfl

/-- **The forms of the equation system are exactly the idempotent forms.**  A translation of `B` is
the hold of some solution precisely when it is idempotent; the system admits nothing else, and
excludes nothing idempotent. -/
theorem forms_are_exactly_idempotents (h : B → B) :
    (∃ (A : Type v) (c : Closure A B), c.hold = h) ↔ ∀ b, h (h b) = h b := by
  constructor
  · rintro ⟨A, c, rfl⟩; exact fun b => c.hold_idem b
  · intro hh; exact ⟨_, idemClosure h hh, rfl⟩

end Admissible

/-! ## §3  The documents' forms are solutions of the same equations -/

section Source

open NRRF723 NRRF725

variable {X S : Type u}

/-- A **source of existence** for a reading (NRRF723) is a solution of the unified equations: the
source is the encoding and the reading is the evaluation. -/
def ofSource {r : X → S} (E : SourceOfExistence r) : Closure S X :=
  ⟨E.src, r, E.returns⟩

/-- Conversely every solution is a reading with a source. -/
def toSource (c : Closure S X) : SourceOfExistence c.eval := ⟨c.encode, c.eval_encode⟩

/-- The two vocabularies are literally the same datum. -/
theorem ofSource_toSource (c : Closure S X) : ofSource (toSource c) = c := rfl

theorem toSource_ofSource {r : X → S} (E : SourceOfExistence r) :
    toSource (ofSource E) = E := rfl

/-- **The return through the source of existence is the hold.**  NRRF725's `ret` and NRRF739's
`hold` are one operation. -/
theorem ret_eq_hold {r : X → S} (E : SourceOfExistence r) :
    ret r E = (ofSource E).hold := rfl

/-- Hence NRRF725's idempotence of the return is the holding equation `(U2)`. -/
theorem ret_idem_is_U2 {r : X → S} (E : SourceOfExistence r) :
    (ret r E ∘ ret r E) = ret r E :=
  unified_hold_idem (ofSource E)

/-- **A single rule already generates every solution**: every closure is the source form of the
reading given by its own evaluation. -/
theorem source_rule_complete {A : Type u} {B : Type u} (c : Closure A B) :
    ∃ (r : B → A) (E : SourceOfExistence r), ofSource E = c :=
  ⟨c.eval, toSource c, rfl⟩

end Source

section Saturation

open NRRF718 NRRF725

variable {X S : Type u}

/-- A saturated set is a fixed point of the saturation. -/
theorem sat_eq_self_of_saturated {r : X → S} {U : Set X} (hU : Saturated r U) :
    sat r U = U := by
  apply Set.Subset.antisymm
  · rintro x ⟨u, hu, hru⟩
    exact (hU x u hru).2 hu
  · exact subset_sat r U

/-- **The fixed points of the reunified operation are exactly the saturated sets.** -/
theorem sat_fixed_iff_saturated (r : X → S) (U : Set X) :
    sat r U = U ↔ Saturated r U := by
  constructor
  · intro h; rw [← h]; exact sat_saturated r U
  · exact sat_eq_self_of_saturated

/-- The **fold form**: the closure of the saturated sets in all sets, whose hold is the reunified
operation `sat r` of NRRF728. -/
def satClosure (r : X → S) : Closure {U : Set X // Saturated r U} (Set X) where
  encode := Subtype.val
  eval := fun U => ⟨sat r U, sat_saturated r U⟩
  eval_encode := by
    rintro ⟨U, hU⟩
    exact Subtype.ext (sat_eq_self_of_saturated hU)

/-- **NRRF728's unique intended operation is the hold of a solution of the unified equations.** -/
@[simp] theorem satClosure_hold (r : X → S) : (satClosure r).hold = sat r := rfl

/-- The fold form closes exactly when the reading separates occurrences: `(U3)` for saturation is
injectivity of the reading. -/
theorem satClosure_transparent_iff_injective (r : X → S) :
    (satClosure r).Transparent ↔ Function.Injective r := by
  constructor
  · intro h x y hxy
    have hU : sat r {x} = {x} := h {x}
    have : y ∈ sat r ({x} : Set X) := ⟨x, rfl, hxy.symm⟩
    rw [hU] at this
    exact this.symm
  · intro h U
    apply sat_eq_self_of_saturated
    intro x y hxy
    rw [h hxy]

end Saturation

section IntendedLevels

open NRRF718 NRRF725 NRRF728

variable {A B : Type}

/-- **The relative diagonal of a closure's reading is the kernel of its hold.** -/
theorem relDiag_eval_eq_ker_hold (c : Closure A B) :
    relDiag c.eval = {p : B × B | c.hold p.1 = c.hold p.2} := by
  ext p
  constructor
  · intro h; exact congrArg c.encode h
  · intro h; exact c.encode_injective h

/-- **The saturation of a closure's reading is the operation of its hold.** -/
theorem sat_eval_eq_hold_preimage_image (c : Closure A B) (U : Set B) :
    sat c.eval U = c.hold ⁻¹' (c.hold '' U) := by
  ext b
  constructor
  · rintro ⟨u, hu, hru⟩
    exact ⟨u, hu, (congrArg c.encode hru).symm⟩
  · rintro ⟨u, hu, hru⟩
    exact ⟨u, hu, (c.encode_injective hru).symm⟩

/-- **The neutral field of a closure's reading is the field of motions its hold cannot see.** -/
theorem neutralField_eval_eq (c : Closure A B) :
    neutralField c.eval = {f : B → B | ∀ b, c.hold (f b) = c.hold b} := by
  ext f
  constructor
  · intro hf b; exact congrArg c.encode (hf b)
  · intro hf b; exact c.encode_injective (hf b)

/-- **All three intended levels of NRRF728 are readings of one closure.**  For the reading carried
by any solution of the unified equations, the collection of intended operations, the collection of
intended relations and the collection of intended fields are one-element collections, and each
element is determined by the hold alone. -/
theorem intended_levels_of_closure (c : Closure A B) :
    intendedOperations c.eval = {sat c.eval} ∧
    intendedRelations c.eval = {fun x y => c.eval x = c.eval y} ∧
    intendedFields c.eval = {neutralField c.eval} ∧
    sat c.eval = (fun U => c.hold ⁻¹' (c.hold '' U)) ∧
    (fun x y => c.eval x = c.eval y) = (fun x y => c.hold x = c.hold y) ∧
    neutralField c.eval = {f : B → B | ∀ b, c.hold (f b) = c.hold b} :=
  ⟨intendedOperations_eq_singleton c.eval, intendedRelations_eq_singleton c.eval,
    intendedFields_eq_singleton c.eval,
    funext (sat_eval_eq_hold_preimage_image c),
    by
      funext x y
      exact propext ⟨fun h => congrArg c.encode h, fun h => c.encode_injective h⟩,
    neutralField_eval_eq c⟩

end IntendedLevels

/-! ## §4  Admissible derivations -/

/-- The **derivation system**: the rules are exactly the forms the documents use to produce a
closure.  A derivation is a *proof that a form is admissible*, and `Deriv.realize` extracts the
solution it names. -/
inductive Deriv : Type → Type → Type 1 where
  /-- the identity form -/
  | idn (A : Type) : Deriv A A
  /-- a reading with a source of existence -/
  | source {X S : Type} {r : X → S} (E : NRRF723.SourceOfExistence r) : Deriv S X
  /-- the fold: the saturated sets inside all sets -/
  | fold {X S : Type} (r : X → S) : Deriv {U : Set X // NRRF718.Saturated r U} (Set X)
  /-- the loop: the line quotiented by a number -/
  | loop (k : ℕ) (hk : NeZero k) : Deriv (ZMod k) ℤ
  /-- the twist: two channels fused by their sum -/
  | twist : Deriv ℤ (ℤ × ℤ)
  /-- composition of derivations -/
  | comp {A B C : Type} : Deriv A B → Deriv B C → Deriv A C

/-- Realization: every derivation names a solution of the unified equations. -/
def Deriv.realize : {A B : Type} → Deriv A B → Closure A B
  | _, _, .idn A => idClosure A
  | _, _, .source E => ofSource E
  | _, _, .fold r => satClosure r
  | _, _, .loop k hk => @lineLoopClosure k hk
  | _, _, .twist => fusionClosure
  | _, _, .comp d e => (d.realize).comp (e.realize)

@[simp] theorem realize_idn (A : Type) : (Deriv.idn A).realize = idClosure A := by
  simp [Deriv.realize]

@[simp] theorem realize_source {X S : Type} {r : X → S} (E : NRRF723.SourceOfExistence r) :
    (Deriv.source E).realize = ofSource E := by
  simp [Deriv.realize]

@[simp] theorem realize_fold {X S : Type} (r : X → S) :
    (Deriv.fold r).realize = satClosure r := by
  simp [Deriv.realize]

@[simp] theorem realize_loop (k : ℕ) (hk : NeZero k) :
    (Deriv.loop k hk).realize = @lineLoopClosure k hk := by
  simp [Deriv.realize]

@[simp] theorem realize_twist : Deriv.twist.realize = fusionClosure := by
  simp [Deriv.realize]

/-- **Every derivation is admissible.**  The return equation `(U1)` is preserved by every rule of
the system — not checked case by case, but carried by the realization itself. -/
theorem deriv_admissible {A B : Type} (d : Deriv A B) :
    Admissible (d.realize).encode (d.realize).eval :=
  (d.realize).eval_encode

/-- Every derivation also satisfies the derived holding equation `(U2)`. -/
theorem deriv_hold_idem {A B : Type} (d : Deriv A B) :
    (d.realize).hold ∘ (d.realize).hold = (d.realize).hold :=
  unified_hold_idem _

@[simp] theorem realize_comp {A B C : Type} (d : Deriv A B) (e : Deriv B C) :
    (Deriv.comp d e).realize = (d.realize).comp (e.realize) := by
  simp [Deriv.realize]

/-- Closing is preserved by composition: a derivation of closing forms closes. -/
theorem deriv_closes_comp {A B C : Type} (d : Deriv A B) (e : Deriv B C)
    (hd : Closes d.realize) (he : Closes e.realize) : Closes (Deriv.comp d e).realize := by
  rw [closes_iff_transparent] at hd he ⊢
  rw [realize_comp]
  exact comp_transparent _ _ hd he

/-- **Levels add along a derivation.** -/
theorem deriv_level_comp {A B C : Type} (d : Deriv A B) (e : Deriv B C)
    [Fintype A] [Fintype B] [Fintype C] :
    (Deriv.comp d e).realize.level = (e.realize).level + (d.realize).level := by
  rw [realize_comp]
  exact level_comp _ _

/-! ### The concrete forms of the documents are derivations -/

/-- The point form. -/
def pointDeriv : Deriv Unit Unit := .idn Unit

/-- The line form: the transparent, perturbatively rigid relation of NRRF739. -/
def lineDeriv : Deriv ℤ ℤ := .idn ℤ

/-- The loop form of period `k`. -/
def loopDeriv (k : ℕ) [hk : NeZero k] : Deriv (ZMod k) ℤ := .loop k hk

/-- The twist form. -/
def twistDeriv : Deriv ℤ (ℤ × ℤ) := .twist

/-- The loop sensor reading the fusion twist: a *derived* form, not a new postulate. -/
def fusionLoopDeriv (k : ℕ) [NeZero k] : Deriv (ZMod k) (ℤ × ℤ) :=
  .comp (loopDeriv k) twistDeriv

@[simp] theorem realize_lineDeriv : lineDeriv.realize = siliconClosure := by
  simp [lineDeriv, idClosure, siliconClosure]

@[simp] theorem realize_loopDeriv (k : ℕ) [NeZero k] :
    (loopDeriv k).realize = lineLoopClosure k := by
  simp [loopDeriv]

@[simp] theorem realize_twistDeriv : twistDeriv.realize = fusionClosure := by
  simp [twistDeriv]

@[simp] theorem realize_fusionLoopDeriv (k : ℕ) [NeZero k] :
    (fusionLoopDeriv k).realize = fusionLoopClosure k := by
  simp [fusionLoopDeriv, fusionLoopClosure]

/-- The point and line forms close; the loop, twist and fused forms do not.  So the fourfold of
NRRF739 is separated *inside the one equation system*, by the closing equation alone. -/
theorem fourfold_by_closing (k : ℕ) [NeZero k] :
    Closes pointDeriv.realize ∧
    Closes lineDeriv.realize ∧
    ¬ Closes (loopDeriv k).realize ∧
    ¬ Closes twistDeriv.realize ∧
    ¬ Closes (fusionLoopDeriv k).realize := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [closes_iff_transparent, pointDeriv, realize_idn]
    exact idClosure_transparent Unit
  · rw [closes_iff_transparent, realize_lineDeriv]
    exact silicon_transparent
  · rw [closes_iff_transparent, realize_loopDeriv]; exact lineLoop_not_transparent k
  · rw [closes_iff_transparent, realize_twistDeriv]; exact fusion_not_transparent
  · rw [closes_iff_transparent, realize_fusionLoopDeriv]
    exact fusionLoopClosure_not_transparent k

/-- The fold form of a reading is a derivation, its hold is NRRF728's unique intended operation,
and it closes exactly when the reading is injective. -/
theorem fold_deriv_is_the_intended_operation {X S : Type} (r : X → S) :
    ((Deriv.fold r).realize).hold = NRRF725.sat r ∧
    (Closes (Deriv.fold r).realize ↔ Function.Injective r) := by
  refine ⟨by rw [realize_fold, satClosure_hold], ?_⟩
  rw [closes_iff_transparent, realize_fold]
  exact satClosure_transparent_iff_injective r

/-! ## §5  The answer -/

/-- **The unified closure equations, their admissible derivations and their forms, in one
statement.**

1. Every solution satisfies the return equation and the derived holding equation, while the closing
   equation is exactly transparency.
2. The forms of the system are exactly the idempotent translations.
3. Every solution is a reading with a source of existence — one rule generates all of them — and
   the return through the source is the hold.
4. The reunified operation, relation and field of NRRF728 are the hold, the kernel of the hold and
   the invisibility field of the hold of a solution.
5. Every derivation of the system is admissible, and levels add along derivations. -/
theorem nrrf740_answer {A B : Type} (c : Closure A B) (r : B → A) (E : NRRF723.SourceOfExistence r)
    (h : B → B) (hh : ∀ b, h (h b) = h b) (d : Deriv A B) :
    (c.eval ∘ c.encode = id ∧ c.hold ∘ c.hold = c.hold ∧ (Closes c ↔ c.Transparent)) ∧
    (∃ (A' : Type) (c' : Closure A' B), c'.hold = h) ∧
    (∃ (r' : B → A) (E' : NRRF723.SourceOfExistence r'), ofSource E' = c) ∧
    NRRF725.ret r E = (ofSource E).hold ∧
    (NRRF728.intendedOperations c.eval = {NRRF725.sat c.eval} ∧
      NRRF718.relDiag c.eval = {p : B × B | c.hold p.1 = c.hold p.2} ∧
      NRRF725.neutralField c.eval = {f : B → B | ∀ b, c.hold (f b) = c.hold b}) ∧
    Admissible (d.realize).encode (d.realize).eval := by
  refine ⟨⟨unified_return c, unified_hold_idem c, closes_iff_transparent c⟩,
    (forms_are_exactly_idempotents h).2 hh, source_rule_complete c, rfl, ?_,
    deriv_admissible d⟩
  exact ⟨NRRF728.intendedOperations_eq_singleton c.eval, relDiag_eval_eq_ker_hold c,
    neutralField_eval_eq c⟩

end NRRF740
