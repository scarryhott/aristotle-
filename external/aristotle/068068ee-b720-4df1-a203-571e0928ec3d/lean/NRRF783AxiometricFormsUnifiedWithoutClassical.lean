/-!
# NRRF783 — The full unification of the axiometric forms, without classical logic

This module carries the development's unified system of axiometric forms — the closure equations
of NRRF739/NRRF740 (`encode`/`eval`, the hold, admissibility, the forms, the derivation system,
the fourfold) — through **constructively**: with no excluded middle, no choice, and, at the level
of the file itself, no library at all.  The file has **no `import` line**: nothing but Lean's own
kernel and `Init` is in scope, so no Mathlib definition, instance or lemma can smuggle a classical
principle in.  §9 machine-checks the claim: each headline statement is passed through
`#print axioms` inside `#guard_msgs`, so the build **fails** if `Classical.choice` (or any other
axiom beyond `propext`/`Quot.sound`, the two non-classical axioms behind function
extensionality and propositional rewriting) ever enters a proof.

## What "not needing classical" means here, precisely

Three separate things, all proved below.

1. **No classical axiom is used.**  Every theorem's axiom set is either empty or `[Quot.sound]`
   (function extensionality) / `[propext, Quot.sound]`.  `Classical.choice` never appears (§9).

2. **The choice that a classical treatment would need is already part of the datum.**  An
   axiometric form is not "a surjection`" (whose section must be chosen); it is a *pair* — the
   section is given.  So the fibre of `eval` over each `a` is inhabited *as data*
   (`Closure.fibre`), a whole family of forms can be sectioned at once (`familySection`), and the
   choice statement over the fibres of a form is a theorem (`form_choice`).  This is why the
   unification never needed choice: the forms carry their own witnesses.

3. **The one classical step in the existing core is removable.**  NRRF739's
   "admission neutrality" theorem — a form admits exactly one admissible encoding iff it closes —
   was proved with excluded middle.  `unique_section_iff_transparent` proves it here with
   `DecidableEq` on the encoded carrier only, and `transparent_stable` shows the closing equation
   is a *stable* proposition whenever equality of readings is stable, so double negation is never
   a gap: nothing classical can be true of a form that is not already constructively true of it.

## The system (unchanged from NRRF740, restated constructively)

For `encode : A → B` (recursion, the self-limit that returns) and `eval : B → A` (fixed, the
inversion that holds), with `hold = encode ∘ eval`:

```
(U1)  eval ∘ encode = id_A          the return equation      -- the only postulate
(U2)  hold ∘ hold  = hold           the holding equation     -- derived, never postulated
(U3)  encode ∘ eval = id_B          the closing equation     -- may fail; its failure is the level
```

* §1 the equations, and the readings of `(U3)`;
* §2 admissible pairs are exactly the forms, and the forms are exactly the idempotents;
* §3 one rule — the source form — already generates every solution;
* §4 the derivation system: every derivation is admissible by construction;
* §5 the fourfold (point, line, loop, twist) separated by `(U3)` alone, by `decide`-level facts;
* §6 the constructive readings of `(U3)`, including the de-classicalised neutrality theorem;
* §7 choice is not needed: the form supplies the section;
* §8 `nrrf783_unification`, the whole unification in one statement;
* §9 the machine-checked axiom audit.
-/

namespace NRRF783

universe u v w

/-! ## §1  The unified closure equations -/

/-- An **axiometric form** (a *closure* of `A` in `B`): an encoding — the recursion side, the
self-limit that returns — and an evaluation — the fixed side, the inversion that holds — subject
to the single equation `(U1)`.  Nothing else is postulated. -/
structure Closure (A : Type u) (B : Type v) where
  /-- The recursion side. -/
  encode : A → B
  /-- The fixed side. -/
  eval : B → A
  /-- `(U1)`, the return equation, the one postulate. -/
  eval_encode : ∀ a, eval (encode a) = a

namespace Closure

variable {A : Type u} {B : Type v} {C : Type w}

/-- The **hold** of a form: evaluate, then encode again. -/
def hold (c : Closure A B) : B → B := fun b => c.encode (c.eval b)

theorem hold_apply (c : Closure A B) (b : B) : c.hold b = c.encode (c.eval b) := rfl

theorem encode_injective (c : Closure A B) : Function.Injective c.encode := by
  intro a₁ a₂ h
  rw [← c.eval_encode a₁, ← c.eval_encode a₂, h]

theorem eval_surjective (c : Closure A B) : Function.Surjective c.eval :=
  fun a => ⟨c.encode a, c.eval_encode a⟩

theorem hold_idem_apply (c : Closure A B) (b : B) : c.hold (c.hold b) = c.hold b := by
  show c.encode (c.eval (c.encode (c.eval b))) = c.encode (c.eval b)
  rw [c.eval_encode]

theorem hold_encode (c : Closure A B) (a : A) : c.hold (c.encode a) = c.encode a :=
  congrArg c.encode (c.eval_encode a)

/-- **Transparency**: the hold is the identity, pointwise. -/
def Transparent (c : Closure A B) : Prop := ∀ b, c.hold b = b

/-- Forms compose: `comp c d` encodes through `c` then `d`. -/
def comp (c : Closure A B) (d : Closure B C) : Closure A C where
  encode := fun a => d.encode (c.encode a)
  eval := fun x => c.eval (d.eval x)
  eval_encode := fun a => by
    show c.eval (d.eval (d.encode (c.encode a))) = a
    rw [d.eval_encode, c.eval_encode]

end Closure

open Closure

variable {A : Type u} {B : Type v} {C : Type w}

/-- **(U1)** written as an equation of maps. -/
theorem unified_return (c : Closure A B) : c.eval ∘ c.encode = id :=
  funext c.eval_encode

/-- **(U2)**, the holding equation.  It is *derived* from `(U1)`, not postulated. -/
theorem unified_hold_idem (c : Closure A B) : c.hold ∘ c.hold = c.hold :=
  funext c.hold_idem_apply

/-- **(U3)**, the closing equation: the one equation of the system that may fail. -/
def Closes (c : Closure A B) : Prop := c.encode ∘ c.eval = id

theorem hold_eq_encode_comp_eval (c : Closure A B) : c.hold = c.encode ∘ c.eval := rfl

theorem closes_iff_transparent (c : Closure A B) : Closes c ↔ c.Transparent :=
  ⟨fun h b => congrFun h b, fun h => funext h⟩

/-! ## §2  Admissible pairs, and the completeness of the form -/

/-- A pair of translations is **admissible** when it solves the return equation `(U1)`. -/
def Admissible (e : A → B) (v : B → A) : Prop := ∀ a, v (e a) = a

/-- Admissible pairs are exactly the forms: the equation *is* the object. -/
theorem admissible_iff_closure (e : A → B) (v : B → A) :
    Admissible e v ↔ ∃ c : Closure A B, c.encode = e ∧ c.eval = v :=
  ⟨fun h => ⟨⟨e, v, h⟩, rfl, rfl⟩, fun ⟨c, he, hv⟩ a => by
    subst he; subst hv; exact c.eval_encode a⟩

/-- The identity form on `A`. -/
def idForm (A : Type u) : Closure A A := ⟨id, id, fun _ => rfl⟩

theorem idForm_transparent (A : Type u) : (idForm A).Transparent := fun _ => rfl

/-- The carrier of the form attached to an idempotent translation: its fixed readings. -/
structure Fixed (h : B → B) where
  /-- The reading. -/
  val : B
  /-- It is fixed by `h`. -/
  fixed : h val = val

/-- **Every idempotent translation is the hold of a form**, built constructively from the
idempotent itself: no choice of representatives is made, the fixed readings *are* the carrier. -/
def idemForm (h : B → B) (hh : ∀ b, h (h b) = h b) : Closure (Fixed h) B where
  encode := Fixed.val
  eval := fun b => ⟨h b, hh b⟩
  eval_encode := fun a => by
    cases a with
    | mk b hb => simp only [hb]

theorem idemForm_hold (h : B → B) (hh : ∀ b, h (h b) = h b) : (idemForm h hh).hold = h := rfl

/-- **The forms of the equation system are exactly the idempotent translations.**  A translation of
`B` is the hold of some solution precisely when it is idempotent; the system admits nothing else,
and the witnessing form is produced, not chosen. -/
theorem forms_are_exactly_idempotents (h : B → B) :
    (∃ (A' : Type v) (c : Closure A' B), c.hold = h) ↔ ∀ b, h (h b) = h b := by
  constructor
  · rintro ⟨A', c, rfl⟩
    exact c.hold_idem_apply
  · intro hh
    exact ⟨Fixed h, idemForm h hh, idemForm_hold h hh⟩

/-! ## §3  One rule generates every solution: the source form -/

/-- A **source of existence** for a reading `r : B → A`: a section of `r`. -/
structure Source (r : B → A) where
  /-- The section. -/
  sec : A → B
  /-- Reading the section returns the datum. -/
  ret : ∀ a, r (sec a) = a

/-- The form determined by a source of existence. -/
def ofSource {r : B → A} (S : Source r) : Closure A B := ⟨S.sec, r, S.ret⟩

/-- Every form is a source of existence for its own evaluation. -/
def toSource (c : Closure A B) : Source c.eval := ⟨c.encode, c.eval_encode⟩

theorem ofSource_toSource (c : Closure A B) : ofSource (toSource c) = c := rfl

theorem toSource_ofSource {r : B → A} (S : Source r) : toSource (ofSource S) = S := rfl

/-- The return through the source *is* the hold. -/
theorem ret_eq_hold {r : B → A} (S : Source r) : (fun b => S.sec (r b)) = (ofSource S).hold := rfl

/-- **A single rule already generates every solution**: every form is the source form of the
reading given by its own evaluation. -/
theorem source_rule_complete (c : Closure A B) :
    ∃ (r : B → A) (S : Source r), ofSource S = c :=
  ⟨c.eval, toSource c, rfl⟩

/-! ## §4  Admissible derivations -/

/-- The derivation system of the axiometric forms.  Its rules are the ways the development
actually builds forms: the identity, a source of existence, the fold along an idempotent, and
composition.  There is no rule that appeals to a choice principle. -/
inductive Deriv : Type → Type → Type 1
  /-- The identity form. -/
  | idn (A : Type) : Deriv A A
  /-- The source form of a reading with a section. -/
  | src {A B : Type} (r : B → A) (S : Source r) : Deriv A B
  /-- The fold along an idempotent translation. -/
  | fold {B : Type} (h : B → B) (hh : ∀ b, h (h b) = h b) : Deriv (Fixed h) B
  /-- Composition of derivations. -/
  | comp {A B C : Type} : Deriv A B → Deriv B C → Deriv A C

/-- Every derivation realizes a form. -/
def Deriv.realize : {A B : Type} → Deriv A B → Closure A B
  | _, _, .idn A => idForm A
  | _, _, .src _ S => ofSource S
  | _, _, .fold h hh => idemForm h hh
  | _, _, .comp d e => Closure.comp d.realize e.realize

@[simp] theorem realize_idn (A : Type) : (Deriv.idn A).realize = idForm A := rfl

@[simp] theorem realize_src {A B : Type} (r : B → A) (S : Source r) :
    (Deriv.src r S).realize = ofSource S := rfl

@[simp] theorem realize_fold {B : Type} (h : B → B) (hh : ∀ b, h (h b) = h b) :
    (Deriv.fold h hh).realize = idemForm h hh := rfl

@[simp] theorem realize_comp {A B C : Type} (d : Deriv A B) (e : Deriv B C) :
    (Deriv.comp d e).realize = Closure.comp d.realize e.realize := rfl

/-- **Every derivation is admissible**, by construction rather than by inspection: the return
equation is preserved by every rule. -/
theorem deriv_admissible {A B : Type} (d : Deriv A B) :
    Admissible (d.realize).encode (d.realize).eval :=
  (d.realize).eval_encode

theorem deriv_hold_idem {A B : Type} (d : Deriv A B) :
    (d.realize).hold ∘ (d.realize).hold = (d.realize).hold :=
  unified_hold_idem _

/-- Closing is preserved by composition of derivations. -/
theorem deriv_closes_comp {A B C : Type} (d : Deriv A B) (e : Deriv B C)
    (hd : Closes d.realize) (he : Closes e.realize) : Closes (Deriv.comp d e).realize := by
  rw [closes_iff_transparent] at hd he ⊢
  intro x
  show e.realize.encode (d.realize.encode (d.realize.eval (e.realize.eval x))) = x
  have h1 : d.realize.encode (d.realize.eval (e.realize.eval x)) = e.realize.eval x :=
    hd (e.realize.eval x)
  rw [h1]
  exact he x

/-! ## §5  The fourfold, separated by the closing equation alone -/

/-- **Point**: the identity form on a one-element carrier. -/
def pointForm : Closure Unit Unit := idForm Unit

/-- **Line**: the identity form on the line of readings. -/
def lineForm : Closure Nat Nat := idForm Nat

/-- **Loop**: a form that reads a two-valued carrier through a point.  It solves `(U1)` and fails
`(U3)`; the failure is exhibited by an explicit reading, not by excluded middle. -/
def loopForm : Closure Unit Bool where
  encode := fun _ => true
  eval := fun _ => ()
  eval_encode := fun _ => rfl

/-- **Twist**: the shift form on the line.  It solves `(U1)` and fails `(U3)` at the origin. -/
def twistForm : Closure Nat Nat where
  encode := Nat.succ
  eval := Nat.pred
  eval_encode := fun _ => rfl

theorem pointForm_closes : Closes pointForm := funext fun _ => rfl

theorem lineForm_closes : Closes lineForm := funext fun _ => rfl

theorem loopForm_not_closes : ¬ Closes loopForm := by
  intro h
  have : true = false := congrFun h false
  exact Bool.noConfusion this

theorem twistForm_not_closes : ¬ Closes twistForm := by
  intro h
  have : Nat.succ (Nat.pred 0) = 0 := congrFun h 0
  exact Nat.noConfusion this

/-- **The fourfold is separated inside the one equation system, by the closing equation alone** —
and the separation is witnessed by explicit readings (`false`, `0`), so it survives without
excluded middle. -/
theorem fourfold_by_closing :
    Closes pointForm ∧ Closes lineForm ∧ ¬ Closes loopForm ∧ ¬ Closes twistForm :=
  ⟨pointForm_closes, lineForm_closes, loopForm_not_closes, twistForm_not_closes⟩

/-! ## §6  The readings of the closing equation, constructively -/

/-- An **admissible encoding** for a form: any translation `A → B` that the evaluation undoes. -/
def IsSection (c : Closure A B) (e : A → B) : Prop := ∀ a, c.eval (e a) = a

theorem isSection_encode (c : Closure A B) : IsSection c c.encode := c.eval_encode

theorem closes_iff_encode_bijective (c : Closure A B) :
    Closes c ↔ Function.Injective c.encode ∧ Function.Surjective c.encode := by
  rw [closes_iff_transparent]
  constructor
  · intro h
    exact ⟨c.encode_injective, fun b => ⟨c.eval b, h b⟩⟩
  · rintro ⟨-, hs⟩ b
    obtain ⟨a, ha⟩ := hs b
    rw [← ha]
    exact c.hold_encode a

theorem closes_iff_eval_injective (c : Closure A B) :
    Closes c ↔ Function.Injective c.eval := by
  rw [closes_iff_transparent]
  constructor
  · intro h b₁ b₂ hb
    rw [← h b₁, ← h b₂, hold_apply, hold_apply, hb]
  · intro h b
    exact h (c.eval_encode (c.eval b))

/-- **Admission neutrality, de-classicalised.**  NRRF739 proved this with excluded middle; here
the only extra ingredient is decidable equality of the encoded readings, which is *data* about the
carrier, not a logical principle.  A form admits exactly one admissible encoding iff it closes;
otherwise the admissible encodings are genuinely plural, and the plurality is exhibited by an
explicit competing encoding rather than inferred from a contradiction. -/
theorem unique_section_iff_transparent [DecidableEq A] (c : Closure A B) :
    (∀ e, IsSection c e → e = c.encode) ↔ Closes c := by
  rw [closes_iff_transparent]
  constructor
  · intro h b
    -- the competing encoding: send `eval b` to `b`, and read everything else as before
    have hsec : IsSection c (fun a => if a = c.eval b then b else c.encode a) := by
      intro a
      by_cases ha : a = c.eval b
      · show c.eval (if a = c.eval b then b else c.encode a) = a
        rw [if_pos ha]
        exact ha.symm
      · show c.eval (if a = c.eval b then b else c.encode a) = a
        rw [if_neg ha]
        exact c.eval_encode a
    have hEq := h _ hsec
    have h1 : (fun a => if a = c.eval b then b else c.encode a) (c.eval b) = b := by
      show (if c.eval b = c.eval b then b else c.encode (c.eval b)) = b
      rw [if_pos rfl]
    rw [hEq] at h1
    exact h1
  · intro h e hsec
    funext a
    have hb : c.encode (c.eval (e a)) = e a := h (e a)
    rw [hsec a] at hb
    exact hb.symm

/-- The **defect** of a form: its readings that the hold moves.  This replaces the finite-carrier
"level" of NRRF739 by a finiteness-free object, so the level-zero reading of `(U3)` needs no
cardinal arithmetic and no decidability. -/
structure Defect (c : Closure A B) where
  /-- The moved reading. -/
  val : B
  /-- It is moved. -/
  moved : c.hold val ≠ val

/-- One half of the level-zero reading of `(U3)`, unconditionally: a closing form has no defect. -/
theorem defect_empty_of_closes (c : Closure A B) (h : Closes c) : Defect c → False :=
  fun d => d.moved ((closes_iff_transparent c).mp h d.val)

/-- **The level-zero reading of `(U3)`**: a form closes exactly when its defect is empty.  The
converse half is *not* constructively free — "no reading is moved" is a negative statement — but
it needs only stability of equality of readings, not excluded middle; on a carrier with decidable
equality the hypothesis is discharged by `stable_of_decidableEq`. -/
theorem closes_iff_defect_empty (c : Closure A B) (hst : ∀ x y : B, ¬¬(x = y) → x = y) :
    Closes c ↔ (Defect c → False) := by
  constructor
  · exact defect_empty_of_closes c
  · intro h
    rw [closes_iff_transparent]
    intro b
    exact hst _ _ (fun hb => h ⟨b, hb⟩)

/-- **Stability of the closing equation.**  Whenever equality of readings is stable — in
particular whenever the carrier has decidable equality — a form that is *not not* closing is
closing.  So passing to classical logic proves nothing new about closing: there is no
double-negation gap for the axiometric forms. -/
theorem transparent_stable (c : Closure A B) (hst : ∀ x y : B, ¬¬(x = y) → x = y) :
    ¬¬ c.Transparent → c.Transparent := by
  intro hnn b
  refine hst _ _ (fun hb => hnn (fun hT => hb (hT b)))

theorem stable_of_decidableEq [DecidableEq B] (x y : B) (h : ¬¬(x = y)) : x = y :=
  match (inferInstance : Decidable (x = y)) with
  | isTrue hx => hx
  | isFalse hx => absurd hx h

/-- Corollary: on a carrier with decidable equality, closing is stable. -/
theorem closes_stable_of_decidableEq [DecidableEq B] (c : Closure A B) :
    ¬¬ Closes c → Closes c := by
  intro hnn
  rw [closes_iff_transparent]
  refine transparent_stable c (stable_of_decidableEq) ?_
  intro hT
  exact hnn (fun hc => hT ((closes_iff_transparent c).mp hc))

/-! ## §7  Choice is not needed: the form supplies the section -/

/-- **The fibre witness.**  For every datum `a`, an *actual element* of the fibre of the evaluation
over `a` is produced from the form itself.  A classical treatment would have to choose this
element from a mere surjectivity statement; the axiometric datum contains it. -/
def Closure.fibre (c : Closure A B) (a : A) : {b : B // c.eval b = a} :=
  ⟨c.encode a, c.eval_encode a⟩

theorem Closure.fibre_val (c : Closure A B) (a : A) : (c.fibre a).val = c.encode a := rfl

/-- The same for a bare admissible pair. -/
def fibreOfAdmissible {e : A → B} {v : B → A} (h : Admissible e v) (a : A) : {b : B // v b = a} :=
  ⟨e a, h a⟩

/-- **Simultaneous sectioning of a whole family of forms**, with no choice principle: the
`I`-indexed choice that the classical argument would need is performed by the encodings. -/
def familySection {I : Type u} {A B : I → Type v} (c : ∀ i, Closure (A i) (B i))
    (a : ∀ i, A i) : ∀ i, {b : B i // (c i).eval b = a i} :=
  fun i => (c i).fibre (a i)

/-- **Choice over the fibres of an axiometric form is a theorem, not an axiom.**  Any property that
holds of the encoded reading of each datum is realized by a genuine section, and the section is
the encoding itself. -/
theorem form_choice (c : Closure A B) (R : A → B → Prop) (h : ∀ a, R a (c.encode a)) :
    ∃ g : A → B, (∀ a, c.eval (g a) = a) ∧ ∀ a, R a (g a) :=
  ⟨c.encode, c.eval_encode, h⟩

/-- The dependent, data-level form of the same statement. -/
def form_choice_data {A B : Type u} (c : Closure A B) (F : A → B → Type v)
    (h : ∀ a, F a (c.encode a)) :
    Σ' g : A → B, PProd (∀ a, c.eval (g a) = a) (∀ a, F a (g a)) :=
  ⟨c.encode, ⟨c.eval_encode, h⟩⟩

/-! ## §8  The unification -/

/-- **The full unification of the axiometric forms, constructively.**

1. Every solution satisfies the return equation `(U1)` and the derived holding equation `(U2)`,
   while the closing equation `(U3)` is exactly transparency, exactly bijectivity of the encoding,
   exactly injectivity of the evaluation, and exactly emptiness of the defect.
2. The forms of the system are exactly the idempotent translations, and the witnessing form is
   constructed from the idempotent.
3. One rule — the source form — already generates every solution.
4. Every derivation of the system is admissible, by construction.
5. The choice a classical treatment would need is supplied by the form itself.
6. Closing is a stable proposition on carriers with decidable equality, so classical logic proves
   nothing further about it.

No step of this uses excluded middle or choice; §9 checks that mechanically. -/
theorem nrrf783_unification {A B : Type} [DecidableEq A] [DecidableEq B]
    (c : Closure A B) (h : B → B) (hh : ∀ b, h (h b) = h b) (d : Deriv A B) :
    (c.eval ∘ c.encode = id ∧ c.hold ∘ c.hold = c.hold) ∧
    (Closes c ↔ c.Transparent) ∧
    (Closes c ↔ Function.Injective c.encode ∧ Function.Surjective c.encode) ∧
    (Closes c ↔ Function.Injective c.eval) ∧
    (Closes c ↔ (Defect c → False)) ∧
    ((∀ e, IsSection c e → e = c.encode) ↔ Closes c) ∧
    (∃ (A' : Type) (c' : Closure A' B), c'.hold = h) ∧
    (∃ (r : B → A) (S : Source r), ofSource S = c) ∧
    Admissible (d.realize).encode (d.realize).eval ∧
    (∀ a : A, c.eval ((c.fibre a).val) = a) ∧
    (¬¬ Closes c → Closes c) := by
  refine ⟨⟨unified_return c, unified_hold_idem c⟩, closes_iff_transparent c,
    closes_iff_encode_bijective c, closes_iff_eval_injective c,
    closes_iff_defect_empty c stable_of_decidableEq,
    unique_section_iff_transparent c, (forms_are_exactly_idempotents h).mpr hh,
    source_rule_complete c, deriv_admissible d, fun a => (c.fibre a).property,
    closes_stable_of_decidableEq c⟩

end NRRF783

/-! ## §9  Axiom audit — machine-checked

Each `#guard_msgs` below fixes the *exact* axiom list of the statement.  Only `propext` and
`Quot.sound` — function extensionality and propositional rewriting, neither of them a classical
principle — ever occur; `Classical.choice` occurs nowhere, and the build fails if it ever does. -/

section Audit

/-- info: 'NRRF783.Closure.hold_idem_apply' does not depend on any axioms -/
#guard_msgs in #print axioms NRRF783.Closure.hold_idem_apply

/-- info: 'NRRF783.unified_return' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms NRRF783.unified_return

/-- info: 'NRRF783.unified_hold_idem' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms NRRF783.unified_hold_idem

/-- info: 'NRRF783.closes_iff_transparent' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms NRRF783.closes_iff_transparent

/-- info: 'NRRF783.admissible_iff_closure' does not depend on any axioms -/
#guard_msgs in #print axioms NRRF783.admissible_iff_closure

/-- info: 'NRRF783.forms_are_exactly_idempotents' depends on axioms: [propext] -/
#guard_msgs in #print axioms NRRF783.forms_are_exactly_idempotents

/-- info: 'NRRF783.source_rule_complete' does not depend on any axioms -/
#guard_msgs in #print axioms NRRF783.source_rule_complete

/-- info: 'NRRF783.deriv_admissible' depends on axioms: [propext] -/
#guard_msgs in #print axioms NRRF783.deriv_admissible

/-- info: 'NRRF783.deriv_closes_comp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms NRRF783.deriv_closes_comp

/-- info: 'NRRF783.fourfold_by_closing' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms NRRF783.fourfold_by_closing

/-- info: 'NRRF783.closes_iff_encode_bijective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms NRRF783.closes_iff_encode_bijective

/-- info: 'NRRF783.closes_iff_eval_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms NRRF783.closes_iff_eval_injective

/-- info: 'NRRF783.unique_section_iff_transparent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms NRRF783.unique_section_iff_transparent

/-- info: 'NRRF783.closes_iff_defect_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms NRRF783.closes_iff_defect_empty

/-- info: 'NRRF783.transparent_stable' does not depend on any axioms -/
#guard_msgs in #print axioms NRRF783.transparent_stable

/-- info: 'NRRF783.closes_stable_of_decidableEq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms NRRF783.closes_stable_of_decidableEq

/-- info: 'NRRF783.form_choice' does not depend on any axioms -/
#guard_msgs in #print axioms NRRF783.form_choice

/-- info: 'NRRF783.familySection' does not depend on any axioms -/
#guard_msgs in #print axioms NRRF783.familySection

/-- info: 'NRRF783.nrrf783_unification' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms NRRF783.nrrf783_unification

end Audit
