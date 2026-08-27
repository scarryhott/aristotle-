import NRRF740FullUnifiedClosureEquationsAdmissibleDerivationsForms
import NRRF783AxiometricFormsUnifiedWithoutClassical

/-!
# NRRF783b — The constructive unification is the development's own one

`NRRF783AxiometricFormsUnifiedWithoutClassical` carries the unified system of axiometric forms
through with no library at all in scope, hence with no classical principle available.  This module
connects that development to the project's own closure object (`NRRF739.Closure`, the object the
unified equations of NRRF740 are stated for) and shows two things.

## §1–2  It is the same object

`toF739` and `ofF739` are mutually inverse *definitionally*: `NRRF783.Closure` and
`NRRF739.Closure` are the same structure, and hold, transparency, sectioning and the closing
equation `(U3)` agree on the nose (`toF739_hold`, `transparent_iff`, `isSection_iff`,
`closes_iff`).  So nothing was weakened by dropping the library: the constructive development is
about the development's own forms.

## §3  Where classical logic actually entered, and how it is removed

Auditing NRRF740 (see §5) shows that most of the unification was already choice-free:
`unified_return`, `unified_hold_idem`, `closes_iff_transparent`, `admissible_iff_closure`,
`forms_are_exactly_idempotents`, `source_rule_complete` and `deriv_admissible` use only `propext`
and `Quot.sound`.  `Classical.choice` entered at exactly three places, all of them avoidable:

1. **Admission neutrality** (`NRRF739.Closure.unique_section_iff_transparent`) — proved by
   `by_contra`.  `unique_section_iff_transparent_constructive` replaces excluded middle by
   decidable equality of the encoded readings: *data about the carrier, not a logical principle*.
2. **The readings of the closing equation** (`NRRF740.unified_closing_readings`) — inherited the
   above, and used the finite-carrier level.  `unified_closing_readings_constructive` gives all
   five readings with the level replaced by emptiness of the defect, so no finiteness, no
   cardinal arithmetic and no choice.
3. **The fourfold** (`NRRF740.fourfold_by_closing`) — its loop and twist witnesses were built from
   library objects carrying classical instances.  `fourfold_by_closing_constructive` separates
   point, line, loop and twist by explicit moved readings (`false`, `0`) instead.

`nrrf740_answer_without_classical` then restates the headline unification of NRRF740 for
`NRRF739.Closure` and proves it choice-free.  §5 pins every claim with `#guard_msgs`.
-/

namespace NRRF783Bridge

universe u v

open Function

variable {A : Type u} {B : Type v}

/-! ## §1  The two presentations of the axiometric form -/

/-- The constructive form, read as the project's closure object. -/
def toF739 (c : NRRF783.Closure A B) : NRRF739.Closure A B :=
  ⟨c.encode, c.eval, c.eval_encode⟩

/-- The project's closure object, read as a constructive form. -/
def ofF739 (c : NRRF739.Closure A B) : NRRF783.Closure A B :=
  ⟨c.encode, c.eval, c.eval_encode⟩

@[simp] theorem ofF739_toF739 (c : NRRF783.Closure A B) : ofF739 (toF739 c) = c := rfl

@[simp] theorem toF739_ofF739 (c : NRRF739.Closure A B) : toF739 (ofF739 c) = c := rfl

/-! ## §2  Everything agrees on the nose -/

@[simp] theorem toF739_hold (c : NRRF783.Closure A B) :
    (toF739 c).hold = c.hold := rfl

theorem transparent_iff (c : NRRF739.Closure A B) :
    c.Transparent ↔ (ofF739 c).Transparent := Iff.rfl

theorem closes_iff (c : NRRF739.Closure A B) :
    NRRF740.Closes c ↔ NRRF783.Closes (ofF739 c) := Iff.rfl

theorem isSection_iff (c : NRRF739.Closure A B) (e : A → B) :
    c.IsSection e ↔ NRRF783.IsSection (ofF739 c) e := Iff.rfl

/-! ## §3  The classical steps, removed -/

/-- **Admission neutrality without excluded middle.**  NRRF739 proved this with `by_contra`; the
only ingredient needed instead is decidable equality on the encoded carrier.  A form admits exactly
one admissible encoding iff it is transparent — and when it is not, the competing encoding is
written down explicitly. -/
theorem unique_section_iff_transparent_constructive [DecidableEq A] (c : NRRF739.Closure A B) :
    (∀ e, c.IsSection e → e = c.encode) ↔ c.Transparent :=
  (NRRF783.unique_section_iff_transparent (ofF739 c)).trans
    (NRRF783.closes_iff_transparent (ofF739 c))

/-- **The readings of the closing equation, without choice and without finiteness.**  `(U3)` holds
iff the form is transparent, iff its encoding is a bijection, iff its evaluation is injective, iff
it admits exactly one admissible encoding, iff its defect — the readings its hold moves — is
empty.  The last clause replaces NRRF740's finite-carrier level, so no cardinal arithmetic and no
classical instance is involved. -/
theorem unified_closing_readings_constructive [DecidableEq A] [DecidableEq B]
    (c : NRRF739.Closure A B) :
    (NRRF740.Closes c ↔ c.Transparent) ∧
    (NRRF740.Closes c ↔ Bijective c.encode) ∧
    (NRRF740.Closes c ↔ Injective c.eval) ∧
    (NRRF740.Closes c ↔ ∀ e : A → B, c.IsSection e → e = c.encode) ∧
    (NRRF740.Closes c ↔ (NRRF783.Defect (ofF739 c) → False)) := by
  refine ⟨NRRF740.closes_iff_transparent c, ?_,
    NRRF783.closes_iff_eval_injective (ofF739 c), ?_, ?_⟩
  · exact (NRRF783.closes_iff_encode_bijective (ofF739 c)).trans
      ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
  · exact (NRRF740.closes_iff_transparent c).trans
      (unique_section_iff_transparent_constructive c).symm
  · exact NRRF783.closes_iff_defect_empty (ofF739 c) NRRF783.stable_of_decidableEq

/-- The fourfold as closure objects of the project. -/
def pointF739 : NRRF739.Closure Unit Unit := toF739 NRRF783.pointForm

/-- The line form, as a closure object of the project. -/
def lineF739 : NRRF739.Closure Nat Nat := toF739 NRRF783.lineForm

/-- The loop form, as a closure object of the project. -/
def loopF739 : NRRF739.Closure Unit Bool := toF739 NRRF783.loopForm

/-- The twist form, as a closure object of the project. -/
def twistF739 : NRRF739.Closure Nat Nat := toF739 NRRF783.twistForm

/-- **The fourfold separated by the closing equation alone, choice-free.**  The two failures are
witnessed by explicit moved readings (`false` for the loop, `0` for the twist), so no excluded
middle and no classical instance is used. -/
theorem fourfold_by_closing_constructive :
    NRRF740.Closes pointF739 ∧ NRRF740.Closes lineF739 ∧
    ¬ NRRF740.Closes loopF739 ∧ ¬ NRRF740.Closes twistF739 :=
  NRRF783.fourfold_by_closing

/-! ## §4  The unification, for the project's own forms -/

/-- **The full unification of the axiometric forms — NRRF740's headline statement for the
project's own closure object — with no classical axiom.**

1. The return equation `(U1)` holds and the holding equation `(U2)` is derived from it.
2. The closing equation `(U3)` has five equivalent readings: transparency, bijectivity of the
   encoding, injectivity of the evaluation, uniqueness of the admissible encoding, and emptiness
   of the defect.
3. The forms of the system are exactly the idempotent translations, and the witnessing form is
   constructed from the idempotent rather than chosen.
4. One rule — the source form — generates every solution.
5. Every derivation is admissible.
6. The section a classical treatment would have to choose is supplied by the form itself.
7. Closing is a stable proposition, so classical logic proves nothing further about it.

Audited in §5: `propext` and `Quot.sound` only. -/
theorem nrrf740_answer_without_classical {A B : Type} [DecidableEq A] [DecidableEq B]
    (c : NRRF739.Closure A B) (h : B → B) (hh : ∀ b, h (h b) = h b) (d : NRRF783.Deriv A B) :
    (c.eval ∘ c.encode = id ∧ c.hold ∘ c.hold = c.hold) ∧
    (NRRF740.Closes c ↔ c.Transparent) ∧
    (NRRF740.Closes c ↔ Bijective c.encode) ∧
    (NRRF740.Closes c ↔ Injective c.eval) ∧
    (NRRF740.Closes c ↔ (NRRF783.Defect (ofF739 c) → False)) ∧
    (NRRF740.Closes c ↔ ∀ e : A → B, c.IsSection e → e = c.encode) ∧
    (∃ (A' : Type) (c' : NRRF739.Closure A' B), c'.hold = h) ∧
    (∃ (r : B → A) (S : NRRF783.Source r), toF739 (NRRF783.ofSource S) = c) ∧
    NRRF783.Admissible (d.realize).encode (d.realize).eval ∧
    (∀ a : A, c.eval (((ofF739 c).fibre a).val) = a) ∧
    (¬¬ NRRF740.Closes c → NRRF740.Closes c) := by
  obtain ⟨r1, r2, r3, r4, r5⟩ := unified_closing_readings_constructive c
  obtain ⟨⟨u1, u2⟩, -, -, -, -, -, hforms, hsrc, hadm, hfib, hstab⟩ :=
    NRRF783.nrrf783_unification (ofF739 c) h hh d
  refine ⟨⟨u1, u2⟩, r1, r2, r3, r5, r4, ?_, ?_, hadm, hfib, hstab⟩
  · obtain ⟨A', c', hc'⟩ := hforms
    exact ⟨A', toF739 c', hc'⟩
  · obtain ⟨r, S, hS⟩ := hsrc
    exact ⟨r, S, congrArg toF739 hS⟩

end NRRF783Bridge

/-! ## §5  Axiom audit

The first block records, with `#guard_msgs`, exactly which parts of NRRF740 were already
choice-free and which three used `Classical.choice`.  The second block pins the replacements
proved above: none of them uses a classical axiom. -/

section Audit

/-! ### Already choice-free in NRRF740 -/

/-- info: 'NRRF740.unified_return' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms NRRF740.unified_return

/-- info: 'NRRF740.unified_hold_idem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms NRRF740.unified_hold_idem

/-- info: 'NRRF740.admissible_iff_closure' does not depend on any axioms -/
#guard_msgs in #print axioms NRRF740.admissible_iff_closure

/-- info: 'NRRF740.forms_are_exactly_idempotents' depends on axioms: [propext] -/
#guard_msgs in #print axioms NRRF740.forms_are_exactly_idempotents

/-- info: 'NRRF740.source_rule_complete' does not depend on any axioms -/
#guard_msgs in #print axioms NRRF740.source_rule_complete

/-- info: 'NRRF740.deriv_admissible' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms NRRF740.deriv_admissible

/-! ### The three classical steps of NRRF740 … -/

/--
info: 'NRRF739.Closure.unique_section_iff_transparent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms NRRF739.Closure.unique_section_iff_transparent

/-- info: 'NRRF740.unified_closing_readings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF740.unified_closing_readings

/-- info: 'NRRF740.fourfold_by_closing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NRRF740.fourfold_by_closing

/-! ### … and their choice-free replacements -/

/-- info: 'NRRF783Bridge.unique_section_iff_transparent_constructive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms NRRF783Bridge.unique_section_iff_transparent_constructive

/-- info: 'NRRF783Bridge.unified_closing_readings_constructive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms NRRF783Bridge.unified_closing_readings_constructive

/-- info: 'NRRF783Bridge.fourfold_by_closing_constructive' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms NRRF783Bridge.fourfold_by_closing_constructive

/-- info: 'NRRF783Bridge.nrrf740_answer_without_classical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms NRRF783Bridge.nrrf740_answer_without_classical

end Audit
