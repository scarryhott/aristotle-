/-!
# NRRF785 — Quantum and classical frameworks unified on translational truth

A **classical** framework says: every question has an answer, the answer does not depend on the
frame in which the question is asked, and one global assignment of answers reproduces every
measurement.  A **quantum** framework says: not every question has an answer in a given frame,
and the answers that *are* obtained cannot be glued into any single global assignment — they are
*contextual*.

This file shows the two are the same kind of object, and that the thing they share is
**translational truth**: truth is not an absolute value attached to an observable, it is a value
attached to the *orbit* of a (frame, observable) pair under change of level.  On that reading:

* every framework — classical or contextual — carries exactly one truth function on translation
  orbits (`unified_truth`, `truth_unique`);
* every framework is classical *inside each frame* (`fragment_noncontextual`): non-classicality is
  never local, it is a global, translational phenomenon;
* classical frameworks are exactly the frameworks that are total and noncontextual
  (`total_noncontextual_iff_classical`), equivalently total and frame-free
  (`classical_iff_total_contextFree`), equivalently *given by a single shift-invariant assignment*
  (`classical_iff_invariant_assignment`).  So the classical case is not a different notion of
  truth: it is the case in which the translational truth happens to descend to an absolute,
  origin-fixing assignment;
* the descent is forced, not chosen: any global assignment consistent with a framework is already
  shift-invariant wherever the framework speaks (`section_invariant_on_defined`).  A classical
  framework therefore *is* a chosen absolute level;
* a fully worked contextual framework (§6) — three observables, three frames, each frame answering
  two of them with opposite values, cyclically translated — has **no** global assignment
  (`parity_contextual`), and yet its translational truth is complete and exact: the nine
  (frame, observable) pairs fall into exactly three translation orbits carrying the verdicts
  `some true`, `some false`, `none` (`parity_three_orbits`, `parity_orbit_truths`).  Quantum data
  is not truth-less data; it is data whose truth is translational rather than absolute.

The file has **no `import` line**: only Lean's kernel is in scope, so no library convention can be
smuggled in.  §7 pins the exact axiom list of every headline result.
-/

namespace NRRF785

universe u v w x

/-! ## §1  Levels, frames, observables, frameworks

A **level shift** is a translation: a neutral shift, composition, reversal — an abelian group,
written out by hand so that nothing is imported. -/

/-- An abelian group of **level shifts** (translations, changes of the level of description). -/
structure Shift (S : Type u) where
  /-- The neutral change of level. -/
  unit : S
  /-- Composition of level changes. -/
  comp : S → S → S
  /-- Reversal of a level change. -/
  inv : S → S
  unit_comp : ∀ s, comp unit s = s
  comp_unit : ∀ s, comp s unit = s
  comp_assoc : ∀ s t r, comp (comp s t) r = comp s (comp t r)
  comp_comm : ∀ s t, comp s t = comp t s
  comp_inv : ∀ s, comp s (inv s) = unit
  inv_comp : ∀ s, comp (inv s) s = unit

/-- A **framework**: observables `O` interrogated in frames `C`, with values in `V`, the whole
datum carried by an action of a group `S` of level shifts.

`val c o = some v` reads "in frame `c`, observable `o` has the value `v`"; `val c o = none` reads
"in frame `c`, observable `o` is not answered" — the frame does not present that question.

`equivariant` is the translational-truth condition: shifting the frame *and* the observable by the
same change of level leaves the verdict alone.  It is the only link imposed between frames; no
frame is privileged, and no absolute value is postulated. -/
structure Framework (S : Type u) (C : Type v) (O : Type w) (V : Type x) where
  /-- The group of level shifts. -/
  shift : Shift S
  /-- Change the level of a frame. -/
  actC : S → C → C
  /-- Change the level of an observable. -/
  actO : S → O → O
  actC_unit : ∀ c, actC shift.unit c = c
  actC_comp : ∀ s t c, actC s (actC t c) = actC (shift.comp s t) c
  actO_unit : ∀ o, actO shift.unit o = o
  actO_comp : ∀ s t o, actO s (actO t o) = actO (shift.comp s t) o
  /-- The verdict of a frame on an observable. -/
  val : C → O → Option V
  equivariant : ∀ s c o, val (actC s c) (actO s o) = val c o

namespace Framework

variable {S : Type u} {C : Type v} {O : Type w} {V : Type x}

/-- Reversing a change of level undoes it, on frames. -/
theorem actC_inv_actC (F : Framework S C O V) (s : S) (c : C) :
    F.actC (F.shift.inv s) (F.actC s c) = c := by
  rw [F.actC_comp, F.shift.inv_comp, F.actC_unit]

/-- Reversing a change of level undoes it, on observables. -/
theorem actO_inv_actO (F : Framework S C O V) (s : S) (o : O) :
    F.actO (F.shift.inv s) (F.actO s o) = o := by
  rw [F.actO_comp, F.shift.inv_comp, F.actO_unit]

/-- The verdict may equally be read one level back. -/
theorem equivariant_inv (F : Framework S C O V) (s : S) (c : C) (o : O) :
    F.val (F.actC (F.shift.inv s) c) (F.actO (F.shift.inv s) o) = F.val c o := F.equivariant _ c o

end Framework

/-! ## §2  Classical, total, frame-free, contextual -/

variable {S : Type u} {C : Type v} {O : Type w} {V : Type x}

/-- Frame `c` answers observable `o`. -/
def Defined (F : Framework S C O V) (c : C) (o : O) : Prop := ∃ v, F.val c o = some v

/-- Every frame answers every observable. -/
def Total (F : Framework S C O V) : Prop := ∀ c o, Defined F c o

/-- The verdict never depends on the frame. -/
def FrameFree (F : Framework S C O V) : Prop := ∀ c c' o, F.val c o = F.val c' o

/-- A framework is **classical** when one global assignment of values to observables reproduces
every frame's verdict on every observable. -/
def IsClassical (F : Framework S C O V) : Prop := ∃ g : O → V, ∀ c o, F.val c o = some (g o)

/-- A framework is **noncontextual** when some global assignment agrees with every verdict the
framework actually gives (frames may still leave questions unanswered). -/
def Noncontextual (F : Framework S C O V) : Prop :=
  ∃ g : O → V, ∀ c o v, F.val c o = some v → g o = v

/-- **Contextual**: no global assignment fits all the verdicts. -/
def Contextual (F : Framework S C O V) : Prop := ¬ Noncontextual F

/-- An assignment is **level-invariant** when a change of level does not move it. -/
def Invariant (F : Framework S C O V) (g : O → V) : Prop := ∀ s o, g (F.actO s o) = g o

/-! ## §3  Each frame is classical; classicality is the global gluing

The single-frame fragment of *any* framework — including a contextual one — admits a global
assignment agreeing with it.  Non-classicality is therefore never visible inside one frame: it is
a statement about how the frames translate into one another. -/

/-- **Every framework is classical inside each frame.**  Given any value `v0` to fill the
unanswered questions, the frame's own verdicts are reproduced by one assignment. -/
theorem fragment_noncontextual (F : Framework S C O V) (v0 : V) (c : C) :
    ∃ g : O → V, ∀ o v, F.val c o = some v → g o = v := by
  refine ⟨fun o => (F.val c o).getD v0, fun o v h => ?_⟩
  show (F.val c o).getD v0 = v
  rw [h]
  rfl

/-- A classical framework is noncontextual. -/
theorem classical_noncontextual (F : Framework S C O V) (h : IsClassical F) : Noncontextual F := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, fun c o v hv => ?_⟩
  have : some (g o) = some v := by rw [← hg c o, hv]
  exact Option.some.inj this

/-- A classical framework is total. -/
theorem classical_total (F : Framework S C O V) (h : IsClassical F) : Total F := by
  obtain ⟨g, hg⟩ := h
  exact fun c o => ⟨g o, hg c o⟩

/-- A classical framework is frame-free. -/
theorem classical_frameFree (F : Framework S C O V) (h : IsClassical F) : FrameFree F := by
  obtain ⟨g, hg⟩ := h
  intro c c' o
  rw [hg c o, hg c' o]

/-- **Classicality = totality + noncontextuality.**  A framework is classical exactly when every
question is answered in every frame and the answers glue. -/
theorem total_noncontextual_iff_classical (F : Framework S C O V) :
    (Total F ∧ Noncontextual F) ↔ IsClassical F := by
  constructor
  · intro ⟨htot, g, hg⟩
    refine ⟨g, fun c o => ?_⟩
    obtain ⟨v, hv⟩ := htot c o
    rw [hv, hg c o v hv]
  · intro h
    exact ⟨classical_total F h, classical_noncontextual F h⟩

/-- **Classicality = totality + frame-independence** (given at least one frame and one value to
name).  The two familiar readings of "classical" coincide. -/
theorem classical_iff_total_frameFree (F : Framework S C O V) (c0 : C) (v0 : V) :
    IsClassical F ↔ (Total F ∧ FrameFree F) := by
  constructor
  · intro h
    exact ⟨classical_total F h, classical_frameFree F h⟩
  · intro ⟨htot, hff⟩
    refine ⟨fun o => (F.val c0 o).getD v0, fun c o => ?_⟩
    obtain ⟨v, hv⟩ := htot c0 o
    show F.val c o = some ((F.val c0 o).getD v0)
    rw [hff c c0 o, hv]
    rfl

/-! ## §4  The absolute assignment, where it exists, is forced to be translational

If a global assignment fits a framework's verdicts at all, then it is already invariant under
every change of level, on every observable the framework speaks about.  So the classical picture
is not an alternative to translational truth: it is translational truth in the case where the
orbit verdicts happen to be carried by a single invariant function. -/

/-- **Any consistent global assignment is level-invariant where the framework speaks.** -/
theorem section_invariant_on_defined (F : Framework S C O V) (g : O → V)
    (hg : ∀ c o v, F.val c o = some v → g o = v) (s : S) (c : C) (o : O) (v : V)
    (hv : F.val c o = some v) : g (F.actO s o) = g o := by
  have h1 : F.val (F.actC s c) (F.actO s o) = some v := by rw [F.equivariant s c o, hv]
  rw [hg (F.actC s c) (F.actO s o) v h1, hg c o v hv]

/-- **A classical framework's assignment is level-invariant.**  Fixing absolute values is only
possible in a way that is itself unmoved by change of level. -/
theorem classical_section_invariant (F : Framework S C O V) (c0 : C) (g : O → V)
    (hg : ∀ c o, F.val c o = some (g o)) : Invariant F g := by
  intro s o
  have h : some (g (F.actO s o)) = some (g o) := by
    rw [← hg (F.actC s c0) (F.actO s o), F.equivariant s c0 o, hg c0 o]
  exact Option.some.inj h

/-- **Classical frameworks are exactly the frameworks given by a single invariant assignment.**
The unification statement for the classical side: to be classical is to be translational truth
that descends to an absolute, level-invariant naming of values. -/
theorem classical_iff_invariant_assignment (F : Framework S C O V) (c0 : C) :
    IsClassical F ↔ ∃ g : O → V, Invariant F g ∧ ∀ c o, F.val c o = some (g o) := by
  constructor
  · intro ⟨g, hg⟩
    exact ⟨g, classical_section_invariant F c0 g hg, hg⟩
  · intro ⟨g, _, hg⟩
    exact ⟨g, hg⟩

/-! ## §5  Translational truth: the object both frameworks share

A (frame, observable) pair is a *presentation* of a question at a level.  Changing the level moves
the pair; the verdict does not move.  Truth is therefore a function on the orbits — and this holds
for every framework whatsoever, classical or contextual.  §5 constructs that function and shows it
is the unique one. -/

/-- Two presentations are **translates** when a single change of level carries one to the other. -/
def Translates (F : Framework S C O V) (p q : C × O) : Prop :=
  ∃ s : S, (F.actC s p.1, F.actO s p.2) = q

theorem translates_refl (F : Framework S C O V) (p : C × O) : Translates F p p :=
  ⟨F.shift.unit, by rw [F.actC_unit, F.actO_unit]⟩

theorem translates_symm (F : Framework S C O V) {p q : C × O} (h : Translates F p q) :
    Translates F q p := by
  obtain ⟨s, hs⟩ := h
  refine ⟨F.shift.inv s, ?_⟩
  cases hs
  rw [F.actC_inv_actC, F.actO_inv_actO]

theorem translates_trans (F : Framework S C O V) {p q r : C × O} (hpq : Translates F p q)
    (hqr : Translates F q r) : Translates F p r := by
  obtain ⟨s, hs⟩ := hpq
  obtain ⟨t, ht⟩ := hqr
  refine ⟨F.shift.comp t s, ?_⟩
  cases hs
  cases ht
  rw [F.actC_comp, F.actO_comp]

/-- The **level-unified questions**: presentations up to change of level. -/
def Orbit (F : Framework S C O V) : Type max v w := Quot (Translates F)

/-- The orbit of a presentation. -/
def orb (F : Framework S C O V) (p : C × O) : Orbit F := Quot.mk _ p

/-- Presentations related by a change of level are the same level-unified question. -/
theorem orb_shift (F : Framework S C O V) (s : S) (c : C) (o : O) :
    orb F (F.actC s c, F.actO s o) = orb F (c, o) :=
  (Quot.sound ⟨s, rfl⟩ : orb F (c, o) = orb F (F.actC s c, F.actO s o)).symm

/-- **Translational truth**: the verdict as a function of the level-unified question.  Every
framework has one. -/
def truth (F : Framework S C O V) : Orbit F → Option V :=
  Quot.lift (fun p => F.val p.1 p.2) <| by
    intro p q h
    obtain ⟨s, hs⟩ := h
    cases hs
    exact (F.equivariant s p.1 p.2).symm

@[simp] theorem truth_orb (F : Framework S C O V) (c : C) (o : O) :
    truth F (orb F (c, o)) = F.val c o := rfl

/-- Translational truth is unchanged by change of level — by construction, not by assumption. -/
theorem truth_shift (F : Framework S C O V) (s : S) (c : C) (o : O) :
    truth F (orb F (F.actC s c, F.actO s o)) = truth F (orb F (c, o)) := by
  rw [truth_orb, truth_orb, F.equivariant]

/-- **The truth function is unique.**  There is exactly one function on level-unified questions
reproducing the framework's verdicts, so "the translational truth of a framework" is a definite
object and not a choice of presentation. -/
theorem truth_unique (F : Framework S C O V) (h : Orbit F → Option V)
    (hh : ∀ c o, h (orb F (c, o)) = F.val c o) : h = truth F := by
  funext q
  induction q using Quot.ind with
  | _ p => exact hh p.1 p.2

/-- **The unification.**  Every framework — classical or contextual, total or not — is exactly a
truth function on level-unified questions: it exists and it is unique. -/
theorem unified_truth (F : Framework S C O V) :
    ∃ h : Orbit F → Option V, (∀ c o, h (orb F (c, o)) = F.val c o) ∧
      ∀ h' : Orbit F → Option V, (∀ c o, h' (orb F (c, o)) = F.val c o) → h' = h :=
  ⟨truth F, fun _ _ => rfl, fun h' hh' => truth_unique F h' hh'⟩

/-- Classicality, read off the translational truth: a framework is classical iff its truth
function is `some (g ·)` for a level-invariant `g` on observables. -/
theorem classical_iff_truth_from_invariant (F : Framework S C O V) (c0 : C) :
    IsClassical F ↔ ∃ g : O → V, Invariant F g ∧
      ∀ c o, truth F (orb F (c, o)) = some (g o) :=
  classical_iff_invariant_assignment F c0

/-! ## §6  A contextual framework whose translational truth is complete

Three observables `a, b, c`; three frames `ab, bc, ca`, each answering exactly two of them with
*opposite* values; and the cyclic group of three level shifts rotating observables and frames
together.  This is the smallest parity obstruction: it is contextual, so it has no classical
description at all — and yet it is a framework in exactly the sense of §1, its translational truth
exists, is unique, and takes exactly three values on exactly three orbits. -/

/-- The three observables. -/
inductive Q where
  | a : Q
  | b : Q
  | c : Q
  deriving DecidableEq

/-- The three frames, each presenting a pair of observables. -/
inductive Fr where
  | ab : Fr
  | bc : Fr
  | ca : Fr
  deriving DecidableEq

/-- The three level shifts. -/
inductive Rot where
  | r0 : Rot
  | r1 : Rot
  | r2 : Rot
  deriving DecidableEq

namespace Rot

/-- Composition of level shifts. -/
def comp : Rot → Rot → Rot
  | r0, s => s
  | r1, r0 => r1
  | r1, r1 => r2
  | r1, r2 => r0
  | r2, r0 => r2
  | r2, r1 => r0
  | r2, r2 => r1

/-- Reversal of a level shift. -/
def inv : Rot → Rot
  | r0 => r0
  | r1 => r2
  | r2 => r1

end Rot

/-- The cyclic group of level shifts. -/
def rotShift : Shift Rot where
  unit := Rot.r0
  comp := Rot.comp
  inv := Rot.inv
  unit_comp := fun s => rfl
  comp_unit := fun s => by cases s <;> rfl
  comp_assoc := fun s t r => by cases s <;> cases t <;> cases r <;> rfl
  comp_comm := fun s t => by cases s <;> cases t <;> rfl
  comp_inv := fun s => by cases s <;> rfl
  inv_comp := fun s => by cases s <;> rfl

/-- One step of the cyclic translation on observables. -/
def Q.step : Q → Q
  | .a => .b
  | .b => .c
  | .c => .a

/-- One step of the cyclic translation on frames. -/
def Fr.step : Fr → Fr
  | .ab => .bc
  | .bc => .ca
  | .ca => .ab

/-- The action of a level shift on observables. -/
def rotQ : Rot → Q → Q
  | .r0, q => q
  | .r1, q => q.step
  | .r2, q => q.step.step

/-- The action of a level shift on frames. -/
def rotFr : Rot → Fr → Fr
  | .r0, f => f
  | .r1, f => f.step
  | .r2, f => f.step.step

/-- The parity verdicts: each frame answers its two observables with opposite values, and is
silent about the third. -/
def parityVal : Fr → Q → Option Bool
  | .ab, .a => some true
  | .ab, .b => some false
  | .bc, .b => some true
  | .bc, .c => some false
  | .ca, .c => some true
  | .ca, .a => some false
  | .ab, .c => none
  | .bc, .a => none
  | .ca, .b => none

/-- The parity framework: contextual, translational, complete. -/
def parity : Framework Rot Fr Q Bool where
  shift := rotShift
  actC := rotFr
  actO := rotQ
  actC_unit := fun c => rfl
  actC_comp := fun s t c => by cases s <;> cases t <;> cases c <;> rfl
  actO_unit := fun o => rfl
  actO_comp := fun s t o => by cases s <;> cases t <;> cases o <;> rfl
  val := parityVal
  equivariant := fun s c o => by cases s <;> cases c <;> cases o <;> rfl

/-- **The parity framework is contextual**: no global assignment of values to the three
observables agrees with the frames.  Frame `ab` says `a` is `true`; frame `ca` says `a` is
`false`. -/
theorem parity_contextual : Contextual parity := by
  intro ⟨g, hg⟩
  have h1 : g Q.a = true := hg Fr.ab Q.a true rfl
  have h2 : g Q.a = false := hg Fr.ca Q.a false rfl
  rw [h1] at h2
  exact Bool.noConfusion h2

/-- Hence the parity framework is not classical. -/
theorem parity_not_classical : ¬ IsClassical parity := fun h =>
  parity_contextual (classical_noncontextual parity h)

/-- Nor is it total: each frame leaves one observable unanswered — complementarity. -/
theorem parity_not_total : ¬ Total parity := by
  intro h
  obtain ⟨v, hv⟩ := h Fr.ab Q.c
  have hv' : (none : Option Bool) = some v := hv
  cases hv'

/-- Yet every pair of distinct observables *is* answered together in some frame: the obstruction
is not pairwise, it is global. -/
theorem parity_pairwise_defined :
    (Defined parity Fr.ab Q.a ∧ Defined parity Fr.ab Q.b) ∧
    (Defined parity Fr.bc Q.b ∧ Defined parity Fr.bc Q.c) ∧
    (Defined parity Fr.ca Q.c ∧ Defined parity Fr.ca Q.a) :=
  ⟨⟨⟨true, rfl⟩, ⟨false, rfl⟩⟩, ⟨⟨true, rfl⟩, ⟨false, rfl⟩⟩, ⟨⟨true, rfl⟩, ⟨false, rfl⟩⟩⟩

/-- And inside each frame the parity framework is classical, by the general theorem: contextuality
is invisible locally. -/
theorem parity_fragment_classical (f : Fr) :
    ∃ g : Q → Bool, ∀ o v, parity.val f o = some v → g o = v :=
  fragment_noncontextual parity false f

/-- A level-invariant assignment on the parity framework is constant — which is the second,
symmetry-based reason no absolute assignment can exist: the frames demand different values for
observables that a change of level identifies. -/
theorem parity_invariant_constant (g : Q → Bool) (h : Invariant parity g) :
    g Q.a = g Q.b ∧ g Q.b = g Q.c := by
  refine ⟨?_, ?_⟩
  · exact (h Rot.r1 Q.a).symm
  · exact (h Rot.r1 Q.b).symm

/-- **Exactly three level-unified questions.**  Every one of the nine presentations is a translate
of `(ab, a)`, `(ab, b)` or `(ab, c)`. -/
theorem parity_three_orbits (p : Fr × Q) :
    orb parity p = orb parity (Fr.ab, Q.a) ∨
    orb parity p = orb parity (Fr.ab, Q.b) ∨
    orb parity p = orb parity (Fr.ab, Q.c) := by
  obtain ⟨f, q⟩ := p
  cases f <;> cases q
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inr (orb_shift parity Rot.r1 Fr.ab Q.c))
  · exact Or.inl (orb_shift parity Rot.r1 Fr.ab Q.a)
  · exact Or.inr (Or.inl (orb_shift parity Rot.r1 Fr.ab Q.b))
  · exact Or.inr (Or.inl (orb_shift parity Rot.r2 Fr.ab Q.b))
  · exact Or.inr (Or.inr (orb_shift parity Rot.r2 Fr.ab Q.c))
  · exact Or.inl (orb_shift parity Rot.r2 Fr.ab Q.a)

/-- **The translational truth of the parity framework is complete and exact**: the three orbits
carry the verdicts `some true`, `some false` and `none`. -/
theorem parity_orbit_truths :
    truth parity (orb parity (Fr.ab, Q.a)) = some true ∧
    truth parity (orb parity (Fr.ab, Q.b)) = some false ∧
    truth parity (orb parity (Fr.ab, Q.c)) = none :=
  ⟨rfl, rfl, rfl⟩

/-- Every presentation's verdict is already determined by its level-unified question: for the
parity framework, translational truth decides everything the framework says, although no absolute
assignment does. -/
theorem parity_truth_decides (f : Fr) (q : Q) :
    truth parity (orb parity (f, q)) = parity.val f q := rfl

/-! ## §7  A classical framework, for comparison, and the collected statement -/

/-- The classical framework attached to a level-invariant assignment: every frame answers every
observable, with the same value. -/
def ofInvariant {S : Type u} {C : Type v} {O : Type w} {V : Type x} (sh : Shift S)
    (aC : S → C → C) (aO : S → O → O)
    (hCu : ∀ c, aC sh.unit c = c) (hCc : ∀ s t c, aC s (aC t c) = aC (sh.comp s t) c)
    (hOu : ∀ o, aO sh.unit o = o) (hOc : ∀ s t o, aO s (aO t o) = aO (sh.comp s t) o)
    (g : O → V) (hg : ∀ s o, g (aO s o) = g o) : Framework S C O V where
  shift := sh
  actC := aC
  actO := aO
  actC_unit := hCu
  actC_comp := hCc
  actO_unit := hOu
  actO_comp := hOc
  val := fun _ o => some (g o)
  equivariant := fun s _ o => by rw [hg s o]

theorem ofInvariant_isClassical {S : Type u} {C : Type v} {O : Type w} {V : Type x} (sh : Shift S)
    (aC : S → C → C) (aO : S → O → O)
    (hCu : ∀ c, aC sh.unit c = c) (hCc : ∀ s t c, aC s (aC t c) = aC (sh.comp s t) c)
    (hOu : ∀ o, aO sh.unit o = o) (hOc : ∀ s t o, aO s (aO t o) = aO (sh.comp s t) o)
    (g : O → V) (hg : ∀ s o, g (aO s o) = g o) :
    IsClassical (ofInvariant sh aC aO hCu hCc hOu hOc g hg) :=
  ⟨g, fun _ _ => rfl⟩

/-- **NRRF785, collected.**  Quantum and classical frameworks are one framework notion, unified on
translational truth:

1. every framework carries a unique truth function on level-unified questions;
2. every framework is classical inside each frame;
3. classical = total + noncontextual = given by a level-invariant assignment, and any consistent
   global assignment is forced to be level-invariant;
4. contextual frameworks exist (the parity framework), are not classical, and nevertheless have
   complete translational truth on exactly three orbits. -/
theorem nrrf785_unification :
    (∀ {S : Type} {C O V : Type} (F : Framework S C O V),
        ∃ h : Orbit F → Option V, (∀ c o, h (orb F (c, o)) = F.val c o) ∧
          ∀ h' : Orbit F → Option V, (∀ c o, h' (orb F (c, o)) = F.val c o) → h' = h) ∧
    (∀ {S : Type} {C O V : Type} (F : Framework S C O V) (_ : V) (c : C),
        ∃ g : O → V, ∀ o v, F.val c o = some v → g o = v) ∧
    (∀ {S : Type} {C O V : Type} (F : Framework S C O V),
        (Total F ∧ Noncontextual F) ↔ IsClassical F) ∧
    (∀ {S : Type} {C O V : Type} (F : Framework S C O V) (_ : C),
        IsClassical F ↔ ∃ g : O → V, Invariant F g ∧ ∀ c o, F.val c o = some (g o)) ∧
    Contextual parity ∧ ¬ IsClassical parity ∧
    (∀ p : Fr × Q, orb parity p = orb parity (Fr.ab, Q.a) ∨
        orb parity p = orb parity (Fr.ab, Q.b) ∨ orb parity p = orb parity (Fr.ab, Q.c)) ∧
    (truth parity (orb parity (Fr.ab, Q.a)) = some true ∧
      truth parity (orb parity (Fr.ab, Q.b)) = some false ∧
      truth parity (orb parity (Fr.ab, Q.c)) = none) :=
  ⟨fun F => unified_truth F,
   fun F v0 c => fragment_noncontextual F v0 c,
   fun F => total_noncontextual_iff_classical F,
   fun F c0 => classical_iff_invariant_assignment F c0,
   parity_contextual,
   parity_not_classical,
   parity_three_orbits,
   parity_orbit_truths⟩

end NRRF785

/-! ## §8  Axiom audit — machine-checked

Only `Quot.sound` — the quotient axiom, needed exactly where level-unified questions are formed —
ever occurs.  `Classical.choice` occurs nowhere: the whole unification is constructive. -/

section Audit

/-- info: 'NRRF785.fragment_noncontextual' does not depend on any axioms -/
#guard_msgs in #print axioms NRRF785.fragment_noncontextual

/-- info: 'NRRF785.total_noncontextual_iff_classical' does not depend on any axioms -/
#guard_msgs in #print axioms NRRF785.total_noncontextual_iff_classical

/-- info: 'NRRF785.classical_section_invariant' does not depend on any axioms -/
#guard_msgs in #print axioms NRRF785.classical_section_invariant

/-- info: 'NRRF785.classical_iff_invariant_assignment' does not depend on any axioms -/
#guard_msgs in #print axioms NRRF785.classical_iff_invariant_assignment

/-- info: 'NRRF785.truth_unique' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms NRRF785.truth_unique

/-- info: 'NRRF785.unified_truth' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms NRRF785.unified_truth

/-- info: 'NRRF785.parity_contextual' does not depend on any axioms -/
#guard_msgs in #print axioms NRRF785.parity_contextual

/-- info: 'NRRF785.parity_three_orbits' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms NRRF785.parity_three_orbits

/-- info: 'NRRF785.nrrf785_unification' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms NRRF785.nrrf785_unification

end Audit
