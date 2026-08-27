import Mathlib.Topology.Homeomorph.Defs
import NRRF766ContinualTradingClosureFeedback

/-!
# NRRF768 — Relative translational truth natural-form selector

This module fills the missing selector layer without assuming a maximizer or a canonical choice.
Closure first identifies occurrences by their return.  The corresponding
quotient is the return carrier, and the topology induced from the discrete return carrier has
exactly the same observational identity.  A natural form is then a *supplied natural section* of
that return, not something manufactured by closure.

`RelativeFormSeed` is an authored, pointwise choice at one temporary origin language.  Translation
extends that choice to all languages, and changing the temporary origin cancels.  No
`Classical.choice` is used.  Reversal exhibits genuine freedom in a separated frame: the two
selectors differ as occurrences but remain closure-equal and topologically indistinguishable.

The final section connects such a selector to the existing trading interface.  Admission still
requires an actual network interaction and a local completion witness.  No profit, ordering of
outcomes, numerical maximization, or terminal closure is inferred.
-/

namespace NRRF768

open Function
open NRRF627
open NRRF764

universe u v w z

/-! ## Return equality, quotient completion, and its derived topology -/

/-- The setoid whose equality is exactly NRRF627 closure equality. -/
def closureSetoid {X : Type u} {B : Type v} (W : X → B) : Setoid X where
  r := CEq W
  iseqv := ceq_equivalence W

/-- Completion identifies precisely the occurrences with one returned identity. -/
abbrev Completion {X : Type u} {B : Type v} (W : X → B) := Quotient (closureSetoid W)

/-- The quotient returns the common identity of any of its representatives. -/
def completionReturn {X : Type u} {B : Type v} (W : X → B) : Completion W → B :=
  Quotient.lift W (fun _ _ h ↦ h)

@[simp] theorem completionReturn_mk {X : Type u} {B : Type v} (W : X → B) (x : X) :
    completionReturn W (Quotient.mk (closureSetoid W) x) = W x :=
  rfl

/-- In a translational frame, every returned identity has an explicit quotient presentation. -/
def completionPresentation {L : Type u} {B : L → Type v} {Y : L → Type w}
    (A : TransFrame L B Y) (l : L) (b : B l) : Completion (A.W l) :=
  Quotient.mk (closureSetoid (A.W l)) (A.E l Pole.zero b)

/-- The quotient completion is exactly the return carrier.  Surjectivity is supplied by `E`; no
choice of an arbitrary representative is required. -/
def completionEquiv {L : Type u} {B : L → Type v} {Y : L → Type w}
    (A : TransFrame L B Y) (l : L) : Completion (A.W l) ≃ B l where
  toFun := completionReturn (A.W l)
  invFun := completionPresentation A l
  left_inv q := by
    refine Quotient.inductionOn q ?_
    intro x
    apply Quotient.sound
    show A.W l (A.E l Pole.zero (A.W l x)) = A.W l x
    exact A.recov l Pole.zero (A.W l x)
  right_inv b := A.recov l Pole.zero b

@[simp] theorem completionEquiv_apply_mk
    {L : Type u} {B : L → Type v} {Y : L → Type w}
    (A : TransFrame L B Y) (l : L) (x : Y l) :
    completionEquiv A l (Quotient.mk (closureSetoid (A.W l)) x) = A.W l x :=
  rfl

/-- Relative occurrence translation descends to truth-equality completion because it preserves
and reflects return equality. -/
def completionMap {L : Type u} {B : L → Type v} {Y : L → Type w}
    (A : TransFrame L B Y) (l m : L) : Completion (A.W l) → Completion (A.W m) :=
  Quotient.map (A.T l m) (by
    intro x y h
    change A.W l x = A.W l y at h
    change A.W m (A.T l m x) = A.W m (A.T l m y)
    rw [A.T_ret, A.T_ret, h])

@[simp] theorem completionMap_mk
    {L : Type u} {B : L → Type v} {Y : L → Type w}
    (A : TransFrame L B Y) (l m : L) (x : Y l) :
    completionMap A l m (Quotient.mk (closureSetoid (A.W l)) x) =
      Quotient.mk (closureSetoid (A.W m)) (A.T l m x) :=
  rfl

/-- Completion translation is itself reversible; translating back cancels without choosing a
representative. -/
def completionTranslationEquiv
    {L : Type u} {B : L → Type v} {Y : L → Type w}
    (A : TransFrame L B Y) (l m : L) :
    Completion (A.W l) ≃ Completion (A.W m) where
  toFun := completionMap A l m
  invFun := completionMap A m l
  left_inv q := by
    refine Quotient.inductionOn q ?_
    intro x
    simp only [completionMap_mk]
    rw [A.T_T]
  right_inv q := by
    refine Quotient.inductionOn q ?_
    intro x
    simp only [completionMap_mk]
    rw [A.T_T]

@[simp] theorem completionMap_id
    {L : Type u} {B : L → Type v} {Y : L → Type w}
    (A : TransFrame L B Y) (l : L) :
    completionMap A l l = id := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  apply Quotient.sound
  show A.W l (A.T l l x) = A.W l x
  rw [A.T_id]

@[simp] theorem completionMap_comp
    {L : Type u} {B : L → Type v} {Y : L → Type w}
    (A : TransFrame L B Y) (l m k : L) (q : Completion (A.W l)) :
    completionMap A m k (completionMap A l m q) = completionMap A l k q := by
  refine Quotient.inductionOn q ?_
  intro x
  apply Quotient.sound
  show A.W k (A.T m k (A.T l m x)) = A.W k (A.T l k x)
  rw [A.T_comp]

/-- The completion/identity square commutes: quotient translation is exactly relative truth
translation on returned identities. -/
theorem completionEquiv_natural
    {L : Type u} {B : L → Type v} {Y : L → Type w}
    (A : TransFrame L B Y) (l m : L) (q : Completion (A.W l)) :
    completionEquiv A m (completionMap A l m q) =
      A.phi l m (completionEquiv A l q) := by
  refine Quotient.inductionOn q ?_
  intro x
  exact A.T_ret l m x

/-- The commuting square above is an equality of the whole completion translations, not only a
statement at one chosen representative. -/
theorem completionEquiv_natural_square
    {L : Type u} {B : L → Type v} {Y : L → Type w}
    (A : TransFrame L B Y) (l m : L) :
    (completionEquiv A m : Completion (A.W m) → B m) ∘ completionMap A l m =
      A.phi l m ∘ (completionEquiv A l : Completion (A.W l) → B l) := by
  funext q
  exact completionEquiv_natural A l m q

/-- One open of the equality-saturation topology, explicitly presented as the inverse image of a
set of returns.  The explicit presentation keeps this topology local and uses no ambient topology
or choice principle. -/
structure EqualitySaturationOpen {X : Type u} {B : Type v} (W : X → B) where
  returns : Set B

namespace EqualitySaturationOpen

def carrier {X : Type u} {B : Type v} {W : X → B}
    (U : EqualitySaturationOpen W) : Set X :=
  W ⁻¹' U.returns

instance {X : Type u} {B : Type v} {W : X → B} : Membership X (EqualitySaturationOpen W) where
  mem U x := U.carrier x

@[simp] theorem mem_iff {X : Type u} {B : Type v} {W : X → B}
    (U : EqualitySaturationOpen W) (x : X) :
    x ∈ U ↔ W x ∈ U.returns :=
  Iff.rfl

def univ {X : Type u} {B : Type v} (W : X → B) : EqualitySaturationOpen W :=
  ⟨Set.univ⟩

def inter {X : Type u} {B : Type v} {W : X → B}
    (U V : EqualitySaturationOpen W) : EqualitySaturationOpen W :=
  ⟨U.returns ∩ V.returns⟩

def sUnion {X : Type u} {B : Type v} {W : X → B}
    (opens : Set (EqualitySaturationOpen W)) : EqualitySaturationOpen W :=
  ⟨⋃ U ∈ opens, U.returns⟩

@[simp] theorem mem_univ {X : Type u} {B : Type v} (W : X → B) (x : X) :
    x ∈ univ W := by
  simp [univ]

@[simp] theorem mem_inter {X : Type u} {B : Type v} {W : X → B}
    (U V : EqualitySaturationOpen W) (x : X) :
    x ∈ U.inter V ↔ x ∈ U ∧ x ∈ V := by
  simp [inter]

end EqualitySaturationOpen

/-- The actual topology of return-saturated sets.  Its axioms are proved directly from return
equality, avoiding any representative choice.  `instance_reducible` permits explicit local use
without installing it globally. -/
@[instance_reducible] def equalitySaturationTopology {X : Type u} {B : Type v} (W : X → B) :
    TopologicalSpace X where
  IsOpen U := ∀ x y, W x = W y → (x ∈ U ↔ y ∈ U)
  isOpen_univ := by
    intro x y _
    simp
  isOpen_inter := by
    intro U V hU hV x y hxy
    exact and_congr (hU x y hxy) (hV x y hxy)
  isOpen_sUnion := by
    intro opens hOpens x y hxy
    constructor
    · rintro ⟨U, hU, hx⟩
      exact ⟨U, hU, (hOpens U hU x y hxy).1 hx⟩
    · rintro ⟨U, hU, hy⟩
      exact ⟨U, hU, (hOpens U hU x y hxy).2 hy⟩

/-- The explicit opens above are exactly the opens of the actual derived topology. -/
theorem isOpen_equalitySaturation_iff {X : Type u} {B : Type v}
    (W : X → B) (U : Set X) :
    @IsOpen X (equalitySaturationTopology W) U ↔
      ∃ V : EqualitySaturationOpen W, V.carrier = U := by
  constructor
  · intro hU
    refine ⟨⟨W '' U⟩, ?_⟩
    ext x
    constructor
    · rintro ⟨y, hy, hreturn⟩
      exact (hU y x hreturn).1 hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  · rintro ⟨⟨V⟩, hV⟩
    rw [← hV]
    intro x y hxy
    change W x ∈ V ↔ W y ∈ V
    rw [hxy]

/-- Two occurrences have the same topological identity when every open of the actual derived
topology contains them together. -/
def SameOpenNeighborhoods {X : Type u} {B : Type v} (W : X → B) (x y : X) : Prop :=
  ∀ U : Set X, @IsOpen X (equalitySaturationTopology W) U → (x ∈ U ↔ y ∈ U)

/-- Closure equality is exactly topological indistinguishability in the topology derived from the
return. -/
theorem ceq_iff_same_open_neighborhoods {X : Type u} {B : Type v}
    (W : X → B) (x y : X) :
    CEq W x y ↔ SameOpenNeighborhoods W x y := by
  constructor
  · intro h U hU
    rcases (isOpen_equalitySaturation_iff W U).1 hU with ⟨V, rfl⟩
    change W x ∈ V.returns ↔ W y ∈ V.returns
    rw [h]
  · intro h
    let V : EqualitySaturationOpen W := ⟨{W x}⟩
    let U : Set X := V.carrier
    have hOpen : @IsOpen X (equalitySaturationTopology W) U :=
      (isOpen_equalitySaturation_iff W U).2 ⟨V, rfl⟩
    have hy : y ∈ U := (h U hOpen).1 (by simp [U, V, EqualitySaturationOpen.carrier])
    have : W y = W x := by
      simpa [U, V, EqualitySaturationOpen.carrier] using hy
    exact this.symm

/-- Relative translation is continuous for the topology derived from truth-return equality. -/
theorem translation_continuous
    {L : Type u} {B : L → Type v} {Y : L → Type w}
    (A : TransFrame L B Y) (l m : L) :
    @Continuous (Y l) (Y m)
      (equalitySaturationTopology (A.W l))
      (equalitySaturationTopology (A.W m))
      (A.T l m) := by
  rw [continuous_def]
  intro U hU x y hxy
  exact hU (A.T l m x) (A.T l m y) (by
    rw [A.T_ret, A.T_ret, hxy])

/-- Relative translation is therefore a homeomorphism of the derived topological identities, not
merely a pointwise preservation statement. -/
def translationHomeomorph
    {L : Type u} {B : L → Type v} {Y : L → Type w}
    (A : TransFrame L B Y) (l m : L) :
    @Homeomorph (Y l) (Y m)
      (@equalitySaturationTopology (Y l) (B l) (A.W l))
      (@equalitySaturationTopology (Y m) (B m) (A.W m)) :=
  @Homeomorph.mk (Y l) (Y m)
    (@equalitySaturationTopology (Y l) (B l) (A.W l))
    (@equalitySaturationTopology (Y m) (B m) (A.W m))
    (A.transEquiv l m)
    (@translation_continuous L B Y A l m)
    (@translation_continuous L B Y A m l)

/-! ## A natural form is a supplied translation-natural section -/

variable {L : Type u} {B : L → Type v} {Y : L → Type w}

/-- A natural-form selector chooses one occurrence over every returned identity and audits that
choice against return and translation.  These fields constrain a supplied choice; they do not
define a canonical choice. -/
@[ext] structure NaturalFormSelector (A : TransFrame L B Y) where
  select : ∀ l, B l → Y l
  returns : ∀ l b, A.W l (select l b) = b
  natural : ∀ l m b, A.T l m (select l b) = select m (A.phi l m b)

namespace NaturalFormSelector

variable {A : TransFrame L B Y}

/-- Holding an occurrence in a natural form means returning it and selecting the authored
representative of that same identity. -/
def hold (F : NaturalFormSelector A) (l : L) (x : Y l) : Y l :=
  F.select l (A.W l x)

@[simp] theorem hold_return (F : NaturalFormSelector A) (l : L) (x : Y l) :
    A.W l (F.hold l x) = A.W l x :=
  F.returns l (A.W l x)

@[simp] theorem hold_idempotent (F : NaturalFormSelector A) (l : L) (x : Y l) :
    F.hold l (F.hold l x) = F.hold l x := by
  rw [hold, hold, F.returns]

@[simp] theorem hold_selected (F : NaturalFormSelector A) (l : L) (b : B l) :
    F.hold l (F.select l b) = F.select l b := by
  simp [hold, F.returns]

/-- The hold identifies exactly, and only, the closure-equal occurrences. -/
theorem hold_exact_iff_ceq (F : NaturalFormSelector A) (l : L) (x y : Y l) :
    F.hold l x = F.hold l y ↔ CEq (A.W l) x y := by
  constructor
  · intro h
    show A.W l x = A.W l y
    have := congrArg (A.W l) h
    simpa using this
  · intro h
    exact congrArg (F.select l) h

/-- Translation carries the hold; it does not reselect from an external ordering. -/
theorem hold_natural (F : NaturalFormSelector A) (l m : L) (x : Y l) :
    A.T l m (F.hold l x) = F.hold m (A.T l m x) := by
  rw [hold, F.natural, hold, A.T_ret]

/-- A selector's hold is an NRRF627 restructuring: it changes presentation while preserving the
return and commuting with every relative translation. -/
def toRestructuring (F : NaturalFormSelector A) : A.Restructuring where
  act := F.hold
  act_ret := F.hold_return
  act_nat := F.hold_natural

/-- Any two supplied natural forms are closure-equal over the same returned identity.  This does
not claim a translation between arbitrary forms beyond the displayed common return. -/
theorem selectors_ceq (F G : NaturalFormSelector A) (l : L) (b : B l) :
    CEq (A.W l) (F.select l b) (G.select l b) := by
  show A.W l (F.select l b) = A.W l (G.select l b)
  rw [F.returns, G.returns]

/-- A closure-respecting verdict cannot distinguish the relative freedom between supplied forms. -/
theorem verdict_cannot_distinguish_forms {Omega : Type z}
    (F G : NaturalFormSelector A) (Q : ∀ l, Y l → Omega)
    (hQ : A.RespectsClosure Q) (l : L) (b : B l) :
    Q l (F.select l b) = Q l (G.select l b) :=
  hQ l _ _ (F.selectors_ceq G l b)

/-- The same blindness holds after either form is used as a hold on an occurrence. -/
theorem verdict_cannot_distinguish_holds {Omega : Type z}
    (F G : NaturalFormSelector A) (Q : ∀ l, Y l → Omega)
    (hQ : A.RespectsClosure Q) (l : L) (x : Y l) :
    Q l (F.hold l x) = Q l (G.hold l x) :=
  hQ l _ _ (by rw [F.hold_return, G.hold_return])

end NaturalFormSelector

/-! ## Proof-relevant freedom between supplied natural forms -/

/-- A movement between natural forms is an explicitly supplied, return-preserving internal
translation which commutes with language translation and carries the selected representatives.
No movement between arbitrary forms is postulated. -/
structure NaturalFormMovement {A : TransFrame L B Y}
    (F G : NaturalFormSelector A) where
  move : ∀ l, Y l ≃ Y l
  return_eq : ∀ l x, A.W l (move l x) = A.W l x
  natural : ∀ l m x, A.T l m (move l x) = move m (A.T l m x)
  carries : ∀ l b, move l (F.select l b) = G.select l b

namespace NaturalFormMovement

variable {A : TransFrame L B Y}

/-- Every form has the identity movement. -/
def refl (F : NaturalFormSelector A) : NaturalFormMovement F F where
  move := fun _ ↦ Equiv.refl _
  return_eq := fun _ _ ↦ rfl
  natural := fun _ _ _ ↦ rfl
  carries := fun _ _ ↦ rfl

/-- Witnessed movements compose, making continual form freedom a trajectory rather than an
unrelated succession of choices. -/
def trans {F G H : NaturalFormSelector A}
    (first : NaturalFormMovement F G) (second : NaturalFormMovement G H) :
    NaturalFormMovement F H where
  move := fun l ↦ (first.move l).trans (second.move l)
  return_eq := by
    intro l x
    rw [Equiv.trans_apply, second.return_eq, first.return_eq]
  natural := by
    intro l m x
    rw [Equiv.trans_apply, second.natural, first.natural, Equiv.trans_apply]
  carries := by
    intro l b
    rw [Equiv.trans_apply, first.carries, second.carries]

/-- Every witnessed movement reverses through its supplied equivalences.  Thus witnessed form
freedom is symmetric without asserting that a witness exists between arbitrary forms. -/
def symm {F G : NaturalFormSelector A} (movement : NaturalFormMovement F G) :
    NaturalFormMovement G F where
  move := fun l ↦ (movement.move l).symm
  return_eq := by
    intro l x
    have h := movement.return_eq l ((movement.move l).symm x)
    simpa using h.symm
  natural := by
    intro l m x
    apply (movement.move m).injective
    rw [Equiv.apply_symm_apply]
    rw [← movement.natural]
    simp
  carries := by
    intro l b
    apply (movement.move l).injective
    rw [Equiv.apply_symm_apply, movement.carries]

end NaturalFormMovement

/-! ## Relative, pointwise, authored seeds -/

/-- An authored seed is supplied at one temporary origin.  Its pole may vary pointwise with the
returned identity, so it is not restricted to one constant orientation. -/
@[ext] structure RelativeFormSeed (A : TransFrame L B Y) where
  origin : L
  pole : B origin → Pole

namespace RelativeFormSeed

variable {A : TransFrame L B Y}

/-- The pole selected by a seed after translating an identity back to the seed's temporary origin
and transporting its authored orientation to `l`. -/
def orientationAt (s : RelativeFormSeed A) (l : L) (b : B l) : Pole :=
  A.pi s.origin l (s.pole (A.phi l s.origin b))

/-- A supplied pointwise seed determines a natural form by the existing presentation and pairwise
translation operations.  This construction contains no choice principle. -/
def selectorOfSeed (s : RelativeFormSeed A) : NaturalFormSelector A where
  select := fun l b ↦ A.E l (s.orientationAt l b) b
  returns := fun l b ↦ A.recov l (s.orientationAt l b) b
  natural := by
    intro l m b
    rw [A.T_ext]
    unfold orientationAt
    rw [A.pi_comp, A.phi_comp]

@[simp] theorem selectorOfSeed_apply (s : RelativeFormSeed A) (l : L) (b : B l) :
    s.selectorOfSeed.select l b = A.E l (s.orientationAt l b) b :=
  rfl

/-- Move the authored context to another temporary origin.  The pointwise choice is transported,
not recomputed by an external rule. -/
def translateOrigin (s : RelativeFormSeed A) (m : L) : RelativeFormSeed A where
  origin := m
  pole := fun b ↦ s.orientationAt m b

/-- Changing the temporary origin leaves the selected natural form literally unchanged. -/
theorem selectorOfSeed_translateOrigin (s : RelativeFormSeed A) (m : L) :
    (s.translateOrigin m).selectorOfSeed = s.selectorOfSeed := by
  cases s with
  | mk origin pole =>
      apply NaturalFormSelector.ext
      funext l b
      apply congrArg (fun p ↦ A.E l p b)
      unfold translateOrigin orientationAt
      simp only
      rw [A.pi_comp, A.phi_comp]

/-- Origin changes compose and cancel through the same relative translation. -/
theorem translateOrigin_cancel (s : RelativeFormSeed A) (m k : L) :
    (s.translateOrigin m).translateOrigin k = s.translateOrigin k := by
  change RelativeFormSeed.mk k _ = RelativeFormSeed.mk k _
  congr 1
  funext b
  unfold translateOrigin orientationAt
  rw [A.pi_comp, A.phi_comp]

/-- The constant-orientation seed is a useful non-vacuous special case, not the general form. -/
def constant (origin : L) (p : Pole) : RelativeFormSeed A where
  origin := origin
  pole := fun _ ↦ p

/-- Reverse every pointwise authored pole at the same temporary origin. -/
def reverse (s : RelativeFormSeed A) : RelativeFormSeed A where
  origin := s.origin
  pole := fun b ↦ Pole.other (s.pole b)

theorem reverse_orientationAt (s : RelativeFormSeed A) (l : L) (b : B l) :
    s.reverse.orientationAt l b = Pole.other (s.orientationAt l b) := by
  unfold reverse orientationAt
  exact perm_comm_other (A.pi s.origin l) (s.pole (A.phi l s.origin b))

/-- Reversal gives a different selector whenever the frame separates its two presentations and an
identity is actually supplied. -/
theorem selector_reverse_ne (s : RelativeFormSeed A) (hsep : A.Separated)
    (l : L) (b : B l) :
    s.reverse.selectorOfSeed ≠ s.selectorOfSeed := by
  intro h
  have hAt := congrArg (fun F : NaturalFormSelector A ↦ F.select l b) h
  simp only [selectorOfSeed_apply, reverse_orientationAt] at hAt
  have hp : Pole.other (s.orientationAt l b) = s.orientationAt l b :=
    A.E_inj_pole hsep l b hAt
  exact Pole.other_ne (s.orientationAt l b) hp

/-- The distinct reversed choices are nevertheless equal under closure. -/
theorem selector_reverse_ceq (s : RelativeFormSeed A) (l : L) (b : B l) :
    CEq (A.W l)
      (s.reverse.selectorOfSeed.select l b)
      (s.selectorOfSeed.select l b) :=
  s.reverse.selectorOfSeed.selectors_ceq s.selectorOfSeed l b

/-- Their equality is therefore also exactly the derived topological identity. -/
theorem selector_reverse_topological_identity (s : RelativeFormSeed A) (l : L) (b : B l) :
    SameOpenNeighborhoods (A.W l)
      (s.reverse.selectorOfSeed.select l b)
      (s.selectorOfSeed.select l b) :=
  (ceq_iff_same_open_neighborhoods _ _ _).1 (s.selector_reverse_ceq l b)

/-- Polar reversal is an explicit movement between the original and reversed authored forms. -/
def reversalMovement (s : RelativeFormSeed A) :
    NaturalFormMovement s.selectorOfSeed s.reverse.selectorOfSeed where
  move := fun l ↦
    { toFun := A.J l
      invFun := A.J l
      left_inv := A.J_invol l
      right_inv := A.J_invol l }
  return_eq := A.J_ret
  natural := A.T_J
  carries := by
    intro l b
    rw [selectorOfSeed_apply, selectorOfSeed_apply, reverse_orientationAt]
    change A.J l (A.E l (s.orientationAt l b) b) =
      A.E l (Pole.other (s.orientationAt l b)) b
    rw [A.J_ext]

end RelativeFormSeed

/-! ## Context comes first; naturality audits the authored choice -/

/-- A context supplies its seed.  `selectorAt` below only translates and audits that supplied
choice; there is intentionally no default context and no optimizer field. -/
structure ContextualNaturalForms (A : TransFrame L B Y) (Context : Type z) where
  seedAt : Context → RelativeFormSeed A

namespace ContextualNaturalForms

variable {A : TransFrame L B Y} {Context : Type z}

def selectorAt (C : ContextualNaturalForms A Context) (context : Context) :
    NaturalFormSelector A :=
  (C.seedAt context).selectorOfSeed

theorem selectorAt_natural (C : ContextualNaturalForms A Context) (context : Context)
    (l m : L) (b : B l) :
    A.T l m ((C.selectorAt context).select l b) =
      (C.selectorAt context).select m (A.phi l m b) :=
  (C.selectorAt context).natural l m b

end ContextualNaturalForms

/-- A context change is admissible for the natural-form layer only when it carries an explicit
movement between the two contextual selectors.  Arbitrary contexts are not declared related. -/
structure ContextualSelectorMove {A : TransFrame L B Y} {Context : Type z}
    (C : ContextualNaturalForms A Context) (source target : Context) where
  movement : NaturalFormMovement (C.selectorAt source) (C.selectorAt target)

namespace ContextualSelectorMove

variable {A : TransFrame L B Y} {Context : Type z}
  {C : ContextualNaturalForms A Context} {source target : Context}

theorem carries_selection (move : ContextualSelectorMove C source target)
    (l : L) (b : B l) :
    move.movement.move l ((C.selectorAt source).select l b) =
      (C.selectorAt target).select l b :=
  move.movement.carries l b

/-- An admitted context change can be read in the inverse direction through the same witnessed
relative freedom. -/
def symm (move : ContextualSelectorMove C source target) :
    ContextualSelectorMove C target source where
  movement := move.movement.symm

end ContextualSelectorMove

/-- A continual contextual selector is the project's sensor/selection loop together with a
proof-relevant form movement at every actual step.  The sensor and update remain authored input;
closure audits their relative translation and does not manufacture their policy. -/
structure ContextualNaturalFormLoop {A : TransFrame L B Y} (Context : Type z)
    (Observation : Type*) (C : ContextualNaturalForms A Context) where
  sense : Context → Observation
  update : Context → Observation → Context
  stepMovement : ∀ context,
    ContextualSelectorMove C context (update context (sense context))

namespace ContextualNaturalFormLoop

variable {A : TransFrame L B Y} {Context : Type z} {Observation : Type*}
  {C : ContextualNaturalForms A Context}

def toLoop (D : ContextualNaturalFormLoop Context Observation C) : Loop Context Observation where
  sense := D.sense
  select := D.update

def runContext (D : ContextualNaturalFormLoop Context Observation C)
    (initial : Context) : ℕ → Context :=
  D.toLoop.run initial

/-- Every consecutive pair in the contextual run carries a witnessed relative form movement. -/
def runStepMovement (D : ContextualNaturalFormLoop Context Observation C)
    (initial : Context) (n : ℕ) :
    ContextualSelectorMove C (D.runContext initial n) (D.runContext initial (n + 1)) := by
  simpa [runContext, toLoop, Loop.step] using D.stepMovement (D.runContext initial n)

/-- Hence every selected representative at one stage is explicitly carried to the next stage's
representative over the same returned identity. -/
theorem run_carries_selection (D : ContextualNaturalFormLoop Context Observation C)
    (initial : Context) (n : ℕ) (l : L) (b : B l) :
    (D.runStepMovement initial n).movement.move l
        ((C.selectorAt (D.runContext initial n)).select l b) =
      (C.selectorAt (D.runContext initial (n + 1))).select l b :=
  (D.runStepMovement initial n).carries_selection l b

end ContextualNaturalFormLoop

/-! ## Trading bridge: selected forms plus an actual local interaction -/

/-- A trading-form witness does not choose a trade by profit.  It records that an already supplied
natural form agrees with the actual source before interaction, that the interaction carries that
selected form to its translated source reading, and that the resulting translated occurrence
agrees with the target. -/
structure SelectedTradingFormWitness {N : Network} {R : Type w}
    {I : TradingInterface N R}
    (F : NaturalFormSelector (NRRF627.flipFrame N.Reading))
    (P : TradingProblem I) where
  interaction : Interaction N
  closure_at_source :
    I.closureReturn (interaction.translate (NRRF766.sourceReading P)) =
      I.closureReturn (NRRF766.sourceReading P)
  translates :
    interaction.translate (NRRF766.sourceReading P) = NRRF766.targetReading P
  source_is_selected :
    F.select (I.perspective P.source) (NRRF766.sourceReading P) =
      I.occurrence P.source
  interaction_carries_selected :
    F.select (I.perspective P.source)
        (interaction.translate (NRRF766.sourceReading P)) =
      (interaction.translate (NRRF766.sourceReading P),
        (F.select (I.perspective P.source) (NRRF766.sourceReading P)).2)
  target_is_selected :
    F.select (I.perspective P.target) (NRRF766.targetReading P) =
      I.occurrence P.target

namespace SelectedTradingFormWitness

variable {N : Network} {R : Type w} {I : TradingInterface N R}
  {F : NaturalFormSelector (NRRF627.flipFrame N.Reading)}
  {P : TradingProblem I}

/-- The supplied source selection is carried through the actual interaction before any language
translation is applied.  This is the interaction-equivariance premise missing from a merely
post-interaction selector equation. -/
theorem source_after_interaction_is_selected
    (witness : SelectedTradingFormWitness F P) :
    F.select (I.perspective P.source)
        (witness.interaction.translate (NRRF766.sourceReading P)) =
      (witness.interaction.translate (NRRF766.sourceReading P), I.orientation P.source) := by
  calc
    F.select (I.perspective P.source)
        (witness.interaction.translate (NRRF766.sourceReading P)) =
        (witness.interaction.translate (NRRF766.sourceReading P),
          (F.select (I.perspective P.source) (NRRF766.sourceReading P)).2) :=
      witness.interaction_carries_selected
    _ = (witness.interaction.translate (NRRF766.sourceReading P),
          I.orientation P.source) := by
      have h := congrArg Prod.snd witness.source_is_selected
      simpa [TradingInterface.occurrence] using h

/-- For an already supplied problem and contextual form, interaction transport plus selector
naturality derive the existing occurrence-closing equation.  This validates the selected form; it
does not numerically choose the problem or its target. -/
theorem selected_frame_closes (witness : SelectedTradingFormWitness F P) :
    (NRRF627.flipFrame N.Reading).T
        (I.perspective P.source) (I.perspective P.target)
        (witness.interaction.translate (NRRF766.sourceReading P), I.orientation P.source) =
      I.occurrence P.target := by
  rw [← witness.source_after_interaction_is_selected]
  rw [F.natural]
  change F.select (I.perspective P.target)
      (witness.interaction.translate (NRRF766.sourceReading P)) = I.occurrence P.target
  rw [witness.translates, witness.target_is_selected]

/-- The selected natural form enters continual trading only by producing the existing local
witness.  Actual interaction and completion evidence remain mandatory. -/
def toLocalTradeWitness (witness : SelectedTradingFormWitness F P) :
    NRRF766.LocalTradeWitness P where
  interaction := witness.interaction
  closure_at_source := witness.closure_at_source
  frame_closes := witness.selected_frame_closes

theorem selected_stage_closes (witness : SelectedTradingFormWitness F P) :
    NRRF766.ClosesAt P :=
  ⟨witness.toLocalTradeWitness⟩

end SelectedTradingFormWitness

#print axioms completionEquiv
#print axioms completionMap_comp
#print axioms completionEquiv_natural_square
#print axioms ceq_iff_same_open_neighborhoods
#print axioms translationHomeomorph
#print axioms NaturalFormSelector.hold_exact_iff_ceq
#print axioms RelativeFormSeed.selectorOfSeed_translateOrigin
#print axioms RelativeFormSeed.selector_reverse_ne
#print axioms ContextualNaturalFormLoop.run_carries_selection
#print axioms SelectedTradingFormWitness.toLocalTradeWitness

end NRRF768
