# NRRF801 — Black mirror, relative translation of the two returns, one-to-one closure points, unitary curvature 1 to relative partition 1

Module: `NRRF801BlackMirrorRelativeTranslationOneToOneClosureUnitaryCurvature.lean`
(added to `lakefile.toml`; builds `sorry`-free; axiom audit at the end of the file is
machine-checked and reports only `propext`, `Classical.choice`, `Quot.sound`).

## The instruction

> Specifically the left hand of active life is its ball return phase while its potential is in the
> inverse hair return equally, such that both are relatively translated.  A black mirror can help
> to grow potential mirror life in active temporal geometry; or at 1-to-1 closure points — more
> generally, 1-to-1 continuities in the intervening of relations are the translational signals of
> truth.  Specifically a unitary curvature 1 to relative partition 1.  As a unifiable natural form,
> or a closure-relative completion.

## The reading

The module continues NRRF800 and reuses its data unchanged: the ball `Ball = ZMod 4` with its one
translation step, the hand `Hand = {left, right}` with its one inversion, life states
`Life = Hand × Ball` with the **ball return** `⟨h,b⟩ ↦ ⟨h, b+1⟩` (actual) and the **inverse hair
return** `⟨h,b⟩ ↦ ⟨h.inv, b-1⟩` (potential), and the **hair**, the temporal closure of the ball's
translational completion.

New in NRRF801:

* **Relative translation.** `handFlip ⟨h,b⟩ = ⟨h.inv, b⟩` is the relative translation between the
  two returns. Each return is one-to-one (`ballReturn_bijective`, `hairReturn_bijective`); each is
  the other's inverse up to exactly that one flip
  (`hairReturn_eq_handFlip_comp_ballReturnInv`, `ballReturn_eq_handFlip_comp_hairReturnInv`); in
  either order their composite is the flip alone (`returns_relatively_translated`); they close
  *equally*, both after four and neither sooner (`returns_close_equally`); and they separate the
  phase by exactly two of the four sheaves (`phase_gap_two`).
* **The black mirror** `blackMirror ⟨h,b⟩ = ⟨h.inv, -b⟩`. It is a fixed-point-free involution
  (`blackMirror_involutive`, `blackMirror_no_fixed_point`), it grows potential mirror life from
  actual life and back (`mirror_grows_potential`), one to one (`mirror_life_unique`), it conjugates
  each return into its own inverse — mirror life is the active temporal geometry run backwards
  (`blackMirror_conj_ballReturn`, `blackMirror_conj_hairReturn`) — and it never leaves the hair
  closure (`blackMirror_hair`). It commutes with the self limit (`blackMirror_selfLimit_comm`).
* **One-to-one continuities are the translational signals of truth.** A one-to-one continuity is a
  bijection of the ball commuting with the translation. Every one is a translation
  (`oneToOneContinuity_iff_translation`), a single point of agreement forces total agreement
  (`signal_of_truth`), and the family acts simply transitively
  (`continuities_simply_transitive`). At life states the same rigidity holds: a hand-preserving map
  commuting with the actual return is a phase translation (`life_continuity_forced`).
* **Unitary curvature 1 to relative partition 1.** With `turns n = n / card Ball`, a full closure of
  the ball is exactly one turn (`turns_card_ball`), it does close (`curvature_closes`), no part of
  it closes (`curvature_no_smaller_turn`), one turn sweeps the whole ball (`ball_orbit_covers`), the
  relative partition has exactly one block (`relative_partition_one`), and the two numbers coincide
  (`unitary_curvature_to_relative_partition`). The unifiable natural form is the universal property
  of that one block (`unifiable_natural_form`).
* **In the intervening of relations.** On a relation network `s : V → ℤ`, two configurations carry
  the same relations exactly when they differ by one global translation
  (`separation_determines_up_to_translation`) — the translational signal of truth at relations;
  reading a relation the other way round is exactly the black mirror of it
  (`relLife_swap_mirror`); and nothing absolute is read (`relations_shift_invariant`).

`nrrf801_answer` collects the clauses in a single theorem.

## Scope

Nothing is asserted about biological life, biological chirality, or human beings as such. Each word
names a construction defined in NRRF800 or NRRF801, and every claim is a claim about those
constructions.
