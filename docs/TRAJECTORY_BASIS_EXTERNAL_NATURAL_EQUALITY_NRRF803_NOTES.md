# NRRF803 — Trajectory and basis are relative to their external forms of natural equality

Module: `NRRF803TrajectoryBasisRelativeExternalNaturalEquality.lean` (builds `sorry`-free; axiom
audit at the end of the file is machine-checked: only `propext`, `Classical.choice`, `Quot.sound`).

## The reading

A system is a type `X` with a return `step : X → X`. A **form of equality** on `X` is a setoid `E`.
It is *external*: it is not part of the data `(X, step)`, it is supplied from outside, and the same
system admits many of them. A form is **natural** for the return when the return does not move it,
`x ≈ step x` (`IsNatural`).

Relative to such an external form — and only relative to one — the two notions of the instruction
are defined:

* **trajectory** — `Traj step E x`, the set of `E`-classes visited by the forward orbit of `x`;
* **basis** — `IsBasis E b`, a family that spans (`∀ x, ∃ i, b i ≈ x`) and is independent
  (`b i ≈ b j → i = j`).

## What is proved

**§1 Forms of natural equality.** The closure of NRRF802 is a natural form (`natural_returnSetoid`)
and the finest one (`returnSetoid_finest`); a natural form is blind to any number of returns
(`natural_iterate`); hence every external form of natural equality is a quotient of the closure, via
a canonical map commuting with the class maps (`factor`, `factor_cl`).

**§2 Trajectory.** `mem_traj` and `sameTraj_iff` identify the set form and the relational form of
"same trajectory". Relative to *any* natural form the trajectory of a point is a **single point**
(`traj_natural`), and `E`-equal points have the same trajectory (`traj_congr`). Sameness of
trajectory is a function of the relation alone: two forms with the same relation give the same
answer (`sameTraj_congr_setoid`). The trajectory relative to any natural form is the image of the
trajectory relative to the closure under the factoring map (`traj_factor`). And trajectory is not
absolute: on `(ℕ, succ)`, `0` and `1` have the same trajectory relative to the translational form
and different trajectories relative to bare equality (`traj_not_absolute`).

**§3 Basis.** A basis for `E` is exactly an indexing of the quotient (`isBasis_iff_bijective`);
being a basis is a function of the relation alone (`isBasis_congr_setoid`); a basis stays a basis
when each vector moves inside its class (`basis_congr`); every external form has a basis
(`exists_basis`); the index type of a basis is the quotient (`basis_equiv_quotient`); any two bases
for the same form are matched by **exactly one** reindexing (`basis_unique_up_to_reindex`). Basis is
not absolute either: on the two-point system with the identity return, bare equality and total
equality are both natural, and the identity family is a basis for the first and not for the second
(`basis_not_absolute`). Read through the closure, a basis is a bijective indexing of the factored
classes (`isBasis_iff_factor_bijective`).

**§4** `nrrf803_answer` collects the clauses.

Nothing is asserted beyond the definitions made in this module and in NRRF802: every claim is a
claim about those definitions.
