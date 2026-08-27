# NRRF796 — Self limit and inversion equality from translational nature; entanglement, superposition, singularities and thermodynamic demons as one hair of the closure ball

Module: `NRRF796SelfLimitInversionEqualityOneHairClosureBall.lean` (registered in `lakefile.toml`;
builds cleanly, no `sorry`, no warnings, with a machine-checked axiom audit at the end of the file
— every headline result depends only on `propext`, `Classical.choice`, `Quot.sound`).

The reading being formalised:

> The theory is about self limit and inversion equality from translational nature — concerning
> also entanglement, superposition, singularities and thermodynamic demons as one hair of the
> closure ball.

Everything is stated inside the ball–hair geometry already built in the earlier modules: a **local
relation** `A : LocalRel` is the translational data of the closure at a point (a real `3 × 3`
matrix), read by the scale reading `divg` and the ball/hair reading `curl` (equivalently
`hair = curl / 2`), with the shear sector left over as the neutral field.

## 1. Inversion, and inversion equality

Translational nature supplies exactly one inversion: the return `relInv A = -Aᵀ` — exchange the
two ends of a translation, then reverse it. It is a linear involution, and it splits the two
readings:

* `divg_relInv` — the scale reading is **reversed**: `divg (relInv A) = -divg A`;
* `curl_relInv`, `hair_relInv` — the hair reading is **equal**: `curl (relInv A) = curl A`. This is
  the inversion equality.

Its fixed sector is exactly the hair sector (`relInv_fixed_iff`, `relInv_fixed_is_hair`), its
anti-fixed sector exactly the return-symmetric sector (`relInv_antifixed_iff`), and the even and
odd parts of a relation under the inversion are exactly its hair form and its return-symmetric
form (`relInv_even_part`, `relInv_odd_part`).

The inversion is not a choice: any linear map that fixes every ball direction and reverses the
return-symmetric sector *is* `relInv` (`relInv_forced`).

## 2. The self limit

`self_limit_equality`: for every local relation,

```
divg A ^ 2 / 3  +  (∑ i, curl A i ^ 2) / 2  +  nrm2 (shearPart A)  =  nrm2 A
```

The two readings never exceed the relation's own translational content, and the exact deficit is
the neutral field. Consequences:

* `divg_self_limit` : `divg A ^ 2 ≤ 3 * nrm2 A`;
* `curl_self_limit` : `∑ i, curl A i ^ 2 ≤ 2 * nrm2 A`;
* `divg_self_limit_saturated_iff` : the scale reading saturates exactly on the pure scale sector
  (`A = dilPart A`);
* `curl_self_limit_saturated_iff` : the hair reading saturates exactly on the pure hair sector
  (`A = rotPart A`);
* `self_limit_joint_saturated_iff` : the two together saturate exactly when the neutral residue is
  zero.

The limit is inversion-invariant (`nrm2_relInv`, `self_limit_inversion_invariant`): the self limit
and the inversion equality are two faces of one fact.

## 3. One hair

`hair_forced` / `hairReading_unique`: there is only one hair reading. Any linear reading blind to
the return-symmetric sector and faithful on ball directions is `hair` — so the four phenomena below
are not four readings but one.

* **Entanglement** is the order defect `entangle A B = A * B - B * A` of two translations. It
  carries no source at all (`divg_entangle`), it is pure hair, its hair is antisymmetric in the
  pair (`hair_entangle_comm`), it vanishes exactly on commuting pairs (`entangle_eq_zero_iff`), and
  it is genuinely nonzero (`entangle_hair_nontrivial`).
* **Superposition** is the linearity of that same hair (`hair_add`, `hair_smul`), including
  destructive interference: two relations with nonzero hair whose superposition is hairless, and
  whose superposition is nevertheless a nonzero neutral field (`hair_interference`).
* **Singularities** are one hair direction. The seam field's hair is `tan t • v` for every `t`
  (`hair_seamField`, `singularity_one_direction`): the blow-up on the approach to the seam happens
  along that one direction and no other (`singularity_unbounded`), and at the seam itself the hair
  is extinguished (`singularity_self_limits`).
* **Thermodynamic demons** get nothing. A demon is a linear action that leaves the hair exactly as
  it found it and never loses source on the neutral field (`Demon`). Then it gains no source there
  either (`demon_no_free_source`) and maps the neutral field into itself
  (`demon_preserves_neutral`, `demon_gains_nothing`) — the reason is precisely the inversion
  equality: the neutral field is symmetric under reversal (`neutral_relInv`), so a linear gain
  would have to be its own negative. A demon also respects the self limit (`demon_self_limit`).

`nrrf796_answer` collects the clauses.

## Scope

Nothing here is asserted about physical entanglement, quantum superposition, spacetime
singularities or Maxwell's demon as such: each word names the construction defined in the module,
and every claim is a claim about those constructions.
