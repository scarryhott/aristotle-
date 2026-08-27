# NRRF798 — Unifying the full closure through translational truth

Companion notes to `NRRF798UnifyFullClosureThroughTranslationalTruth.lean`
(registered in `lakefile.toml`; builds cleanly, no `sorry`, no warnings, with a machine-checked
axiom audit at the end of the file — every headline result depends only on `propext`,
`Classical.choice`, `Quot.sound`).

## The instruction

> Unify full closure through translational truth.

Nothing new is assumed. The two halves that the earlier modules built — the relational half
(`LocalRel` with the scale reading `divg`, the hair reading `hair`, the neutral sector) and the
sensor half (the loop-sensor `State` with `gaugeClass`, `Test`, `qgConfig`) — are placed under one
notion, and the whole closure is recovered from it.

## The one notion

For a translation relation `s` on presentations, a truth `T : P → Prop` is **translational** when
translation carries it: `s.r p q → (T p ↔ T q)`. A reading is translational when translation does
not move its value.

Proved once, in general, and used three times:

- `truthEquiv` — an explicit bijection `{T // Translational s T} ≃ (Quotient s → Prop)`: the
  translational truths *are* the truths of the closure, no more and no less.
- `related_iff_all_translational` — the closure is recovered from its truths: two presentations
  are translations of one another exactly when every translational truth agrees on them. So
  translational truth is neither coarser (it separates: `translational_separates`) nor finer
  (that is the definition) than the closure.
- `translational_not / and / or / imp / forall / exists`, `translational_const`,
  `translational_rel` — the translational truths are closed under the whole propositional and
  quantificational apparatus. They form a full logic, not a fragment.
- `translational_iff_reading`, `quotEquivOfReading` — if a reading decides translation, then
  translational truth is exactly truth about that reading, and the closure is exactly its range.

## The relational half

`relTr A B := Neutral (A - B)`: the translations are the neutral relations, the ones no reader
sees.

- `relTr_iff` — translation is *exactly* agreement of `relRead = (divg, hair)`.
- `relQuotEquiv : Quotient relSetoid ≃ ℝ × (Fin 3 → ℝ)` — the relational closure is the ball–hair
  pair, and every pair is realised (`relRead_surjective`, witness `relRep`).
- `rel_truth_iff` — its translational truths are exactly truths about `(divg, hair)`.
- `neutral_invisible`, `rel_closure_nontrivial` — the quotient is genuine: the neutral sector is a
  nonzero move of the presentation invisible to every translational truth.
- `relInv_descends` — the one inversion of NRRF796 descends to the closure: it is a symmetry of
  translational truth (scale flips, hair does not).

## The sensor half

`stateTr k x y := gaugeClass k x = gaugeClass k y`.

- `stateTr_iff_tests` — translation is exactly "passes every loop test".
- `stateTr_iff_qgConfig` — and exactly "has the same geometric configuration `qgConfig`". The
  discrete sensor picture and the continuous relational picture define the *same* translation
  relation; they were never two relations.
- `stateQuotEquiv : Quotient (stateSetoid k) ≃ ℤ × ZMod k`, `state_truth_iff` — the sensor closure
  is the gauge-class space and its truths are the truths about the gauge class.
- `hair_shift_invisible`, `state_closure_nontrivial` — the hair period is a nonzero move invisible
  to every translational truth: the phase returns.

## The full closure

On `Full := LocalRel × State`, `fullTr k` is translation in each half.

- `fullTr_iff_read`, `fullQuotEquiv`, `full_truth_iff` — the full closure is exactly the range of
  the single reading `fullRead k = ((divg, hair), gaugeClass k)`, that reading is onto
  (`fullRead_surjective`), and a truth of the whole is translational exactly when it is a truth
  about it.
- `rel_truth_embeds`, `state_truth_embeds` — each half's translational truths sit inside the
  whole.
- `full_separated_by_sectors` — and the two halves already separate everything the whole
  separates: whenever two full presentations are not translations of one another, a truth of one
  of the two halves, pulled back, tells them apart. No third sector is needed to close the theory.
- `gravRel_morphism`, `embed_translational` — the halves are linked, not merely juxtaposed: the
  gravitational relation of a state is a morphism of closures, and a state translates to another
  exactly when its full presentation `(gravRel x, x)` does.

`nrrf798_unification` collects the nine clauses in a single theorem, for every hair period
`k > 0`.

As throughout this project, the physical words name the constructions defined in the Lean modules;
every claim above is a claim about those constructions.
