# NRRF790 — Complete and incomplete are natural selections and forced isolations respectively

Module: `NRRF790CompleteNaturalSelectionIncompleteForcedIsolation.lean` (registered in
`lakefile.toml`; builds cleanly, no `sorry`, no warnings, with a machine-checked axiom audit at the
end of the file).

## The setup

A **reading** of a datum is a predicate `P : S → Prop` on a field of symbols: which symbols the
datum admits. Nothing else is assumed — no coding, no order, no measure.

* `Complete P` — exactly one symbol is admissible (`∃! s, P s`).
* `Symmetry P e` — a permutation `e` of the symbol field that preserves admissibility.
* `NaturalSelection P c` — `c` is admissible and is fixed by *every* symmetry of the reading: the
  reading itself makes the selection, nothing is added on top of it.
* `Isolate c` — the reading strengthened to the single symbol `c`.
* `ForcedIsolation P c` — `c` is admissible and isolating it is a **strict** strengthening: symbols
  the reading admits are cut away by the choice.

## What is proved

**Complete = naturally selected.** `complete_iff_exists_naturalSelection`: a reading is complete
iff it carries a natural selection. The forward direction is immediate; the converse is the
symmetry argument — if a second symbol were admissible, the transposition exchanging it with the
selection would be a symmetry of the reading moving the selection. The selection is then unique
(`naturalSelection_unique`), it is the completing symbol (`theSelection`), and it is fixed by every
symmetry (`theSelection_symm_fixed`).

**Incomplete = forced isolation.** For an incomplete reading, *every* admissible symbol is a forced
isolation (`forcedIsolation_of_not_complete`), and conversely a forced isolation witnesses
incompleteness (`not_complete_of_forcedIsolation`). Each forced isolation cuts away a genuinely
admissible symbol (`exists_other_admissible`) and is broken by an explicit symmetry of the reading
(`exists_symmetry_moving`). On an admissible symbol the two notions are exact negations of one
another (`naturalSelection_iff_not_forcedIsolation`), and no symbol is both
(`not_natural_and_forced`). An empty reading selects nothing at all (`no_selection_of_empty`):
total isolation from the field.

**Completing is isolating.** `complete_sub_iff_isolate`: a strengthening of a reading is complete
exactly when it is the isolation of one admissible symbol. So the completions of an incomplete
reading are precisely its isolations — there is no third way to complete it.

**The dichotomy and naturality.** `complete_dichotomy` splits every reading into the naturally
selected case (unique natural selection) and the forcibly isolated case (every admissible symbol a
forced isolation). Selection is natural in the symbol field: complete readings transport along
injective translations (`complete_map`) and the selection transports with them
(`theSelection_map`).

**No selector without completeness.** `no_natural_selector`: on a field with at least two symbols
there is no equivariant choice function defined on all non-empty readings. Away from completeness,
every choice is an isolation imposed from outside.

**Stagewise form.** In the NRRF775 language of constraints, rigidity is exactly stagewise
completeness (`rigid_iff_forall_complete`), the NRRF775 natural form is the stagewise natural
selection (`sel_naturalSelection`), a non-rigid stage forces isolation
(`forcedIsolation_of_not_rigid`), and such a stage carries no natural selection at all
(`exists_stage_without_selection`).

**Concrete readings.** On `Bool`: the reading `· = false` is complete with natural selection
`false`; the total reading is incomplete, both of its symbols are forced isolations, and it carries
no natural selection.

`nrrf790_answer` collects the clauses into one statement.
