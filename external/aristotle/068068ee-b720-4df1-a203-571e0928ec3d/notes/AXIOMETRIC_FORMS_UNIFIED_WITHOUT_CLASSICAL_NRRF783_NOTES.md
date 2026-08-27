# NRRF783 — The full unification of the axiometric forms, without classical logic

**Claim formalised.** The development's unification of the axiometric forms does not need classical
logic: it can be carried through with no excluded middle and no axiom of choice, and the claim is
machine-checked rather than asserted.

## The files

| File | Role |
|---|---|
| `NRRF783AxiometricFormsUnifiedWithoutClassical.lean` | The unified system of closure equations, forms and derivations, developed with **no `import` line at all** — nothing but Lean's kernel and `Init` is in scope, so no library definition can smuggle a classical principle in. |
| `NRRF783TranslationalTruthFormsWithoutClassical.lean` | The second strand — translational truth, closures of readings, potentials — developed constructively, and joined to the first: a translational closure **is** an axiometric form, and it closes. |
| `NRRF783BridgeConstructiveFormsNRRF739NRRF740.lean` | The connection to the project's own closure object (`NRRF739.Closure`): the two presentations are definitionally the same, and the three places where NRRF740 used `Classical.choice` are identified and replaced. |
| `NRRF783BridgeTranslationalTruthNRRF782.lean` | The connection to the project's own translational-truth module NRRF782, with choice-free replacements for its classical steps. |

Every headline statement in all three files is pinned with `#guard_msgs in #print axioms`, so the
**build fails** if `Classical.choice` ever enters one of these proofs. The only axioms that occur
anywhere are `propext` and `Quot.sound` — propositional extensionality and the axiom behind
function extensionality — neither of which is a classical principle.

## What "not needing classical" is shown to mean

1. **No classical axiom is used.** Audited statement by statement (§9 of the core file, §6 of the
   translational file, §5 of the bridge).

2. **The choice a classical treatment would need is already part of the datum.** An axiometric form
   is not "a surjection whose section must be chosen"; it is a pair `(encode, eval)` with
   `eval ∘ encode = id`. So:
   * `Closure.fibre` produces an actual element of each fibre of the evaluation, as data;
   * `familySection` sections a whole indexed family of forms at once, with no choice principle;
   * `form_choice` (and its data-level version) is a *theorem*: the section is the encoding.

3. **The classical steps that were there are removable.** Auditing NRRF740 shows that
   `unified_return`, `unified_hold_idem`, `closes_iff_transparent`, `admissible_iff_closure`,
   `forms_are_exactly_idempotents`, `source_rule_complete` and `deriv_admissible` were already
   choice-free. `Classical.choice` entered at exactly three places:

   | classical statement | why | choice-free replacement |
   |---|---|---|
   | `NRRF739.Closure.unique_section_iff_transparent` (admission neutrality) | `by_contra` | `unique_section_iff_transparent_constructive`: excluded middle replaced by decidable equality of the encoded readings, and the competing encoding written down explicitly |
   | `NRRF740.unified_closing_readings` (the five readings of `(U3)`) | inherited the above; used the finite-carrier level | `unified_closing_readings_constructive`: all five readings, with the level replaced by emptiness of the **defect** (the readings the hold moves) — no finiteness, no cardinal arithmetic |
   | `NRRF740.fourfold_by_closing` (point / line / loop / twist) | library witnesses carrying classical instances | `fourfold_by_closing_constructive`: the two failures are witnessed by explicit moved readings (`false` for the loop, `0` for the twist) |

   `nrrf740_answer_without_classical` then restates NRRF740's headline unification for the
   project's own closure object and proves it with `propext` and `Quot.sound` only.

## The system, unchanged

For `encode : A → B` (recursion) and `eval : B → A` (fixed), with `hold = encode ∘ eval`:

```
(U1)  eval ∘ encode = id_A      the return equation    -- the only postulate
(U2)  hold ∘ hold  = hold       the holding equation   -- derived
(U3)  encode ∘ eval = id_B      the closing equation   -- may fail; its failure is the level
```

* **Forms are exactly the idempotents** (`forms_are_exactly_idempotents`), and the witnessing form
  is *constructed* from the idempotent (its fixed readings are the carrier), not chosen.
* **One rule generates all solutions** (`source_rule_complete`): every form is the source form of
  its own evaluation.
* **Every derivation is admissible** (`deriv_admissible`), by construction: the derivation system
  `Deriv` has identity, source, fold and composition rules, and no rule appeals to a choice
  principle.
* **The fourfold** is separated by `(U3)` alone, by explicit witnesses.
* **Closing is stable**: `¬¬ Closes c → Closes c` whenever equality of readings is stable, in
  particular on carriers with decidable equality (`transparent_stable`,
  `closes_stable_of_decidableEq`). So passing to classical logic proves nothing new about the
  closing of a form: there is no double-negation gap for the axiometric forms.

## The translational strand

Levels are given as data (`AddGroupStr`: an additive commutative group written out by hand rather
than imported). For readings `x y : ι → G`, translational truth is `∃ g, ∀ i, y i = x i + g`.

* it is reflexive, symmetric, transitive, and a reading lies in its own closure;
* **closure equality is translational truth** (`closure_eq_iff_transTruth`);
* **overlapping closures are equal** (`closure_eq_of_overlap`) — this is the constructive content
  of "equal or disjoint": the dichotomy would have to *decide* translational truth, and the
  development never needs it;
* the shift is unique at any site (`shift_unique`), relative potentials are invariant on a closure
  (`potential_invariant`) and determine it (`potential_complete`), while individual levels are not
  absolute (`value_not_absolute`, with the moving reading exhibited);
* **the two strands are one**: `closureForm` presents the closure of a reading as an axiometric
  form whose encoding is the shift action and whose evaluation reads the shift off at a base site,
  and `closureForm_closes` proves that this form satisfies `(U3)`. Reading the shift off is a
  computation, not a choice — the site is taken as data instead of extracted from a bare
  non-emptiness assumption.

## The translational bridge to NRRF782

A Mathlib additive commutative group supplies the level data of the constructive development, and
under it the two notions of translational truth and of closure coincide *definitionally*
(`transTruth_iff`, `mem_closure_iff` are both `Iff.rfl`). The audit shows that NRRF782's
`closure_eq_iff_transTruth`, `exists_unique_closure`, `potential_invariant`, `value_not_absolute`
and `transTruth_transEq` were already choice-free, and that `Classical.choice` entered in exactly
two ways, both replaced:

| classical statement | why | choice-free replacement |
|---|---|---|
| `NRRF782.closure_eq_or_disjoint` | the dichotomy must *decide* translational truth | `closure_eq_of_overlap`: a shared reading forces equality |
| `NRRF782.shift_unique`, `closureEquiv`, `closure_mk_eq`, `sizes_absolute`, `potential_complete`, `cocycle_iff_potential` | `[Nonempty ι]` used to produce a site, and existentials used to produce a shift | `shift_unique_at_site`, the **computable** `closureEquivOfSite : G ≃ Closure x`, `closureIsoOfSite`, `potential_complete_at_site`, `cocycle_iff_potential_at_site` — the site is taken as data and the shift is computed |

`nrrf782_answer_without_classical` collects the strand, choice-free.
