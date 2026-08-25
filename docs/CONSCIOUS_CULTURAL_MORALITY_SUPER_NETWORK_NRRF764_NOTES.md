# Conscious cultural morality super-network — NRRF764 companion

## Status and scope

This note records the intended reading of
`NRRF764ConsciousCulturalMoralitySuperNetwork.lean`. It is a companion to the
formal source, not an independent proof. The registered project and the source
both build with warnings treated as errors. `#print axioms NRRF764.nrrf764_answer`
reports `[propext, Quot.sound]`; the source declares no `axiom` and contains no
`sorry`.

NRRF764 begins with interaction. It does **not** assume a universal machine, a
halting oracle, a monetary order, a social hierarchy, or a pre-existing global
ledger. Its carrier types are arbitrary. “Consciousness,” “culture,” and
“morality” name fields of the formal interface; they are not empirical claims
about psychology or society.

## 1. One loop of sensor and selection

A `Loop S Obs` has only two operations:

```text
sense  : S -> Obs
select : S -> Obs -> S
```

`step` feeds the sensed observation back into selection, and `run` iterates
that step. A finite history and its residual continuation are two views of one
stream. `splitEquiv n` expresses this directly:

```text
(Nat -> S)  ~=  (Fin n -> S) x (Nat -> S).
```

`continued_run` says that the tail is again a run of the same loop.
`halts_iff_continuation_const` reads halting as eventual constancy of that
continuation. Nothing in this construction assumes Turing completeness.

Two boundary results prevent that reading from being inflated:

- `no_universal_selection` is Cantor diagonalization for binary-valued
  selections. It is not a theorem about the non-existence of every possible
  programming language or physical computer.
- `no_finite_halting_test` says no test of a fixed finite stream prefix decides
  eventual constancy for all streams. It is not a replacement proof of the
  classical machine halting theorem.

## 2. Indeterminate strings and authorship

An `Ind` assigns a still-open type of possibilities to every position. Its
potential determinations factor positionwise:

```text
Det I = (i : I.Position) -> I.possibility i.
```

`detEquivPi` exposes that factorization. In the finite case, `card_det` counts
the product of the local choices. `det_nonempty` uses choice to obtain a
determination when every position is inhabited. `agree` and `equalize` compare
readings position by position.

Authorship then restricts the possible determinations to those agreeing with
one selected determination. `mem_det_collapse_iff` gives the membership
criterion and `det_globalCollapse_unique` says that after global authorship no
further discretion remains. This is a collapse of a supplied possibility
family; it does not assert that nature, society, or a market has a uniquely
authored state.

## 3. Network as a shared interactive field

A `Network` supplies:

```text
Site, Reading
read    : Site -> Reading
admits  : Reading ~= Reading
shared  : Set Reading
```

Every site reading is shared, and admission preserves the shared field. In the
intended language, `read` is consciousness, `shared` is culture, and the
invertible `admits` operation is morality. These are names for a typed
structure, not an external authority.

The historically named `ruleOf` is a unary admitted-site set, not a binary
order relation. It contains every site, so `ruleOf_eq_top` makes that predicate
universal. `authority_does_not_exclude` says that an independently supplied
rank or standing cannot remove a site reading from this shared field.
`networks_not_determined_by_order` (also a legacy name) exhibits two networks
with the same universal admitted-site set but different readings. The proved
claim is therefore that this admission predicate does not determine the
network—not a theorem about every possible monetary, legal, or social order.

## 4. Interaction, memory, and connection

An `Interaction N` is an endotranslation of readings which preserves the
shared field and commutes with admission. A list of interactions acts on a
reading as memory. `memory_admissible` keeps that result in the shared field.

Connection records the multiset of interactions. It is additive under append,
monotone under extension, and invariant under permutation (`conn_append`,
`conn_subset_append`, and `conn_of_perm`). Only this connection record is
order-independent. The iterated memory state need not be order-independent
unless extra commutation hypotheses are supplied.

## 5. Translation, reinterpretation, and unity

A translation maps sites and readings between networks while respecting
reading, admission, and sharedness. Translations have identity and
composition. A `Reinterp N` is an invertible, admissible self-translation; it
carries interactions by conjugation, so a change of presentation retains the
interaction structure.

The `unity` network has one site and one reading. `unity_terminal` gives the
unique structure-preserving translation from any network into it. This is a
categorical terminality statement: it does not claim that every source network
is identical, that its local distinctions disappear internally, or that no
other isomorphic presentation of a terminal object can exist.

## 6. Operators derived relative to interaction

The module identifies, rather than postulates separately, the main operational
readings:

- a run is iteration of the sensor-selection step (`run_eq_stepLoop_run`);
- a reinterpretation yields an interaction;
- one interaction is one-step memory;
- a finite memory can be packaged as a composed interaction.

The architecture therefore treats problems as shared readings and solutions
as admissible interactions. It does not identify a solution with a numerical
reward merely because it closes formally.

## 7. The 0–infinity polar closure

`PolarPoint R` presents a unit and two rays with a common radius. Polar
reversal exchanges the two ray orientations and fixes the unit. The relation

```text
x ~ y  iff  y = x or y = polar(x)
```

is the closure relation. It identifies the paired zero and infinity
orientations (`zero_rel_top`) while retaining the radius. Equality of radii is
the numerical reading of the same relation (`rel_iff_radius`). Quotienting by
the relation gives `ZeroInfClosure R`, equivalent to the retained optional
radius (`zeroInfClosureEquiv`). `poles_admissible` reads the two polar sites as
one shared admissible field.

This is a deliberately constructed quotient model. It does not prove that
ordinary extended-real zero equals ordinary extended-real infinity, nor that
an empirical magnitude vanishes.

## Properties map

| Reading | Formal object or result | Boundary |
|---|---|---|
| sensor and selection | `Loop`, `step`, `run` | no universal-machine assumption |
| past and continuation | `splitEquiv`, `continued_run` | one stream, two presentations |
| halting | `halts_iff_continuation_const` | eventual constancy only |
| finite-test obstruction | `no_finite_halting_test` | fixed-prefix tests only |
| potential determination | `Ind.Det`, `detEquivPi` | choice is explicit where used |
| authored collapse | `det_globalCollapse_unique` | relative to a selected authoring |
| shared field | `Network` | carries no monetary or legal order |
| admissible change | `Interaction` | preserves sharedness and admission |
| latent memory | `memory_admissible` | order can matter to the resulting state |
| connection | `conn_of_perm` | only the multiset record forgets order |
| perspective change | `Reinterp` | invertible admissible relabelling |
| one closure | `unity_terminal` | categorical terminality |
| polar completion | `ZeroInfClosure` | quotient model, not scalar annihilation |

The collected theorem `nrrf764_answer` packages these seven sections. The Lean
source remains authoritative for its exact statement and axiom report.
