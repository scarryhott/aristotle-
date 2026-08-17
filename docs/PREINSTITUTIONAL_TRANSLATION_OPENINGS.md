# Pre-institutional translation: formal openings

## Foundational alignment

The metaphysical ordering adopted by this project is:

```text
relational translation / relative asymmetry
  -> local appearance as language, definition, axiom, geometry, institution,
     Turing presentation, or topological presentation
  -> interactive choices of translation, return, orientation, and extension
  -> coherence audit
  -> relative closure, obstruction, or OPEN
```

Translation is therefore not merely a morphism between already fixed languages.
It is the prior relational condition under which a language or institution can
appear as a local, temporarily fixed perspective. This is a **foundational
interpretation**. The present Lean kernel begins later, with explicitly supplied
local frames and translations; it does not yet formalize this priority claim.

## Formal openings

### O1 — pre-institutional translation structure

Define a structure whose primitive data are relative relational translations,
composition/return opportunities, and asymmetry/orientation witnesses—without
starting from a fixed global signature category or institution. Then define a
local language, institution, axiom geometry, or equality as a representation
of that structure.

Success would give a map:

```text
PreTranslation representation -> local InstitutionFrame / TransFrame
```

It would not make every local representation equivalent or remove local
obstructions.

### O2 — interactive choice and constraint cost

Formalize a candidate choice as data made in a local interaction, before any
naturality verdict. Specify a proof-relevant ledger of commitments,
counterexamples, exclusions, and required repairs. Only then define the
conditions under which the choice is natural, obstructed, or open.

No numeric “choice cost” is currently defined. A cost functional must not be
introduced until its invariance and relation to the registered proof obligations
are explicit.

### O3 — relative gluing reversal controls

For overlapping intervals, retain both ordinary controls:

```text
f_0(x) = x, f_1(x) = x       -- literal overlap agreement
g_0(x) = 0, g_1(x) = 1       -- literal overlap disagreement
```

Add a translation interface, return, and equality relation. Test, rather than
assume, whether a relative returned identification can complete the second
case, or whether an added translation constraint obstructs the first. Any such
result requires preservation, reflection, and explicit witnesses; it is not
ordinary sheaf gluing with renamed vocabulary.

### O4 — inverse-limit-style relative closure

Given a diagram of local appearances and registered translations, define the
object of compatible cones/returns. A relative closure claim should distinguish:

```text
coherent compatible cone       -> candidate inverse-limit realization
no compatible cone             -> explicit translational obstruction
insufficient interface/evidence -> OPEN
```

This does not assert that a global inverse limit exists, nor that the resulting
object is a privileged global language. It records only the compatible relation
available from a particular diagram.

### O5 — Turing/topos mutual realization

Specify two local presentations—computational and categorical/topological—with
translations in both directions. State exact factorization, preservation, and
reflection obligations. Test their composite rather than identifying “Turing”
and “topos” by metaphor. A failed composite is a valuable obstruction result.

### O6 — local geometry/global axiom-basis realization

State when a local maze geometry realizes a global axiom basis, and conversely,
only through a named translation and return. The current finite maze is a
bounded proxy; it cannot establish the general equivalence.

## Relation to existing work

`TransFrame`, `GeomEquiv`, and institution/Hets comparison are downstream
candidate representations. They are useful once local frame data are supplied,
but they must not be presented as deriving the pre-institutional translational
condition. See [Open translational foundation](OPEN_TRANSLATIONAL_FOUNDATION.md)
and [Institutions, interactive proof, and relative closure](INSTITUTIONS_INTERACTIVE_PROOF_COMPARISON.md).
