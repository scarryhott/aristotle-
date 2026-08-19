# Institutions, interactive proof, and relative closure

## Status

**Research comparison and integration plan — not a theorem of this checkout.**

This note situates the translational framework beside institution theory and
Hets. Institutions are treated as downstream local representations of the
foundational translational relation, not as the relation's metaphysical source.
It does not claim that the current runtime implements Hets, that every
translation is an institution morphism/comorphism, or that a Phase B/C outcome
is already a sheaf-cohomology or model-amalgamation invariant.

## The proposed correspondence

| Translational framework | Institution-theoretic candidate | Required formal work |
| --- | --- | --- |
| local definitions, axioms, and language qualities | a local institution/theory representation | derive/define the representation from the prior translation structure, then specify signatures, sentences, models, and satisfaction |
| translation as globally available but frame-relative | institution morphism/comorphism in an indexed network | prove the satisfaction condition and composition law |
| local/global closure | indexed institution and its Grothendieck globalization | define the index category and the precise global object |
| interactive proof/review | heterogeneous proof management over a development graph | preserve proof obligations and provenance through translations |
| truth-conditioned admission / choice-naturality constraint | a chosen section/return plus commuting naturality squares | register a choice before evaluation; treat naturality as a post-choice constraint and test whether the relation continues |
| relative topological closure | an additional topology/closure layer over the network | define it independently; it is not supplied by a colimit alone |

Hets is directly relevant because it supports heterogeneous specifications,
logic translations, static analysis, development graphs, and proof management.
Its documented logic interface is institution-based; the tool is therefore a
candidate execution surface for a future adapter, not a substitute for the
current causal protocol.

## The crucial distinction: construction versus admissible gluing

Grothendieck institutions globalize indexed local institutions and carry
results about theory colimits, free constructions, exactness/model
amalgamation, and inclusion systems. A colimit is a construction of a global
specification when the relevant diagram and colimit exist. It does **not**, by
itself, establish that a proposed comparison preserves and reflects the local
relations selected by this programme.

The more precise comparison target is therefore **model amalgamation/exactness
and interpolation under a registered translation interface**:

```text
registered local frames + admissible translations
  -> test satisfaction/naturality and model amalgamation conditions
  -> either construct an admissible global model
     or retain the failed condition/witness as an obstruction
```

This is where the programme's non-promotion rule belongs. A partial admitted
interface may be useful without entitling a whole-frame equivalence claim.

## Reading the current Aristotle evidence correctly

The Phase B3 record says only that a frozen 34-role declaration interface was
accepted after identity-independent validation; Phase C1 adds local return
evidence. A frozen structural failure blocks whole-frame equality and
`GeomEquiv`. These records do **not** yet establish any of the following:

- a diagram of institutions or a Grothendieck institution;
- an institution morphism/comorphism satisfying the satisfaction condition;
- a pushout/colimit or a failed model-amalgamation square;
- a sheaf, descent datum, Čech cocycle, or `H¹` obstruction;
- semantic completeness of the local or global logic.

Accordingly, “34/36 roles glue” is only an informal shorthand and must not be
used in formal claims. The committed evidence index remains authoritative for
the exact Phase B/C statements.

## Choice, naturality, and relative completeness

The intended foundational claim can be made testable without treating a local
language as globally privileged:

```text
translation category: globally available relation of comparison, not a
                      privileged language
local frame: definitions, axioms, equality, and questions
registered choice/return: a frame-relative section or witness
admissibility: naturality/commutation against declared translations, with failures retained as transformation burdens/obstructions
closure: local-to-global completion only when those obligations hold
```

Here “complete” must always name its target property: for example, completion
of a registered return square, exact realization of an admitted equality, or
model amalgamation for a specified signature diagram. It must not be read as
an unrestricted logical-completeness or metaphysical-completeness claim.

The accompanying [open-foundation note](OPEN_TRANSLATIONAL_FOUNDATION.md)
explains why this framework does not posit a single global topos: translation
is globally available as a relation of comparison, while definitions and
geometries remain local. Any Turing/topos realization remains a separate bridge
obligation.

## Next implementation bridge

1. Specify a minimal `InstitutionFrame` interface for an Aristotle frame:
   signatures, sentences, models, satisfaction, translations, and registered
   equality/questions.
2. Translate the frozen Phase B interface into an explicit signature diagram;
   retain the 34 admitted roles and the two exclusions as data.
3. State and test the satisfaction and naturality conditions without candidate
   equality as an input.
4. Test the relevant amalgamation/exactness condition on that diagram. Record a
   constructed model or an explicit failed condition/witness.
5. Only after this mapping is explicit, compare any failure witness with
   institution-theoretic interpolation/inclusion-system results. Do not label
   it cohomological merely because it is an obstruction.
6. Build a Hets adapter only when the interface above is stable: its purpose is
   interactive heterogeneous proof management and provenance-preserving
   checking, not canonical normalization of local frames.

The prior opening is documented in
[Pre-institutional translation: formal openings](PREINSTITUTIONAL_TRANSLATION_OPENINGS.md):
it asks for the relational translation structure from which these local
institutional representations would be obtained.

## Sources for the comparison

- R. Diaconescu, *Grothendieck Institutions* (2002): indexed/fibred
  institutions, globalization, colimits, exactness/model amalgamation, and
  inclusion systems: <https://www.imar.ro/~diacon/PDF/gi.pdf>.
- Hets documentation: heterogeneous CASL, logic translations, development
  graphs, static analysis, and proof management:
  <https://www.informatik.uni-bremen.de/agbkb/forschung/formal_methods/CoFI/hets/src-distribution/versions/Hets/docs/index.html>.
- R. Diaconescu, *Borrowing interpolation* (2012), for the relation between
  institution-theoretic translation and interpolation:
  <https://doi.org/10.1093/logcom/exr007>.
- Current experimental claim boundary:
  [Aristotle native-translation evidence](ARISTOTLE_NATIVE_TRANSLATION_EVIDENCE.md).
