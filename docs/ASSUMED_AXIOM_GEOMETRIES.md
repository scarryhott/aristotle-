# Assumed Axiom Geometries and Explicit Translational Closure

## Semantic boundary

A novel axiom geometry must be evaluated under the equality it admits. In this project,
**assumed** means supplied as local semantic data before comparison—not declared globally true and
not exempted from verification. The evaluator may find a setoid, grounding, operation, or
translation counterexample. It may not replace the local equality with a preferred external normal
form after seeing another frame.

The executable order is:

```text
local axiom-geometry assumption F          local axiom-geometry assumption G
                 |                                         |
                 +---- internal closure audits and freeze --+
                                      |
                              raw candidate T
                                      |
                    preservation and reflection of equality
                                      |
                              GeomEquiv admission
                                      |
                       explicit translational form (T,phi,pi)
                                      |
                  W / E / J / C / operation naturality
                                      |
                    quotient factor or separating witness
                                      |
                             next-basis transfer
```

This resolves two different questions. Internal evaluation asks whether a geometry coheres in its
own unified manner. Cross-frame evaluation asks whether an explicit candidate preserves and
reflects the two already-frozen equalities. Neither question defines the other's answer.

## Runtime representation

Each frame protocol now contains a content-addressed `axiom_geometry_assumption`. The bounded D4
fixture declares equality by identical complete local right-action signatures for two distinct
program presentations, `x` and `x·e`. The frame stage instantiates that declared rule and
exhaustively checks:

- reflexivity, symmetry, and transitivity;
- returning: every occurrence equals a presentation of its local returned class;
- grounding: distinct returned local elements are not identified;
- operation congruence under frame equality; and
- closure under presentation reversal.

The frame artifact records both an `axiom_geometry_assumption_id` and the audit. An unknown
relation kind is rejected with an explicit unsupported-geometry error; it is never silently
normalized to the implemented D4 relation. Supporting a new geometry therefore requires a new,
precommitted local evaluator, not a post-hoc equality choice.

## Closure lineage

Every candidate certificate contains an `explicit_translational_form` with:

- source and target assumption and frame identifiers;
- the raw basis map and occurrence map `T`;
- the preservation-and-reflection `GeomEquiv` decision;
- the explicit tuple `(T,phi,pi)` when the equality translation is admitted; and
- separate `W`, `E`, `J`, `C`, operation, quotient-question, and next-basis closure statuses.

This distinction is observable in the controls. `equality_collapse` fails equality reflection, so
no tuple is admitted. `operation_twist` admits a `GeomEquiv` and constructs `(T,phi,pi)`, but the
full closure chain is rejected by a multiplication-naturality counterexample. Partial and absent
proposals carry explicit `PENDING_COMPARISON` and `UNSELECTED_COMPARISON` lineage and are never
reported as `OpenIn`.

Every question record likewise contains an `explicit_relational_closure_form`. A resolved question
records its unique quotient factor. An open question records an actual pair `x~y` with
`Q(x) != Q(y)`. Cross-frame transport is attached only to admitted translational-form identifiers,
and the held-out next basis cites the exact selected form.

## Formal boundary

`NRRF631RuntimeFrameConditionalBridge.lean` exposes `assumeAxiomGeometry`: an explicit constructor
from a supplied `Setoid` to a `ReferenceFrame`. This adds no Lean axiom. The theorem
`resolvedIn_assumed_geometry_iff` confirms that a question is evaluated using exactly that supplied
relation; `GeomEquiv` continues to require preservation and reflection before transport.

The separately reported NRRF633 development gives the stronger conditional theorem: once a
`TransFrame` exists and a relational definition is returning and grounded, closure equality is
unique and all closure forms factor through returned identities. The current checkout does not
contain the general NRRF631 dependency needed to audit that uploaded module, so the executable
study does not pretend to re-prove it. Instead, it makes its empirical boundary explicit: local
geometries are assumed and audited first; existence of a cross-frame translational closure remains
something the experiment can confirm or refute.

## Scope

Here “all closure forms follow” means every declared runtime form—return, extension, reversal,
curvature, quotient resolution/openness, and next-basis transfer—carries explicit lineage from the
admitted local geometries through a verified translational form. It does not claim that the finite
D4 evaluator implements or classifies every possible equality geometry in mathematics.
