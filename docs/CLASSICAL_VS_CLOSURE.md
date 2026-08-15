# Classical Mathematical ASI vs Closure Runtime

“Classical ASI” and “closure ASI” name verification architectures here. The current executables are
bounded symbolic proxies, not actual superintelligences. A fair comparison holds the mathematical
artifacts, candidate maps, process budget, and local checking power fixed; it changes what
relational evidence the verifier is required to produce.

| Layer | Classical mathematical ASI | Translational / closure ASI |
|---|---|---|
| Trusted object | proof checked in a fixed kernel | recoverable invariant across admissible translations, ultimately still kernel-checked when formalized |
| Language | fixed or translated back into a privileged formal language | family of pairwise comparable languages; no language is the metaphysical origin |
| Capability growth | harder theorem proving, search, synthesis, formalization | may additionally change representation, axiomatization, geometry, internal ontology, and reasoning route |
| Equality | syntactic/definitional/propositional equality in the formal system | closure equality can identify distinct occurrences with the same verification return |
| Verification | theorem checks | theorem checks **plus** cross-language return/coherence claim |
| History | proof object/derivation matters operationally | coherent evolutionary route is predicted to leave no verdict trace beyond endpoints |
| Internal change | usually implementation detail | return-invisible change is modeled as gauge freedom |
| Failure | rejected proof / counterexample | failure to preserve/reflect frame equality, broken naturality, or a concrete counterexample; absence of contact is merely non-selection |

## Not a replacement for Lean

Closure verification is not proposed as a substitute for a trusted proof kernel. Lean checks the formal claims about the closure architecture. The new question is what architecture should be checked when the mathematical intelligence can change the presentation in which its reasoning occurs.

## Classical runtime

A classical runtime can be idealized as:

`prompt → search/reason → formal statement → proof term → kernel verdict`.

Its central invariant is kernel acceptance in a selected formal environment.

## Closure runtime

A closure runtime adds explicit relational state:

`frame equality → GeomEquiv(T,phi,pi) → occurrence in L_j → return naturality → frame-qualified question evaluation`.

The runtime records the translation, return, basis, and obstruction rather than only a final boolean. Its purpose is to test whether mathematical content survives representation change for reasons not hard-coded into the transformation generator.

## Required experimental distinction

A useful closure runtime must contain both **admitted moves**, predicted to preserve the return, and **non-admitted/adversarial moves**, capable of breaking it.

Without the second class, the runtime only demonstrates its own definitions.

## Implemented bridge experiment

`experiments/full_stack_math_asi.py` composes both layers without conflating them. Each local
classical agent learns and executes in its own fixed presentation. Only after both states are frozen
does a separate constructor propose cross-frame comparisons; an independent verifier then checks the
precommitted translational operations.

The mathematical relation after freeze is therefore:

`frame equality → post-hoc GeomEquiv(T,phi,pi) → W,E,J,C naturality → ResolvedIn/OpenIn`.

All eight D4 isomorphisms extend to coherent axiom-geometry equivalences. Structure alone does not
select one comparison, but that non-selection is not `OpenIn` and is not an internal defect. A
relative reversal is also coherent when `phi` and `pi` travel with it. The negative control is
instead a sign-erasing map that fails bijectivity and learned-operation naturality.

## Executed paired architecture comparison

`experiments/classical_vs_closure_asi.py` now runs both verifier contracts over byte-identical
frozen inputs. It strengthens the upstream boundary beyond the first bridge experiment: each
language independently derives and freezes a primitive operational equality table before any
candidate map exists. Equality is identical local right-action behavior of the distinct programs
`x` and `x·e`; no `W` or cross-frame map defines it. The quotient return is derived downstream.

The paired order is:

```text
questions precommitted
  → independent presentations frozen
  → local equality geometries frozen
  → raw candidate T frozen
  → fixed-frame arm || closure arm
  → paired differential
```

The fixed-frame arm checks local group kernels, all supplied maps, multiplication, bijectivity,
inverses, and element-order transport. It accepts all eight ordinary isomorphisms, including
relative reversal. The closure arm begins from the frozen equality matrices and additionally emits
preservation/reflection certificates, derived quotient return, `W/E/J/C` naturality,
frame-qualified question factors or separating witnesses, and next-basis transfer.

The distinction is not “isomorphism versus no isomorphism.” Both arms recognize isomorphism. The
comparative hypothesis is that the explicit origin-free frame/`GeomEquiv` pipeline yields auditable
transport, obstruction, and frame-relative resolution/openness evidence not contained in local
kernel acceptance alone.

Paired measurements include:

- local kernel success and ordinary isomorphism coverage;
- equality-preservation and equality-reflection coverage;
- downstream naturality failure after `GeomEquiv` success;
- adversarial false-admission rate;
- quotient factor and explicit openness-witness counts;
- held-out next-basis transfer;
- process time and evidence size in future frontier runs.

The number of open relations is not an optimization target. `OpenIn` is meaningful only for a
named total question in a named frame with a separating witness.

The bounded run found an informational extension but not capability superiority. The added-utility
hypothesis is falsified at scale if a strong fixed-frame/equivalence baseline produces the same
auditable relations with equal or lower cost, or if closure comparison must secretly select a
canonical frame. See [`CLASSICAL_VS_CLOSURE_RUN.md`](CLASSICAL_VS_CLOSURE_RUN.md).
