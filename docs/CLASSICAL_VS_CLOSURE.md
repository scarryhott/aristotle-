# Classical Mathematical ASI vs Closure Runtime

| Layer | Classical mathematical ASI | Translational / closure ASI |
|---|---|---|
| Trusted object | proof checked in a fixed kernel | recoverable invariant across admissible translations, ultimately still kernel-checked when formalized |
| Language | fixed or translated back into a privileged formal language | family of pairwise comparable languages; no language is the metaphysical origin |
| Capability growth | harder theorem proving, search, synthesis, formalization | may additionally change representation, axiomatization, geometry, internal ontology, and reasoning route |
| Equality | syntactic/definitional/propositional equality in the formal system | closure equality can identify distinct occurrences with the same verification return |
| Verification | theorem checks | theorem checks **plus** cross-language return/coherence claim |
| History | proof object/derivation matters operationally | coherent evolutionary route is predicted to leave no verdict trace beyond endpoints |
| Internal change | usually implementation detail | return-invisible change is modeled as gauge freedom |
| Failure | rejected proof / counterexample | rejected proof, broken translation/return, counterexample, or OPEN obstruction |

## Not a replacement for Lean

Closure verification is not proposed as a substitute for a trusted proof kernel. Lean checks the formal claims about the closure architecture. The new question is what architecture should be checked when the mathematical intelligence can change the presentation in which its reasoning occurs.

## Classical runtime

A classical runtime can be idealized as:

`prompt → search/reason → formal statement → proof term → kernel verdict`.

Its central invariant is kernel acceptance in a selected formal environment.

## Closure runtime

A closure runtime adds explicit relational state:

`occurrence in L_i → translation/restructuring/evolution → occurrence in L_j → verification return → comparison/return → verdict`.

The runtime records the translation, return, basis, and obstruction rather than only a final boolean. Its purpose is to test whether mathematical content survives representation change for reasons not hard-coded into the transformation generator.

## Required experimental distinction

A useful closure runtime must contain both **admitted moves**, predicted to preserve the return, and **non-admitted/adversarial moves**, capable of breaking it.

Without the second class, the runtime only demonstrates its own definitions.

## Implemented bridge experiment

`experiments/full_stack_math_asi.py` composes both layers without conflating them. Each local
classical agent learns and executes in its own fixed presentation. Only after both states are frozen
does a separate translator propose a cross-frame relation; an external gate then checks the
precommitted return.

The closure relation is therefore:

`local learning/checking in A and B → frozen occurrence relation → post-hoc T → external W → δ_C`.

The observed `OPEN` structure-only branch is important: local proof of two isomorphic D4 groups does
not by itself choose which of eight relative orientations is the intended return. The `FALSE`
reversed-contact branch likewise shows that abstract isomorphism is weaker than translational
verification against a selected external relation.
