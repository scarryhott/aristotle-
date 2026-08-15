# Post-hoc prompt C — frozen translation

You receive two immutable Lean modules, `D4Permutation.lean` and `D4NormalForm.lean`, produced in
independent runs, plus the previously frozen `precommit_return.json`.

Create a third module named `D4Translation.lean`. You may import but must not edit either input.
The module must:

1. define a total equivalence `T` from every normal form to a permutation presentation;
2. define and prove its inverse;
3. prove identity and compositional coherence for the induced translations;
4. prove that `T` preserves multiplication;
5. prove the return square `W_A (T u) = W_B u` without changing either return;
6. enumerate the exact images of all eight normal forms in a machine-readable table;
7. print the axioms of the translation, homomorphism, inverse, and return-square theorems.

No `sorry`, `admit`, custom axioms, source modification, narrowed domain, or redefinition of `W` is
permitted. If the full translation cannot be proved, return the smallest explicit obstruction and
leave the result OPEN. If an equality fails, return a concrete counterexample rather than changing
the protocol.
