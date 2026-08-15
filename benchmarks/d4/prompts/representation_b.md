# Blind prompt B — semidirect normal-form presentation

You are formalizing one presentation of the symmetry group of a square in Lean 4 with Mathlib.

Create one self-contained module named `D4NormalForm.lean` in which:

1. the carrier consists of normal forms `(k, flip)` with `k : Fin 4` and `flip : Bool`;
2. multiplication is defined directly by
   `(k,f) * (l,g) = (k + (-1)^f l mod 4, f xor g)`;
3. identity, inverse, associativity, and the eight-element cardinality are proved from this
   definition;
4. `W_B` returns the complete induced action
   `x ↦ k + (-1)^flip x (mod 4)` in the fixed vertex order `0,1,2,3`;
5. the module provides an explicit enumeration of all eight normal forms and proves completeness
   and no duplication.

Do not define the carrier as permutations and do not import a pre-existing dihedral-group
implementation as the definition. Do not introduce `sorry`, `admit`, custom axioms, or an oracle.
You are not given, and must not request, another representation or a cross-representation
translator.

Return the exact Lean source plus a machine-readable build report listing the toolchain and all
axioms reported for the principal theorems.

