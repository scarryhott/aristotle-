# Runtime Reunification with Translational Existence and Naturality

The full-stack runtime is a finite operational realization of the translational consequences
described by NRRF630. It does not define closure from one canonical D4 coordinate system.

## Unified frame form

After the two learners have frozen their local bases, each coherent comparison supplies

```text
phi : B_B ≃ B_A
pi  : Pole ≃ Pole
T   : Pole × B_B ≃ Pole × B_A
T(p,b) = (pi(p),phi(b)).
```

The remaining operations are

```text
W_l(p,b)=b
E_l(p,b)=(p,b)
J_l(p,b)=(other(p),b)
C_l(p,b)=the pole section transported through pi.
```

Relative equality is therefore

```text
(p,b) ≡_C (q,c)  iff  W_l(p,b)=W_l(q,c)  iff  b=c.
```

No branch assigns truth values to this relation.

## NRRF630-to-runtime map

| Translational result | Executable realization |
|---|---|
| `retNat` | 16 exhaustive instances of `W_A(Ty)=phi(W_B y)` per frame form |
| natural occurrence/identity functors | 64 exhaustive operation cases carried through `T` and `phi` |
| `revNat` | 16 exhaustive instances of `T(Jy)=J(Ty)` |
| `curvNat` | 16 exhaustive instances of `T(Cy)=C(Ty)` |
| `quotBasisEquiv` | 16 polar occurrences quotient to eight returned basis classes |
| `quotBasisEquiv_natural` | 256 exhaustive preservation-and-reflection cases for relative equality |
| `polarSection` and naturality | the source section is transported by `pi` to the target section |
| reversal exchanges sections | preserved and reversed `pi` forms both pass the section/reversal checks |
| universal factorization | all 256 Bool-valued closure-respecting basis evaluations factor uniquely through `W` per language |
| no origin representably | all eight coherent D4 frame forms are retained; none is declared the absolute comparison |

The Bool factorization check is the complete finite instance for `Ω = Bool`. The general
codomain-independent universal property remains the Lean theorem, not a claim inferred from the
finite enumeration.

## Openness relative to the frame

The structural-family branch contains eight valid equality forms. Its reference question is open
because no contact selects one form for that episode, not because the fixed axioms contain an
unresolved ambiguity. The relative-reversal branch demonstrates this directly: its nontrivial
`pi` preserves all closure operations.

The negative branch is instead a sign-erasing map. It collapses distinct basis forms, fails
bijectivity and multiplication naturality, and therefore cannot extend to a `TransFrame` comparison.
This is an operation-level obstruction rather than a static false label.

## Admission relation

A basis receipt exists only when the actual episode contains an independently witnessed frame form
whose operations commute. A self-claim is not such a witness. Counterfactual valid frame forms are
retained as controls but do not issue additional episode receipts.
