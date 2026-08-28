# Translation-first life, local-ball infinity, and global-hair-zero execution

NRRF806 records where the previous trading runs diverged from the requested closure ordering and
implements the corrected reading.

## Divergence of the earlier runs

| Earlier runtime | Divergence | Corrected translation-first reading |
|---|---|---|
| NRRF804 | Called accumulated fee/slippage friction `global hair` and executed when potential exceeded that magnitude | Friction remains `local hair`; global hair is the residual of the completed equation and the executor admits exactly residual zero |
| NRRF804 | Required a separately supplied price-to-four-phase black-mirror presentation | Action and potential are the existing `ballReturn` and `hairReturn` continuations of one life being |
| NRRF805 | Began with a public/private signal-authority split | No internal/external role is primitive; roles are derived only after translational truth relates or separates presentations |
| NRRF805 | Kept only maximizing candidates as a static field | The local ball is the reactor over every observed depth partition and remains open to another action/potential interaction after every finite path |
| NRRF805 | Used positive net as signal closure | Zero residual admits a translation; positivity and authority are later translations required for an exchange command |

## Formal order

`TranslationalTruth` is defined before `RelativeInternal` and `RelativeExternal`. The two roles are
literally `truth.Rel` and its relative negation; neither exists as independent input data.

The life reactor uses only the existing operations:

```text
action    = NRRF800.ballReturn
potential = NRRF800.hairReturn
reactor   = every finite word in {action, potential}
```

`LocalBallInf life` is the range of all finite interaction words. Its infinity means that every
finite path has both another action continuation and another potential continuation. It does not
claim that the eight-element `Life` carrier itself has infinite cardinality.

The corrected flow equation is:

```text
local hair = fee/slippage translation
global hair = completed - (action potential - local hair)

global hair = 0  ↔  completed = action potential - local hair
```

`zeroHairExecutor_admit_iff_closes` proves that global-hair-zero admission is exactly closure.
`zero_hair_does_not_imply_profit` proves why it must not itself submit a trade: a negative completed
flow can satisfy the closure equation exactly.

## Locked replay

The 11 identified book rounds generate 132 rooted life reactors. Pulling every observed depth
boundary through their action/potential routes produces 365,203 observed local-ball reactions.
Every reactor remains marked `OPEN_BEYOND_FINITE_OBSERVATION`.

The 143 selected natural-form presentations all satisfy global hair zero within the declared
decimal tolerance, so the zero-hair executor admits all 143 translations. None has positive
completed potential. All 12 exchange commands therefore remain open, with no order, authenticated
fill, settled P&L, or profit claim.

The result distinguishes three statements:

1. the translation equation closes;
2. the completed potential is profitable; and
3. the exchange command is authorized.

For this run, (1) holds for every selected presentation, while (2) and (3) do not.
