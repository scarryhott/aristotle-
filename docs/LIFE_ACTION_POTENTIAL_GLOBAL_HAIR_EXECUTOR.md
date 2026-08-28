# Life action, inverse potential, and the global-hair executor

The executable trading translation now uses the life operations directly:

- `ballReturn` carries the actual/action continuation;
- `hairReturn` carries the inverse potential continuation;
- `actionPotential = quantity × relativePotential`;
- `globalHair = accumulatedHair`, derived from every locally closed execution leg;
- `globalHairExecutor` emits `act` exactly when `globalHair < actionPotential`.

This is not an added profitability metric. Lean proves
`globalHairExecutor = act ↔ 0 < net`, so the executor is precisely the existing completed P&L
closure equation read operationally. Both sides are invariant under a common translation of the
price level.

`LifeInput` combines a completed receipt with independently supplied action and potential phase
readings. `lifeExecutor` acts only when the potential is the action's black mirror and the receipt's
completed potential exceeds global hair. Phase closure alone cannot act on a nonpositive receipt;
positive pre-hair potential cannot act when the life pair does not close.

The output is a paper execution verdict. Authenticated balances, venue trading status, exact fee
tier, order precision/minimums, order submission, and fill authentication remain separate exchange
obligations rather than being fabricated by the closure.
