# NRRF833 True-Unification Reintegration

The fee/pricing simulator is reintegrated as one persistent closure state rather than a pipeline of independent models.

## One state

The operational state is

\[
X_t=(\text{instrument rules},\text{fee schedule},\text{rolling volume},\text{global learner},\mathcal K_t,\text{receipt chain},\text{transition chain}).
\]

Book evidence and the current episode enter the transition; pricing, fee selection, route selection, execution, accounting, learning, and memory are projections of the same operator

\[
\Phi:X_t\mapsto X_{t+1}.
\]

The implementation is `experiments/nrrf833_unified_closure_reintegration.py`.

## Natural execution forms are derived, not named

The memory partition does not use synthetic labels such as `CALM`, `THIN`, `ADVERSE`, or `RECOVERY`.  A `NaturalExecutionForm` is derived before trading from observable execution relations only:

- venue and symbol;
- effective Alpaca fee tier;
- spread geometry;
- top-of-book depth relative to the declared quote budget;
- top-of-book imbalance.

Thus changing only a human regime label cannot change the selected form.  A change in observable market geometry can.

## Persistent closure memory

Each form owns a `FormMemory` containing its own learned execution state and the hashes of evidence admitted into that form.  The global learner is only a transfer prior for a form that has never been observed before.  Once a form exists, revisiting other forms does not overwrite it.

The knowledge lattice is ordered by evidence inclusion:

\[
\mathcal K_t\preceq\mathcal K_{t+1}
\]

iff every previously known form remains present, every previously admitted evidence hash remains present, and closed-return/no-fill counts never decrease.

Every transition checks this order.  A contraction raises an assertion instead of producing another state.

This is the monotone fidelity statement that can actually be guaranteed in a changing market:

\[
\boxed{\mathcal K_t\subseteq\mathcal K_{t+1}}.
\]

It deliberately does **not** manufacture the false statement

\[
|\epsilon_{t+1}|\le |\epsilon_t|
\]

for every successive trade.  Point prediction error remains empirical and may increase when the market changes.  What cannot decrease is the closed set of environmental relations already learned.

## Unified transition

For each episode the single operator performs:

\[
\begin{aligned}
X_t
&\to \text{effective rolling-volume fee tier}\\
&\to [E_t]_{\equiv}\quad\text{(natural execution form)}\\
&\to \text{form-specific learned state or global prior}\\
&\to \text{full-cost route selection}\\
&\to \text{depth/queue execution}\\
&\to \text{cash + inventory + cost receipt}\\
&\to \text{accounting closure}\\
&\to \text{local-form learning + global transfer learning}\\
&\to \mathcal K_{t+1}=\operatorname{Cl}(\mathcal K_t\cup\{E_t,A_t,R_{t+1}\})\\
&\to X_{t+1}.
\end{aligned}
\]

The receipt and transition are independently hash chained.  The next state contains the returned receipt hash and transition hash, so the state is not advanced outside the return relation.

## Zero / infinity translation

The operational reading is now:

\[
\infty_t=\text{environmental relation not yet contained in }\mathcal K_t,
\]

\[
0_t=\text{environmental relation already closed into }\mathcal K_t.
\]

A trade/observation translates

\[
\infty\to\text{partition}\to\text{execution}\to\text{return}\to0.
\]

When the environment later changes, a new unresolved relation opens without erasing a previously closed one:

\[
0_t\to\infty_{t+1},\qquad \mathcal K_t\subseteq\mathcal K_{t+1}.
\]

That is the reintegrated continual-closure interpretation.

## Executed CI properties

`tests/test_nrrf833_unified_closure_reintegration.py` is written as `unittest.TestCase`, matching the repository workflow's actual `python3 -m unittest discover -s tests -v` runner.  It executes the following properties:

1. every admitted accounting return has zero closure residual;
2. the knowledge lattice is extensive at every transition;
3. human regime labels do not define the natural execution partition;
4. a learned form survives an intervening different form unchanged;
5. revisiting that form refines rather than replaces its evidence;
6. the same state and evidence give the same transition;
7. evidence accumulates without falsely forcing point-error monotonicity;
8. per-form closed-return and no-fill counts are monotone;
9. the unified state contains the fee, pricing, learning, receipt, and volume projections.

The remaining empirical boundary is unchanged: to turn this from a high-fidelity Alpaca counterfactual closure into an Alpaca empirical closure, the same operator must ingest authenticated paper/live acknowledgements, fills, cancellations, posted fee activities, and reconciled cash/inventory deltas as its return evidence.
