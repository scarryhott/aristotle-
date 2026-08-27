# NRRF789 — Continuation and halting of a computer: encoding is the universe of halting, evaluation is the canon of continuation

Module: `NRRF789ComputerContinuationHaltingEncodingUniverseEvaluationCanon.lean`
(registered in `lakefile.toml`, builds with no `sorry`, machine-checked axiom audit at the end).

The reading formalised:

> Of a computer, encode the substrate and evaluate the operation in an equally natural manner,
> where encoding is the universe of halting and evaluation is the canon of continuation.

## The computer

Nothing is added to the apparatus already present in the project. A **computer** is the partial step
of NRRF775: an operation `step : σ → Option σ` on a substrate `σ`, where `none` is the computer's
report that it has stopped. `run step x n` is the state after `n` stages, `Halts` is "some stage is
empty", `Continues` is "every stage carries a state".

Two readings are taken of the same datum, and the whole point is that neither is prior to the
other: each is the *unique* thing satisfying its own law, and both are carried along by any
simulation of the computer.

## §1 Encoding is the universe of halting

The **encoding** of the substrate, `enc step x`, is the stage at which the run of `x` stops — and
nothing at all when it never stops.

- `enc_eq_some_iff` — `enc step x = some n` exactly when stage `n` is empty and no earlier stage is:
  the encoding is a *minimal* stopping stage, not a chosen code.
- `enc_universe` — `{x | (enc step x).isSome} = {x | Halts step x}`. The domain of the encoding is
  the halting set on the nose: encoding *is* the universe of halting.
- `enc_unique`, `enc_exists_unique` — the encoding is the unique reading satisfying its
  specification `EncSpec` (report a minimal stopping stage; report nothing exactly on continuing
  data). Nothing is chosen; the halting universe forces it.

## §2 Evaluation is the canon of continuation

**Evaluation** `eval step x` is the run itself, read stage by stage.

- `eval_unique`, `eval_exists_unique` — `eval` is the unique function obeying the two evaluation
  laws (`E x 0 = some x`, `E x (n+1) = (E x n).bind step`). That uniqueness is the sense in which
  evaluation is a canon and not a convention.
- `traj`, `step_traj` — on a continuing datum the evaluation is a *total* trajectory `ℕ → σ` with
  `step (traj n) = some (traj (n+1))`.
- `continues_of_trajectory`, `traj_unique`, `trajectory_exists_unique` — conversely a trajectory
  through a datum forces continuation, and a continuing datum has exactly one trajectory. So
  continuation has a canon, and the evaluation is it.

## §3 The two readings partition the substrate

`continues_iff_enc_eq_none` and `substrate_partition`: `{x | Continues step x}` is exactly the
complement of the encoded universe `{x | (enc step x).isSome}`. Every datum is read by exactly one
of the two readings.

## §4 Equally natural

A **simulation** is a map `f : σ → τ` with `step' (f x) = (step x).map f`.

- `run_map`, `eval_map` — evaluation is *equivariant*: `eval step' (f x) n = (eval step x n).map f`.
- `enc_sim` — the encoding is *invariant*: `enc step' (f x) = enc step x`; the halting universe does
  not move at all.

Naturality is one and the same statement for the two readings — the encoding natural in the
invariant way, the evaluation natural in the equivariant way. That is the sense of "an equally
natural manner".

## §5 Mutual determination, and no collapse

- `enc_eq_of_none_pattern`, `eval_determines_enc` — the encoding depends only on the pattern of
  stopping stages, so the evaluation determines the encoding.
- `enc_does_not_determine_eval` — the converse fails: two data of the fibred countdown machine,
  `(1, true)` and `(1, false)`, share their encoding while their evaluations differ. Equally
  natural, but not equal.

## §6 Concrete computers

- `countdown` (step down by one, stop at the bottom): `run_countdown` computes every stage, and
  `enc_countdown` gives `enc countdown x = some (x + 1)` — the whole substrate lies inside the
  halting universe.
- `climb` (never stop): `enc_climb x = none` and `traj_climb x n = x + n` — the whole substrate lies
  inside the continuation canon.
- `countdownPair` (the countdown machine fibred over a tag): `countdownPair_sim` exhibits the
  fibring as a simulation, and `enc_countdownPair` reads its encoding off §4 with no new
  computation.

`nrrf789_answer` collects the clauses for an arbitrary computer on an arbitrary substrate.
