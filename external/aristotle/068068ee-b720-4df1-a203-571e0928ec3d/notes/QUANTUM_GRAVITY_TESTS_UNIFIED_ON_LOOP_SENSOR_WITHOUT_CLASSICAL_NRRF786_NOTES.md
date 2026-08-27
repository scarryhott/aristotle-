# NRRF786 — Quantum gravity and its tests unified on the loop sensor, with no classical physics

**Module:** `NRRF786QuantumGravityTestsUnifiedOnLoopSensorWithoutClassical.lean`
(registered in `lakefile.toml`; builds cleanly, no `sorry`, no warnings; every headline result has
a machine-checked axiom audit in §7).

**Instruction formalized.**

> Unify our quantum gravity theory and tests without relying on classical physics; use our
> translational truth loop sensor completely.

## The reading

*Completely on the loop sensor* is taken literally: the only apparatus admitted into the module is
NRRF739's `LoopSensor` — a reading of a translation line into a loop of period `k` that advances by
exactly one step per translation. No background manifold, no absolute position, no classical
assignment of values, and no classical limit that the quantum theory must reproduce.

* A **state** is a pair of translations, `State = ℤ × ℤ`: the *ball* (gravitational, never
  returning) translation and the *hair* (quantum phase, returning) translation. A state is never
  observed — only readings of it are.
* A **test** at resolution `n` is a loop-sensor comparison: ball components through the loop of
  period `n`, hair components through the loop of period `k` (`Test`, `test_is_loop_sensor`,
  `test_iff`). This family is the entire experimental content of the theory.
* The **theory** is the same data in the framework shape of NRRF785: frames are sensors (an origin,
  which the sensor cannot report, and a resolution), observables are states, and a verdict is the
  frame's loop reading of the separation, undefined outside its window (`qgFramework`).

## What is proved

### Relational by construction (§2)

* `test_translation_invariant` — translating both states alike leaves every verdict unchanged.
  Background independence is a theorem about the sensor, not a postulate.
* `test_relational` — every verdict is a verdict about a separation.
* `test_equivalence` — at each resolution the verdicts form an equivalence of states.

### Theory and tests are one object (§3)

* `agree_iff_gaugeClass` — two states pass **every** loop-sensor test exactly when they share a
  class in `ℤ × ZMod k`: ball translation exactly, hair translation only modulo its period. So the
  state space modulo what no test can see is precisely NRRF745's ball–hair fibre
  (`gaugeClass_surjective`).
* `agree_iff_hair_translate` — the indistinguishable states are exactly the hair translates:
  `hair_gauge_undetectable` (a full quantum period is invisible at every resolution) against
  `ball_shift_detectable` (every nonzero gravitational translation fails some finite loop). The
  QM/GR asymmetry is *derived* from one sensor family rather than imposed by two theories.
* `no_single_test_complete` — no single loop, at any period, is the theory: each relative reading
  is partial, and the truth is their absolute translation (NRRF747's principle, here for quantum
  gravity).

### The framework, and the impossibility of a classical reading (§4–§5)

* `qgFramework`, `qg_equivariant` — the loop-sensor data is an NRRF785 framework: shifting sensor
  and state together moves no verdict.
* `qgVal_eq_iff_test` — the framework's verdicts *are* the loop-sensor tests: inside a window, two
  states get the same verdict exactly when they pass the ball test of period `2n+1` (exact in the
  window, `ballRead_eq_iff_of_window`) and the hair test of period `k`.
* `qg_not_total`, `qg_contextual`, `qg_not_classical`, `qg_no_invariant_assignment` — the theory
  answers only inside a window and admits **no** global assignment of absolute values to states.
  It is not merely written without classical physics: it cannot be given a classical reading.
* `qg_unified_truth`, `qg_truth_unique`, `qg_truth_relational` — and yet exactly one translational
  truth function exists on level-unified questions, and `qg_translates_iff` identifies those
  questions with (resolution, separation) pairs. The truth of the theory is exactly relational
  data.
* `qg_fragment_noncontextual` — each single sensor is classical inside itself: the
  non-classicality is never local, only translational.

### One statement (§6)

`nrrf786_unification` bundles the three: theory = tests (up to the hair translate), no single loop
and no classical reading, and a unique translational truth.

## Axiom audit

Only Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`) occur, pinned by
`#guard_msgs` in §7. `Classical.choice` there is Lean's axiom of choice, inherited from the library
used for modular arithmetic; it is unrelated to classical physics, which §5 shows the theory cannot
admit.
