# NRRF785 — Quantum and classical frameworks unified on translational truth

Machine-checked module: `NRRF785QuantumClassicalFrameworksUnifiedOnTranslationalTruth.lean`
(registered in `lakefile.toml`, builds with no `sorry`, and with **no `import` line at all** — only
Lean's kernel is in scope). Every claim below is a theorem in that file; §8 of the file pins the
axiom list of each headline result with `#guard_msgs`, so the build fails if it ever changes.
Only `Quot.sound` occurs; `Classical.choice` occurs nowhere.

## The single notion

A **framework** `Framework S C O V` is:

* observables `O` — the questions;
* frames `C` — the levels at which questions are presented (a measurement context);
* values `V`, and a verdict map `val : C → O → Option V`, where `none` records that the frame does
  not answer that question (complementarity);
* an abelian group `S` of **level shifts**, acting on frames and on observables, subject to the
  single link

      val (s · c) (s · o) = val c o.

That last equation is **translational truth**: the verdict belongs to the *relation* between a
frame and an observable, not to either one absolutely; shifting both leaves it alone.

Classical physics and quantum physics are not two notions here. They are two conditions on one
notion:

* `IsClassical F` — one global assignment `g : O → V` reproduces every verdict;
* `Noncontextual F` — some global assignment merely agrees with every verdict actually given;
* `Contextual F` — no such assignment exists.

## What is proved

1. **Every framework carries exactly one truth function on level-unified questions.**
   Presentations `(c, o)` are identified when a shift carries one to the other (`Translates`, an
   equivalence: `translates_refl/symm/trans`); the quotient `Orbit F` is the type of level-unified
   questions, and `truth F : Orbit F → Option V` reproduces every verdict (`truth_orb`) and is the
   *unique* such function (`truth_unique`). `unified_truth` states existence and uniqueness
   together. This holds for classical and contextual frameworks alike — it is the object they
   share.

2. **Every framework is classical inside each frame** (`fragment_noncontextual`): the verdicts of
   any single frame are reproduced by one assignment. Contextuality is never local; it is a
   statement about how frames translate into one another.

3. **Classical = total + noncontextual** (`total_noncontextual_iff_classical`), and equally
   **total + frame-independent** (`classical_iff_total_frameFree`, given one frame and one value to
   name). A classical framework is total, frame-free and noncontextual
   (`classical_total`, `classical_frameFree`, `classical_noncontextual`).

4. **The absolute assignment, where it exists, is forced to be translational.** Any global
   assignment consistent with the framework is already shift-invariant wherever the framework
   speaks (`section_invariant_on_defined`); for a classical framework it is invariant outright
   (`classical_section_invariant`). Hence
   `classical_iff_invariant_assignment` / `classical_iff_truth_from_invariant`: **to be classical
   is exactly to be a translational truth that descends to a single level-invariant naming of
   values.** The classical case is a special case of translational truth, not a rival to it.
   `ofInvariant` / `ofInvariant_isClassical` build the classical framework of any invariant
   assignment, so the converse direction is realised too.

5. **A contextual framework whose translational truth is complete** (§6 of the file). Three
   observables `a, b, c`; three frames `ab, bc, ca`, each answering two of them with opposite
   values; the cyclic group of three level shifts rotating observables and frames together.
   * `parity_contextual`, `parity_not_classical`: no global assignment fits — frame `ab` says `a`
     is `true`, frame `ca` says `a` is `false`.
   * `parity_not_total`: each frame leaves one question unanswered.
   * `parity_pairwise_defined`: yet every pair of distinct observables is answered together in
     some frame — the obstruction is global, not pairwise.
   * `parity_fragment_classical`: inside each frame it is classical (instance of 2).
   * `parity_invariant_constant`: a level-invariant assignment there must be constant — the
     symmetry reason why no absolute assignment can exist.
   * `parity_three_orbits`, `parity_orbit_truths`, `parity_truth_decides`: the nine presentations
     fall into exactly **three** translation orbits, carrying the verdicts `some true`,
     `some false`, `none`, and the orbit verdict decides every presentation.

   So the quantum-like case is not truth-less: its truth is complete, exact and unique — it is
   translational rather than absolute.

`nrrf785_unification` collects (1)–(5) in a single statement.

## The reading

Insisting that truth be an absolute value attached to an observable is what makes the quantum case
look paradoxical: the parity framework has no such truth at all. Reading truth as translational —
attached to the orbit of a presentation under change of level — both cases are described by the
same object, and the classical case is recovered exactly when that orbit truth happens to descend
to an invariant assignment, i.e. exactly when a level can be fixed absolutely.
