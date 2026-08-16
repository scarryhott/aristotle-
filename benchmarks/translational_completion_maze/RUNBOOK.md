# Translational completion maze topology runbook

Status: **EXECUTED BOUNDED DESIGNED PROXY** once the committed evidence replays.

This run tests a finite analogue related to the separately reported NRRF639
boundary; it neither imports nor audits the unavailable source. Each local
axiom-geometry and its admitted equality freeze before the line set. It then
derives:

```text
local axiom-geometry / admitted equality
  -> learning lines
  -> directed translation
  -> reflexive-transitive reach
  -> explicit return-chain completion
  -> reach equivalence and exact agreement with admitted equality
  -> closure-saturation topology
  -> local ResolvedIn / witnessed OpenIn
  -> post-freeze translation family
  -> transported registered-question checks
  -> bounded topology receipt.
```

The maze is not replaced by an ordinary undirected graph. Every frozen line has
a direct passage reading and an inverse wall reading. Reverse recoverability
must be witnessed by the rest of the returned learning cycle; the verifier may
not turn an inverse wall into an edge merely to force symmetry.

The deterministic process reloads the frozen geometry, derives and reloads the
forward subset, evaluates forward reach, and only then derives and reloads the
designated-return subset. Disclosure verifies the two parent hashes, unique
line identifiers, disjoint source roles, and exact union into the total line
set; all later analysis consumes that reloaded disclosure. This enforces
geometry parentage, artifact sequencing/reload, and disclosure integrity in
one process. It does not establish independent return generation,
independent-agent provenance, security blinding, or epistemic isolation.

## Reproduce

```bash
python3 experiments/translational_completion_maze.py --assert-reference
python3 -m unittest tests.test_translational_completion_maze -v
```

The reference output is written to
`runs/translational_completion_maze/latest/`. A valid replay is byte-identical;
`evidence_manifest.json` fixes the exact 17-artifact set, sizes, and hashes.

## Required controls

- completion with `LocalIVI_W`;
- completion without `LocalIVI_W`;
- `LocalIVI_W` without completion;
- neither condition;
- raw reach strictly below the frozen equality (`UNDERCOMPLETE`);
- raw reach crossing a frozen equality boundary (`OVERREACH`);
- a one-way equality collapse;
- a candidate that passes equality equivalence but fails polar/return
  naturality;
- a self-certified bounded-topology-receipt request without a completed return.

Here
`LocalIVI_W(F,b) := exists u v, u != v and W_F(u)=b=W_F(v)`. It witnesses
local non-faithfulness only. Translational IVI additionally requires an
admitted natural comparison across frames.

The topology-receipt gate requires completion, `LocalIVI_W`, and exact
reach/equality alignment. The distinct episode-admission gate requires a
process-independent return and an explicitly selected translation. The
reference designed fixture produces one bounded topology receipt and zero
episode-admission tokens.

For an incomplete relation, the run must retain both failure modes:

1. quotienting by strongly connected components loses a one-way reach chain;
2. taking an undirected/equivalence closure invents the missing return.

Neither repair counts as translational completion.

## Evidence boundary

This is a deterministic finite operationalization. It does not independently
audit NRRF639, prove a theorem about every maze or topology, classify homotopy
classes, or constitute an autonomous Slearn/ASI run. The next generative test
must freeze independently produced line sets and independent returns before a
translator sees either one.
