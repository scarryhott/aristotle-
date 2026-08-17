# Three-part assumption-interaction runbook

Status: **EXECUTED BOUNDED PROXY** after the committed receipt bundle is regenerated and checked.

Run:

```sh
python3 experiments/three_part_assumption_interaction_asi.py --assert-reference
python3 -m unittest tests.test_three_part_assumption_interaction_asi -v
lake build
```

The protocol registers the existing total questions plus distinct external-geometry and
candidate-packet hashes. Parts 1 and 2 run without either packet as an input. After both freeze, the
geometry packet is checked and each equality is instantiated in its own declared terms. Those frame
artifacts freeze before the candidate packet is checked and consumed. This is causal input
separation inside a scripted fixture, not security blinding.

The selected trace is

```text
frozen B --native GeomEquiv--> frozen A
         --external GeomEquiv--> external coordinate isolation
         --split relation--> external D4 x C2 isolation
         --closure quotient--> returned A isolation.
```

The exact legs require equality preservation and reflection. The split and quotient legs are
typed separately because neither is bijective: the split relation identifies every new `z=1`
residue, and the quotient records its expected reflection loss. The complete composite must recover
the already admitted native occurrence relation and returned basis. Every counterexample remains in
the evidence; a partial proposal is `PENDING_COMPARISON`, never `OpenIn`.

“Continuous” means a finite, gap-free relational and receipt lineage. No topology is asserted. The
fixture is D4-sized and deterministic; it is not an ASI or Aristotle result, and it does not claim
that arbitrary external assumptions preserve closure.
