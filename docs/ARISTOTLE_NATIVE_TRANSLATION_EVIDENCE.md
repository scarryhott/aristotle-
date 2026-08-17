# Aristotle native-translation evidence index

This page is the reviewer entry point for the executed frontier-agent run. The
frozen manifests are committed under
[`runs/aristotle_native_translation/`](../runs/aristotle_native_translation/);
the full source/result archives remain Aristotle downloads because they are
authenticated, project-scoped artifacts. Every archive is identified below by
its SHA-256 hash and its Harmonic request link.

This evidence is on the `agent/full-stack-translational-closure` branch. It is
not part of the repository default branch until the associated pull request is
merged.

## Causal sequence and present boundary

```text
independent F_A, F_B
  -> frozen native declaration-role translation T_AB
  -> identity-independent validation
  -> candidate equality on admitted subinterface only
  -> independent local return evidence
  -> completion / CrossFrameIVI / topology     (OPEN)
```

The result is not a whole-frame equivalence. The frozen `frame-structure`
failure blocks promotion to `F_A ≃ F_B` or `GeomEquiv(F_A,F_B)`.

| Stage | Harmonic request(s) | Frozen result | Committed record |
| --- | --- | --- | --- |
| A — independent frame generation | [A](https://aristotle.harmonic.fun/dashboard/requests/ed828dd7-3c4a-4211-99b3-906e365f3534), [B](https://aristotle.harmonic.fun/dashboard/requests/2f01c523-89cf-4011-8d5f-446308c6d226) | Two isolated single-frame artifacts; no translation/equality claim. | [`initial manifest`](../runs/aristotle_native_translation/initial_isolated_generation/manifest.json) |
| B — frozen native translation | [request](https://aristotle.harmonic.fun/dashboard/requests/e4b59a82-d7b8-46fd-b7e5-a8ba059f44a1) | 66 roles: 36 `MAPPED`, 10 `AMBIGUOUS`, 20 `UNMAPPED`; no cross-frame Lean map. | [`B manifest`](../runs/aristotle_native_translation/phase_b_native_translation/manifest.json) |
| B2 — identity-independent validation | [request](https://aristotle.harmonic.fun/dashboard/requests/ea684ccd-f50d-4e6f-97ca-31c2463517c5) | 34/36 mapped roles pass; one structural failure; one outside-interface item; all abstentions retained. | [`B2 manifest`](../runs/aristotle_native_translation/phase_b2_validation/manifest.json) |
| B3 — candidate equality | [request](https://aristotle.harmonic.fun/dashboard/requests/eda32ca8-d7dd-4336-8843-619a424086a1) | `ACCEPTED_ON_SUBINTERFACE` for exactly 34 roles; whole-frame equality and `GeomEquiv` blocked. | [`B3 manifest`](../runs/aristotle_native_translation/phase_b3_candidate_equality/manifest.json) |
| C1 — independent return | [request](https://aristotle.harmonic.fun/dashboard/requests/799b6bf1-bd23-4f55-8725-75bd42bde00e) | 20 determined, 5 unique, 1 round-trip, 8 identity-only local receipts; no assembled cross-frame return or completion claim. | [`C1 manifest`](../runs/aristotle_native_translation/phase_c1_independent_return/manifest.json) |

## Why the raw artifacts are not committed

The runtime outputs are project-scoped Aristotle tarballs. The manifests retain
their project/task identifiers, SDK version, output hashes, input lineage, and
explicit abstentions so a reviewer with project access can retrieve and verify
the exact result. The repository does **not** replace those artifacts with
handwritten summaries or claim a local Lean re-build of their frozen source.

The next permitted experiment is C2: evaluate whether the C1 local return
receipts assemble into recoverability/completion over the admitted interface.
It must preserve the structural obstruction, excluded entries, and all C1
global abstentions.
