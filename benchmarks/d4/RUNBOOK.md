# Aristotle D4 Blind-Translation Runbook

Status: **EXPERIMENTAL PROTOCOL**. No Aristotle output has yet satisfied this protocol.

## Question under test

Can two mathematical systems generated independently, and connected only after both are frozen,
support a translation whose precommitted relational return closes?

The benchmark uses the same finite mathematical object in two materially different presentations:

- **A:** the action of the square symmetries as permutations of four vertices;
- **B:** normal forms in the semidirect product `Z/4 ⋊ Z/2`.

The return `W` is fixed in [`precommit_return.json`](precommit_return.json): the complete induced
action on the ordered vertex set `[0,1,2,3]`. It is not selected after inspecting a translation.

## Separation of runs

Use three fresh Aristotle sessions with no shared hidden conversation state.

1. Give session A only [`prompts/representation_a.md`](prompts/representation_a.md). It must not see
   session B's prompt or output.
2. Give session B only [`prompts/representation_b.md`](prompts/representation_b.md). It must not see
   session A's prompt or output.
3. Record the exact bytes, SHA-256 digests, model identifiers, toolchain, and complete logs for both
   outputs. Outputs become immutable inputs.
4. Give a third session the two frozen outputs, the frozen return protocol, and
   [`prompts/translator.md`](prompts/translator.md). The translator may not edit either source.
5. Record and freeze the translator output before scoring it.

The coordinator must commit the return protocol before step 1. A changed return protocol creates a
new benchmark version; it cannot be used to rescue the old run.

## Required artifacts

The evidence bundle must contain:

- `representation_a.lean` and its complete Aristotle transcript;
- `representation_b.lean` and its complete Aristotle transcript;
- `translator.lean` and its complete Aristotle transcript;
- a manifest containing byte hashes, model identifiers, prompts, timestamps, and Lean/Mathlib
  versions;
- Lean build output with no `sorry`, `admit`, extra axioms, or modified source artifacts;
- the extracted eight-element translation table;
- the JSON output of the reference scorer.

## Gate

The gate uses contradiction-first three-valued semantics:

| Verdict | Requirement | Token |
|---|---|---:|
| `TRUE` | Both frozen formalisms compile; the total translator compiles; all 8 returns and all 64 ordered products agree | 1 |
| `FALSE` | At least one explicit return or multiplication contradiction is produced | 0 |
| `OPEN` | No contradiction is known, but a formalism, translation, proof, or required case is unavailable | 0 |

A model's assertion that its own result is correct is not return evidence and produces no token.
A Lean compilation failure without a mathematical counterexample is `OPEN`, not `FALSE`.

## Reference adversaries

Run from the repository root:

```bash
python3 experiments/aristotle_d4_closure.py --assert-reference
```

The fixed scorer must return:

- `candidate_correct → TRUE`;
- `adversarial_wrong_sign → FALSE` (reflection is erased);
- `adversarial_partial → OPEN` (reflections are undefined).

These are test fixtures for the gate, not evidence that Aristotle has passed the experiment.

## Falsification value

Any of the following is a successful research outcome:

- a post-hoc translator closes without changing the precommitted `W`;
- an explicit counterexample shows that the predicted invariant fails;
- a minimal missing hypothesis explains why the bridge remains OPEN;
- a translator closes extensionally but exposes a stronger, representation-sensitive claim as false.

The benchmark therefore tests the framework at its boundary rather than admitting only
transformations already defined to preserve return.

