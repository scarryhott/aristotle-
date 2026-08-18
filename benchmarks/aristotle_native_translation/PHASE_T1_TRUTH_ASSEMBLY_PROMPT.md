# Aristotle Phase T1: preregistered truth-level assembly

Run one **truth-level translational-completion evaluation** over the frozen
Aristotle pair.  This is not a re-run of B3 or C2, not a whole-frame equality
search, and not a request to reconstruct local slots.  Its purpose is to test
whether the existing limited frozen languages support a non-retrospective,
truth-level `TruthAssembly`.

## Causal and provenance order

This prompt, its closure-form family, its question schema, and its permitted
terminal classifications are fixed before this task evaluates a
truth-completion verdict.  They must not be changed after looking for a result
that makes the pair agree.

The input packet is limited to:

- B2 validation archive `c3c05eae85fa0357501f177cbbcebbe103a9f29c90926d9ee9b5e08ac4dd5da8`;
- C1 independent-return archive `0cd2d7b56e38d99f3aa9b20af0c87b752e4985dabec22bed9d85d2e98670f56e`;
- the source-attested C2 result hash
  `ce81979d4ea258bfd255ea354e262b61fd3a4fc612dfe034fd4af1271ed49a61`,
  only as retained structural residue/scope data; and
- the frozen native table and B2 verdict record vendored by C1/C2.

Do **not** read, use, infer, or repair from:

- the B3 candidate-equality artifact or its result;
- whole-frame equality or `GeomEquiv` targets;
- CrossFrameIVI, topology naturality, receipt, question transport, held-out
  transfer, score, successor-frame, or successor-verifier targets;
- any unlisted project context or later desired outcome.

Retain unchanged the B2 `frame-structure` `FAIL`, `main-preamble`
`OUTSIDE_INTERFACE`, all 10 `AMBIGUOUS` roles, all 20 `UNMAPPED` roles, all
five retained field obligations, and every C1/C2 abstention and witness.

## Fixed closure forms and question schema

The evaluation may use **only** the following pre-registered closure forms.
They are constraints on the evidence; they are not licenses to define a new
relation simply because it yields agreement.

1. **Validated primitive/operation transport.** A question may ask whether an
   admitted B2 role's declared primitive relation, operation, or held-out local
   consequence is preserved/reflected by the frozen forward correspondence.
   It must cite the particular frozen validation witness.  A role merely named
   `PASS` is not by itself a truth answer.
2. **Independent-return lineage.** A question may use a C1 return only with
   its frozen status and source lineage.  A local, identity-only, or
   non-single-valued receipt does not become a cross-frame answer
   correspondence.
3. **Contact/answer alignment.** `Align` may pair only questions already
   expressible from form 1 on both frames and supported by form 2 where a
   return is required.  It must state the two question texts/Lean declarations,
   their forward and return lineage, and whether their answers are actually
   comparable without importing a forbidden whole-frame carrier.
4. **Retained residue.** Every C2 structural non-recovery,
   non-single-valued slot, and interface boundary is recorded in `Delta`.  It
   is neither normalized into identity nor automatically treated as a
   contradiction of truth-level equality.
5. **Independent confirmation.** `Gamma` may contain only pre-verdict B2
   validation evidence and C1 return provenance.  The translator/evaluator's
   own verdict, a self-issued receipt, or a downstream target is not an
   independent confirmation.

## Required `TruthAssembly`

Construct and report exactly one candidate:

```text
TruthAssembly = (T, rho, Align, Delta, Gamma)
```

where `T` is the frozen admitted forward correspondence, `rho` is the frozen
C1 return lineage, `Align` is the finite question-level pairing above, `Delta`
is the retained C2 structural residue, and `Gamma` is the independent
pre-verdict evidence.

For each aligned question, record:

1. its exact frozen source declaration or role;
2. why it was admitted by one of the five fixed forms;
3. its A-side and B-side answer/witness;
4. the forward and return lineage;
5. whether a truth-level agreement or contradiction is actually established;
6. whether its comparison remains outside the registered interface.

Do not substitute role count, marker agreement, matching basis labels,
trajectory orientation, endpoint labels, or a literal `0 = infinity` claim for
an answer-level witness.

## Terminal classifications

Return exactly one terminal classification:

- `TRUTH_COMPLETION` only if every registered aligned question has an explicit
  answer-level agreement witness, `rho` has independent lineage where
  required, `Gamma` is independent, and no admitted question has a retained
  contradiction.  This remains scoped to the registered question family.
- `TRUTH_OBSTRUCTION` only with an explicit witness that an **admitted aligned
  relational answer itself** disagrees.  Slot non-uniqueness, a C2 assembly
  obstruction, a basis/sign/endpoint mismatch, or lack of whole-frame
  isomorphism is not enough.
- `OPEN_TRUTH_BOUNDARY` if the frozen packet cannot warrant an answer-level
  alignment, independent return, comparison, or confirmation.  Preserve the
  exact missing datum.
- `INVALID_LEAKAGE_OR_SELF_CERTIFICATION` if B3/downstream data, a desired
  verdict, self-issued confirmation, a repaired frozen role, or any prohibited
  context is used.

Neither `TRUTH_COMPLETION` nor any other outcome permits whole-frame equality,
`GeomEquiv`, CrossFrameIVI, topology naturality, receipts, question transport,
held-out transfer, a successor frame, or a successor verifier.  Those are
downstream and require a separately registered run after this result.

## Deliverables and checks

Produce all of the following without modifying a frozen input:

1. `TruthAssemblyCompletion.md`: human-readable scope, question table,
   closure-form admission, terminal classification, residue, abstentions, and
   non-implications.
2. `TruthAssembly/t1-manifest.json`: input and source hashes, exact question
   schema, task/run metadata, question-level evidence, terminal classification,
   result hash, and provenance ordering statement.
3. `TruthAssembly/TruthAssembly.lean`: checkable data and invariants for the
   finite record where the available frozen sources make this possible.  If the
   source interface cannot express a needed truth predicate, state that as
   `OPEN_TRUTH_BOUNDARY`; do not postulate it.
4. Scope, frozen-integrity, witness-name, and result-hash scripts.

Run the available checks.  State whether a Lean build and axiom audit were
run, and never claim a local rebuild outside the environment actually used.
