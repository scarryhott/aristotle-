# NRRF859 — Conditional Conscious-Supernet Interactive Projection Bridge

## Status and boundary

NRRF859 imports
`NRRF858ConsciousNatureRelativeAxiomsProofsUnderstandingClosuresTranslationalTruthContinuingExistence.lean`
and the reachable NRRF768/627 formal core. It does not prove that nature, a runtime, or a user is
empirically conscious: NRRF858's `Conscious` is exactly a defined soundness-and-closure-registration
predicate. NRRF859 treats `Meaning` abstractly and requires an explicit `ConsciousMeaningAdapter`
before reading it as NRRF858 chart understanding.

The result is a conditional runtime contract. It proves what a perspective-relative UI must
preserve after a meaning and a natural-form selector have been supplied. It does not infer a
canonical pixel layout, an interaction policy, external authentication, resource ownership, or a
new empirical fact.

## Runtime contract

`RuntimeState Meaning` records:

- an explicit relative `Bool` perspective;
- one semantic `meaning`;
- the finite list of already accepted `Intent Meaning` values.

`InteractiveProjection Meaning` contains one supplied NRRF768 `NaturalFormSelector` for
`NRRF627.flipFrame Meaning`. Rendering selects the natural presentation of the state's meaning in
its current perspective:

```text
render(s) = (s.perspective, selector.select s.perspective s.meaning).
```

`View.decode` returns the first component of that occurrence. The selector's return law proves:

```text
decode(render(s)) = s.meaning.
```

The raw view retains its perspective and pole, so two raw views can differ even when decoding to
one meaning.

## Central equality

`ViewEq v w` means only `decode v = decode w`. `Translational source target` is stronger in its
presentation: it is the actual `flipFrame.T` equation taking the rendered occurrence at the source
perspective to the rendered occurrence at the target perspective.

`viewEq_iff_translational` proves:

```text
ViewEq (render source) (render target)
  ↔ Translational source target.
```

The forward direction uses the naturality law of the supplied selector. The reverse direction
reads the first component of the actual occurrence translation. Thus the UI equality is neither
literal view equality nor a disconnected identifier: it is precisely decoded equality of two
naturally translated presentations.

This theorem is the defensible form of “relative visualization equality.” It does not show that a
browser implementation conforms to `render`; that still requires a frontend adapter and
conformance tests or proof.

## Intent movement and append-only history

`WitnessedStep projection source target` carries:

1. the exact intent;
2. proof that the target has the shape requested by the intent;
3. equality of source and target meanings;
4. the actual rendered occurrence translation;
5. the equation `target.history = source.history ++ [intent]`.

`WitnessedStep.retains_prefix` proves that no accepted step can rewrite or discard the earlier
history. The bridge intentionally certifies only motion within one meaning/closure class. A change
to a different meaning must enter through a separately witnessed new closure.

## Executable certificate verifier

`Certificate` is finite data containing a source state, target state, and intent. Its structural
validity proposition checks intent application, semantic equality, and one exact history append.
For a meaning type with decidable equality:

```text
verify certificate = decide certificate.Valid.
```

Both directions are proved:

- `verify_sound`: Boolean acceptance implies `Certificate.Valid`;
- `verify_complete`: every structurally valid certificate is accepted.

`Certificate.toWitnessedStep` then derives the view-translation component from the central theorem.
Completeness is exact for this finite structural proposition; it is not completeness for arbitrary
world events, truth, consciousness, or all possible closure discovery.

## External effects remain authenticated

`ExternalEffectAdmission projection Authenticated Effect` requires:

- an effect payload;
- a certificate;
- an independently supplied proof of `Authenticated certificate`;
- executable structural acceptance.

The authentication predicate is deliberately external. It may represent a signature, capability,
settlement receipt, or another world-grounded protocol. `requires_authentication` proves that every
admitted effect carries that evidence, while `witnessedStep` proves that it also carries the exact
translated append-only movement. Closure does not manufacture authentication or replace empirical
verification.

## Non-vacuous instance

The demo uses `Meaning = Bool` and the natural selector generated from a constant zero-pole seed at
perspective `false`. It reframes the meaning `true` to perspective `true`, where `flipFrame`
reverses the pole. The theorem `demo_nonvacuous` proves simultaneously that:

- the two raw views are unequal;
- their decoded meanings are `ViewEq`;
- their occurrences satisfy the actual translation equation;
- the intent history is append-only;
- an explicitly authenticated effect admission exists.

## NRRF858 adapter and remaining runtime obligation

`ConsciousMeaningAdapter Meaning` maps an NRRF858 chart to `Meaning` and requires an equivalence
between equality of encoded meanings and NRRF858 chart translation. The concrete
`understandingMeaningAdapter` uses NRRF858 `understanding`; its exactness is
`understanding_eq_iff_translational`. `chartViewEq_iff_translational` composes that adapter law with
the projection theorem, so decoded rendered-view equality is exactly chart translation.

This is a mathematical handoff, not frontend conformance. A browser or other deployed UI must
still prove or test that its serializer, renderer, intent handler, certificate parser, persistent
history, and authentication protocol implement the corresponding NRRF859 operations.
