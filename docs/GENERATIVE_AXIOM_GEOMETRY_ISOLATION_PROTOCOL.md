# Generative Axiom-Geometry Isolation Protocol

Status: **PROTOCOL EXECUTED FOR A BOUNDED PROXY; FRONTIER EXPERIMENT OPEN**.

This is the scale-up design after the scripted D4 fixtures. It asks whether two generative
mathematical processes can choose locally well-defined but materially different axiom-geometries
within precommitted generation contracts, freeze them without knowledge of a bridge, and only then
support conditional natural-existential evidence through an explicit translation. The bounded
reference implementation and raw-agent assay are reported in
[`GENERATIVE_AXIOM_GEOMETRY_ISOLATION_RUN.md`](GENERATIVE_AXIOM_GEOMETRY_ISOLATION_RUN.md).

## The three-part comparison

### 1. Classical well-defined/free-choice isolation

Generator A and generator B receive the same task envelope, proof-kernel policy, tool allowance,
and resource budget in separate subprocesses. “Free choice” is relative to each registered
generation contract: a bounded fixture may fix carrier size and an equality schema while leaving
the construction family, local labels, presentation, and proof route isolated. A later frontier
run may widen those choices, but it must record every shared constraint. The classical control
asks whether each resulting system is internally well-defined and locally verified; it does not
infer a cross-frame identity merely because both systems solve the same task.

Each generator must emit and locally audit a frame `F_i` and a finite registered family of total
questions `Q_i`. A frame is assumed conditionally and evaluated in exactly the equality it
declares. “Assumed” does not mean globally true or immune to counterexample. It means that the
local audit may accept or reject that supplied geometry but may not replace it with the other
generator's equality or a preferred external normal form.

The two frame and question bundles are content-addressed and frozen before either is disclosed to
the translator.

### 2. Post-freeze translational-open search

Only after both local freezes does a disclosure event make the immutable bundles available to a
fresh translation-search process. The translator may propose zero, one, or many explicit
`(T,phi,pi)` candidates. No candidate correspondence, canonical identifier, shared hidden normal
form, or expected successful map may be encoded in the generation prompts.

The required causal order is:

```text
F_A, F_B, Q_A, Q_B
          ≺ disclose
          ≺ candidate (T,phi,pi)
          ≺ GeomEquiv
          ≺ naturality
          ≺ frame-qualified resolution/openness evidence.
```

The first four artifacts are immutable before disclosure. A candidate remains proposal data until
a separately invoked verifier checks both directions of frame equality:

```text
x ~_A y  ↔  T(x) ~_B T(y).
```

Only an admitted `GeomEquiv` proceeds to the `W/E/J/C`, operation, and registered-question
naturality checks. “Translational-open search” describes freedom in the post-freeze candidate
search. It is not the formal predicate `OpenIn`.

### 3. Conditional natural-existential evidence

A passing candidate supplies existential evidence only for the particular frozen frames and
declared laws in its certificate:

```text
∃ (T,phi,pi), GeomEquiv(F_A,F_B,T) ∧ Naturality(F_A,F_B,T,phi,pi).
```

This is **conditional** evidence because the two generated frames, their equality assumptions,
and the verifier contract are explicit premises. It is **natural** because the registered return
and closure operations commute. It is **existential** because the evidence contains an actual
witness, not model confidence or a self-description. It does not establish that every
axiom-geometry translates, that either generator is an ASI, or that this protocol supplies evidence
before the certificate is checked.

The admissible result classes are:

| Result | Required evidence | Meaning |
|---|---|---|
| `NATURAL_EXISTENTIAL_WITNESS` | complete `(T,phi,pi)`, `GeomEquiv`, and naturality certificate | one conditional cross-frame witness exists |
| `EQUALITY_OBSTRUCTION` | explicit preservation or reflection counterexample | this candidate is not a geometry equivalence |
| `NATURALITY_OBSTRUCTION` | admitted `GeomEquiv` plus a downstream commuting-law counterexample | equality transports, but the requested closure structure does not |
| `COHERENT_FAMILY_UNSELECTED` | two or more admitted witnesses with no independent selector | multiple coherent forms remain; no form is selected |
| `PARTIAL_COMPARISON` | incomplete candidate domain or certificate | comparison is incomplete |
| `NO_ADMITTED_CANDIDATE_FOUND_UNDER_BUDGET` | complete search log and exhausted registered budget | no witness was found by this search; global nonexistence is not proved |

Rejected, partial, absent, and unselected comparisons are never `OpenIn`. For a named total
question `Q`, `OpenIn(F,Q)` may be emitted only with an explicit witness
`x ~_F y` and `Q(x) != Q(y)`. A resolved question must instead include its quotient factor.

## Isolation boundary

The first implementation may use fresh subprocesses, distinct working directories, immutable
input manifests, and receipt ordering to demonstrate causal non-use of undisclosed artifacts.
Those controls do not by themselves establish:

- security isolation against a malicious process able to read the host filesystem;
- statistical independence between generators using related training data or model weights;
- autonomous mathematical agency; or
- an ASI or Aristotle execution.

A frontier run must report the exact model, prompt, tools, retrieval sources, environment, budget,
and process boundary for each role. If strong non-access is claimed, it requires an actual sandbox
or separately administered session rather than a Boolean field in an artifact.

## Required evidence bundle

An executable run must preserve:

1. the precommitted task, generator prompts, budgets, proof policy, and total-question schemas;
2. `F_A`, `F_B`, `Q_A`, and `Q_B` with hashes and local audit outputs;
3. a disclosure receipt later than all four freezes;
4. every candidate with a creation receipt later than disclosure;
5. separate preservation, reflection, and downstream naturality results;
6. quotient factors or explicit `OpenIn` witnesses for every reported question classification;
7. complete rejected, partial, and unselected outcomes, including retries;
8. search-resource accounting sufficient to interpret “not found under budget”; and
9. an immutable receipt chain linking any admitted witness or next-basis use to its exact frames.

No admission token may be issued for local kernel acceptance alone, model self-certification,
candidate multiplicity, or a budget-limited failure to find a bridge. A later runtime may define a
token for an externally selected natural witness that is actually used as a next basis, but that
policy is not executed here; this run issues zero tokens.

## Falsification and invalidation

The protocol is invalidated if:

- either frame, admitted equality, or registered question changes after disclosure;
- generation receives a candidate bridge, target coordinate dictionary, or shared canonical IDs;
- a candidate or its expected verdict exists before the frame/question freeze;
- the target frame is evaluated using the source frame's equality;
- `GeomEquiv` is admitted from preservation without reflection;
- naturality is copied from the candidate constructor instead of checked by a separate verifier;
- failed attempts or alternative coherent candidates are omitted from the receipt history;
- a search outcome or non-selection is mislabeled `OpenIn`; or
- subprocess separation is reported as security blinding, autonomous generation, or ASI evidence.

The broader added-value hypothesis is weakened or falsified if repeated separately administered
generative runs only close after reduction to a privileged normal form, if no nontrivial
post-freeze witness survives separately executed naturality checks, or if a strong classical
equivalence baseline emits the same complete evidence with equal or lower cost. A single explicit
obstruction is not itself a failure of the conditional architecture; it is a valid result
identifying where the attempted relation stops.
