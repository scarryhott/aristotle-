# Grant: Independently Generated Mathematics and Translational Return

## Proposal in one sentence

Test whether a precommitted verification return survives translations discovered only after
independent mathematical systems have been generated, and derive the strongest closure structure
supported by the result—even when that result is a counterexample.

## Operational target

**EXPERIMENTAL DEFINITION:** for this project, a mathematical ASI is an agent whose future
representational transformations cannot reasonably be enumerated and fixed in advance by its
verifier. The agent need not be mystical, conscious, or generally superhuman. The definition
isolates a practical second-order verification problem: the proof kernel can remain fixed while
the definitions, axioms, internal ontology, and proof presentation supplied to it change.

Classical formal verification asks:

`Γ ⊢_L P ?`

Translational verification additionally asks whether a transformation of the frame

`(L, Γ, P) → (L′, Γ′, P′)`

commutes with an independently fixed return. This makes the proposed work complementary to
Lean/Aristotle proof checking.

## Existing formal core

**PROVED:** NRRF627's `TransFrame` gives coherent pairwise translations, verification returns `W`,
relative polar presentations, reversal `J`, and curvature representative `C`. Its central theorem
is:

`(Invariant(Q) ∧ RespectsClosure(Q)) ↔ MeasuredByReturn(Q)`.

The proof constructs the return measurement from a selected presentation and proves translation
compatibility. Its evolutionary theorem similarly characterizes verdicts conserved through every
coherent generation sequence.

**LIMIT:** `TransFrame` already requires the commuting return square and translation coherence.
Consequently, these theorems characterize the implications of that structure; they do not by
themselves prove that independently evolving AI systems instantiate it.

## First necessity result and exact remaining gap

**PROVED:** `NRRF627WeakRequirementsRepresentation.lean` assumes:

1. a language-independent relational occurrence carrier and return carrier;
2. recoverable polar presentations on that carrier;
3. reversible codecs for each language's occurrences, bases, and orientations.

It then *constructs* pairwise `T`, `phi`, and `pi`, along with their identity, composition,
inverse, return-square, and extension laws. With explicit carrier-level `J` and `C`, it constructs a
full `TransFrame` and inherits NRRF627's axiometric and evolutionary characterization theorems.

**CONJECTURED:** the grant's theoretical target is stronger:

`origin independence + recoverability + coherent comparison`

`⇒ existence of a common relational carrier/codecs, or a precisely classified obstruction`.

Thus the new module is a representation bridge and a reduction of the open problem, not a claim
that necessity has already been proved from the weakest possible premises.

## Preregistered Aristotle experiment

**EXPERIMENTAL — OPEN:** the first benchmark is the dihedral group `D4` in two independently
generated forms:

- A: eight permutations acting on the square's vertices;
- B: eight normal forms in `Z/4 ⋊ Z/2`.

Before either generation, the protocol freezes `W` as the complete induced action on the ordered
vertices. Two isolated Aristotle sessions formalize A and B. Their exact artifacts and hashes are
frozen. Only then does a third Aristotle session receive both artifacts and attempt to discover a
translation, inverse, homomorphism theorem, and commuting return square without editing either
source.

The executable gate checks all 8 elements and all 64 ordered products:

`δ_C(F) ∈ {TRUE, FALSE, OPEN}`.

`TRUE` requires total closure and complete proof evidence. `FALSE` requires an explicit witness.
`OPEN` preserves any unresolved bridge, missing proof, or partial translation. Self-certification
does not issue a token.

## Work packages

### WP1 — Blind mathematical generation

Run multiple representation pairs across finite groups, algebraic structures, combinatorial
objects, and theorem reformulations. Separate the sessions and freeze all artifacts before bridge
discovery.

### WP2 — Necessity and obstruction theory

Attempt to derive the carrier/codec hypothesis from weaker operational conditions. When derivation
fails, formalize the minimal obstruction: non-recoverability, non-functorial comparison, partial
translation, incompatible returns, or genuine holonomy.

### WP3 — Adversarial closure

Generate transformations deliberately outside admitted closure. Include wrong orientation,
non-homomorphic maps, total return-breaking maps, partial maps, and presentation-sensitive returns.
The gate must distinguish contradiction from absence of evidence.

### WP4 — Evolving mathematical agents

Move from static representation pairs to agents that independently change definitions,
decompositions, libraries, and proof strategies. Test path independence as a prediction rather than
assuming it in the transition generator.

### WP5 — Fibre and IVI classification

Classify what a non-faithful `W` certifies without reconstructing the occurrence. Test whether fibres
carry richer residues than the reversal walk's proved parity.

## Milestones

| Milestone | Deliverable | Falsifiable exit condition |
|---|---|---|
| M0 | Freeze D4 protocol, prompts, toolchain, and scorer | Any post-hoc change creates a new benchmark version |
| M1 | Two isolated Aristotle formalizations | Buildable immutable artifacts, or an OPEN report naming the first obstruction |
| M2 | Post-hoc translator | Total proved bridge, explicit counterexample, or minimal OPEN obstruction |
| M3 | Adversarial suite | At least one TRUE, one FALSE witness, and one OPEN partial case are correctly separated |
| M4 | Representation theorem | Weaken the codec premise or prove a no-go/countermodel |
| M5 | Agent-evolution study | Empirical path-independence boundary with full receipts and replay |

## Evaluation and falsification

The proposal fails in an informative way if precommitted returns systematically depend on the
chosen presentations, independently generated systems admit no discoverable bridge, or apparently
coherent histories exhibit irreducible path dependence. Those results must be published as
counterexamples or minimal obstructions rather than hidden by redefining admissibility.

The strongest positive outcome is:

`independent systems → frozen artifacts → translation discovered afterward → precommitted return closes`.

The strongest theoretical outcome is a necessity theorem. The minimum successful outcome is a
machine-checked boundary showing exactly which weaker premise fails.

## Relevance to Harmonic

Aristotle supplies the unusual capability this experiment needs: independently generated formal
mathematics plus machine-checkable bridge attempts. The project does not ask Harmonic to accept
`TransFrame` as evidence of real ASI invariance. It asks Harmonic to use Aristotle to test whether
that structure emerges, breaks, or remains OPEN when the mathematical systems are specified first
and the translation is discovered afterward.
