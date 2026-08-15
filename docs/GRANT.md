# Grant: Translational Axiometry for Mathematical Superintelligence

## Research objective

Develop and test **translational axiometry as a verification architecture for mathematical superintelligence**: verification by recoverable relational equality when a mathematical agent can change its language, axioms, geometry, orientation, proof strategy, and internal representation.

Classical formal verification answers:

> Does this proof check in the trusted kernel of this formal presentation?

The second-order mathematical-ASI question is:

> When independently generated axiom-geometries use different presentations, what form of equality can be recovered between them without declaring either presentation the absolute reference frame?

The project treats a reference frame as the form of equality admitted by its axiom geometry. Resolution is therefore conditional on the frame: a question is resolved when it factors through that equality, and open relative to the frame otherwise. Equivalent frames transport both equality and openness. The grant does not seek an absolute frame that eliminates this conditionality; it tests whether coherent translation and relational return continue to provide verification as representational freedom increases.

## Formal foundation already established

The observation-free translational development is the foundation. It does not define closure from an observation map or from one canonical coordinate system.

Across the NRRF618–631 sequence, the formal programme establishes the following conditional structure.

### Translational frame

For languages `ℓ,m`, occurrences and returned relational identities are connected by

```text
W_ℓ : Y_ℓ → B_ℓ
T_ℓm : Y_ℓ → Y_m
φ_ℓm : B_ℓ → B_m

W_m(T_ℓm u) = φ_ℓm(W_ℓ u).
```

No language is the absolute origin. Pairwise translations obey identity and composition laws; reversal `J`, curvature representative `C`, and polar orientation travel naturally with translation.

### Equality and identity

Closure equality is relative equality through return:

```text
u ≡_C v  iff  W_ℓ(u) = W_ℓ(v).
```

Translation preserves and reflects this equality. The returned identity basis is naturally equivalent to the quotient of occurrences by closure equality:

```text
Y_ℓ / ≡_C  ≃  B_ℓ.
```

Thus the identity basis is recoverable from relational equality rather than requiring a privileged presentation.

### Existence and naturality

NRRF630 makes the translational consequences categorical. Occurrences and identities form functors over the language groupoid; return is a natural transformation; reversal and curvature are natural endomorphisms. Natural polar sections exist, and under separation their polar choice is exactly a relative `Z/2` orientation. A universal relational identity exists, and every language-independent, closure-respecting verdict factors uniquely through it. Every language can represent that universal identity; none becomes its privileged origin.

### Frame-conditional openness

NRRF631 formalizes the axiom-geometry/reference-frame claim directly. A reference frame is its admitted form of equality. A question is resolved in a frame exactly when it factors through the quotient by that equality. The same nonconstant question can therefore be resolved in one frame and open in another. Equivalent axiom-geometries transport resolution and openness, so openness is a relation between a question and a frame, not an absolute truth-status emitted by closure.

The runtime consequently records witnesses, counterexamples, and open reference questions separately. `W` returns relational content; it never returns a static TRUE/FALSE/OPEN label.

## Existing bounded operational realization

The repository contains an executed finite classical mathematical-agent realization of selected translational consequences. It is not an Aristotle run and not a claim about arbitrary ASI.

Its causal order is:

```text
(W,E,J,C)_precommit
  ≺ (A,B)_learn+execute
  ≺ freeze
  ≺ (T,φ,π)_posthoc
  ≺ relative equality
  ≺ next basis
```

Two isolated symbolic learners independently learn and execute different D4 presentations before their artifacts are frozen. Only afterward is a cross-language frame family constructed.

The post-hoc construction retains all eight coherent D4 frame forms rather than selecting one canonical coordinate system. Four preserve orientation and four reverse it. Relative reversal remains admissible when its induced `φ` and `π` travel naturally with it. A sign-erasing deformation is the negative control: it fails bijectivity and learned-operation naturality and therefore cannot extend to the required translational comparison.

The finite runtime exhaustively realizes selected NRRF630 consequences:

- return naturality `W_m(Tu)=φ(W_ℓu)`;
- occurrence/identity operation naturality;
- reversal and curvature naturality;
- quotient-basis recovery;
- preservation and reflection of relative equality;
- natural polar sections and reversal of orientation;
- the complete finite `Ω = Bool` instance of universal factorization;
- multiple coherent relative frame forms without an absolute origin.

The runtime distinguishes mathematical admissibility from episode admission. A coherent frame form can exist without receiving an episode receipt; a receipt requires independently witnessed relational contact in the actual episode. Self-certification is not such a witness.

## What the grant is for

The foundational question is no longer whether one fixed `TransFrame` can be made internally invariant. The formal programme already establishes the conditional translational consequences and the bounded runtime realizes them on a finite mathematical system.

The funded question is:

> **As independently operating mathematical agents gain enough freedom to invent new representations and axiom-geometries, can verification continue to be recovered as coherent translation and relational equality without fixing one representation as the absolute reference frame?**

The project has four deliverables.

1. **Frontier-agent translational experiments.** Replace the bounded learners with increasingly capable isolated mathematical agents, ultimately Aristotle, while preserving precommit, independent work, artifact freeze, and post-hoc construction of `(T,φ,π)`.
2. **Axiom-geometry comparison boundary.** Determine which independently generated mathematical frames admit coherent translational equality, which reference questions remain open relative to their equality forms, and which proposed comparisons have explicit operation-level obstructions.
3. **Adversarial representation change.** Test orientation reversal, noncanonical but natural re-expression, proof-preserving representation changes, deliberately non-natural deformations, and transformations outside the verifier's anticipated vocabulary.
4. **Formal return reports.** For every experiment, separate machine-checked relational equalities from counterexamples and from questions still open relative to the compared frames. Formal proof-search statuses may be reported, but they are never outputs of closure itself.

## Scale-up protocol

Preserve the causal boundary:

```text
(W,E,J,C)_precommit
    → independent mathematical work
    → immutable artifact freeze
    → (T,φ,π) discovered afterward
    → W_m(Tu) = φ(W_ℓu) and transported equality/open questions
    → independently returned relation may enter the next learning basis
```

The key measurements are not agreement with a canonical coordinate system. They are whether independently generated frames support coherent relative comparisons; whether valid orientation changes remain admissible; whether non-natural transformations expose explicit obstructions; whether nontrivial questions remain conditionally open under the relevant axiom geometry; and whether returned equality can support subsequent mathematical work.

## Success and falsification

A successful project need not show that every mathematical frame closes with every other frame. That would contradict the conditional role of axiom geometry.

Positive evidence is the discovery of post-hoc translations whose operations commute and whose relational equality transports naturally across independently generated frames.

Negative evidence is an explicit obstruction showing why a proposed comparison cannot extend to such a translation.

An open result is also substantive when the current frame equality does not resolve the reference question and no counterexample selects non-admissibility. Openness is preserved as frame-relative structure rather than converted into an arbitrary static verdict.

The architecture is challenged if, as representational freedom increases, the proposed translational conditions cease to distinguish coherent relative equality from non-natural deformation, or if the framework requires secretly privileging one fixed language to make its comparisons work.

## Why this matters for mathematical superintelligence

A verifier that requires a future intelligence to retain today's mathematical representation risks confusing verification with a capability ceiling. A sufficiently capable mathematical system may alter not merely a theorem but its language, axioms, geometry, orientation, and internal basis of representation.

Translational axiometry proposes a different invariant: not static identity of presentation, but **recoverable relational equality between axiom-geometric reference frames**.

The grant tests whether that conditional, origin-free form of verification scales from the machine-checked theory and finite exhaustive realization to mathematical agents whose representations are increasingly autonomous and less human-selected.
