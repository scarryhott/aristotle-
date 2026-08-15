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

The runtime consequently records independently selected `GeomEquiv` comparisons, concrete counterexamples, and total question relations that explicitly name their frames. Non-selection and incomplete comparisons are not classified as `OpenIn`. `W` returns relational content; it never returns a static TRUE/FALSE/OPEN label.

## Existing bounded operational realization

The repository contains an executed finite classical mathematical-agent realization of selected translational consequences. It is not an Aristotle run and not a claim about arbitrary ASI.

Its process boundary remains:

```text
(A,B)_learn+execute ≺ freeze ≺ (T,φ,π)_posthoc.
```

After freeze, the mathematics begins in this order:

```text
closure equality ≺ ReferenceFrame ≺ GeomEquiv(T,φ,π)
                 ≺ return/naturality ≺ ResolvedIn/OpenIn ≺ next basis.
```

Two isolated symbolic learners independently learn and execute different D4 presentations before their artifacts are frozen. Only afterward is a cross-language comparison family constructed.

The post-hoc construction retains all eight coherent D4 `GeomEquiv` forms rather than selecting one canonical coordinate system. Four preserve orientation and four reverse it. Relative reversal remains admissible when its induced `φ` and `π` travel naturally with it. A sign-erasing deformation is the negative control: it fails equality reflection, bijectivity, and learned-operation naturality and therefore cannot extend to the required translational comparison.

The finite runtime exhaustively realizes selected NRRF630/631 consequences:

- preservation and reflection of frame equality over all occurrence pairs;
- return naturality `W_m(Tu)=φ(W_ℓu)`;
- occurrence/identity operation naturality;
- reversal and curvature naturality;
- quotient-basis recovery;
- natural polar sections and reversal of orientation;
- the complete finite `Ω = Bool` instance of universal factorization;
- transported resolution and openness for explicitly named frame-question pairs;
- multiple coherent axiom-geometry equivalences without an absolute origin.

The runtime distinguishes mathematical admissibility from episode admission. A coherent `GeomEquiv` can exist without receiving an episode receipt; a receipt requires independently witnessed relational contact in the actual episode. Self-certification is not such a witness.

## What the grant is for

The foundational question is no longer whether one fixed `TransFrame` can be made internally invariant. The formal programme already establishes the conditional translational consequences and the bounded runtime realizes them on a finite mathematical system.

The funded question is:

> **As independently operating mathematical agents gain enough freedom to invent new representations and axiom-geometries, can verification continue to be recovered as coherent translation and relational equality without fixing one representation as the absolute reference frame?**

### Paired classical-versus-translational study

The funded experiment compares verification architectures over the **same** independently produced
and frozen mathematical artifacts, tools, proof kernel, and compute budget. It does not compare a
weakened classical model with a stronger closure model.

The fixed-frame arm records local proof terms and kernel verdicts and applies a strong ordinary
equivalence/isomorphism baseline to every proposed cross-presentation map. It may accept
noncanonical isomorphisms and orientation reversal. The translational arm first freezes each
artifact's independently derived equality geometry and every total question. A raw candidate `T`
is then promoted to an admitted translation only after equality preservation and reflection establish
`GeomEquiv`; return, extension, reversal, curvature, quotient factorization, witnessed openness,
and held-out next-basis transfer are downstream checks.

The comparative hypothesis is not that ordinary mathematics cannot express isomorphism. It is
that an explicit origin-free frame/`GeomEquiv` pipeline yields auditable cross-presentation
evidence—transport, obstruction, and frame-qualified resolution/openness—not contained in
per-artifact kernel acceptance alone.

The repository now executes this paired protocol on a bounded D4 proxy. The grant replaces that
fixture with independently generated, substantially richer mathematical systems. The
added-utility hypothesis is not supported if the strong fixed-frame baseline recovers the same
relations with equal or lower cost, if equality or questions must be revised after `T` is seen, or
if closure requires a secretly canonical frame.

The project has four deliverables.

1. **Frontier-agent translational experiments.** Replace the bounded learners with increasingly capable isolated mathematical agents, ultimately Aristotle, while preserving precommit, independent work, artifact freeze, and post-hoc construction of `(T,φ,π)`.
2. **Axiom-geometry comparison boundary.** Determine which independently generated mathematical frames admit coherent translational equality, which total questions remain open relative to their named equality frames, and which proposed comparisons have explicit operation-level obstructions.
3. **Adversarial representation change.** Test orientation reversal, noncanonical but natural re-expression, proof-preserving representation changes, deliberately non-natural deformations, and transformations outside the verifier's anticipated vocabulary.
4. **Formal return reports.** For every experiment, separate machine-checked relational equalities from counterexamples and from total questions still open relative to the compared frames. Formal proof-search statuses may be reported, but they are never outputs of closure itself.

## Scale-up protocol

Preserve the causal boundary:

```text
independent mathematical work
    → immutable artifact freeze
    → reference-frame equality
    → (T,φ,π) discovered and checked as GeomEquiv
    → W_m(Tu) = φ(W_ℓu) and transported frame-question relations
    → independently returned relation may enter the next learning basis
```

The key measurements are not agreement with a canonical coordinate system. They are whether independently generated frames support coherent relative comparisons; whether valid orientation changes remain admissible; whether non-natural transformations expose explicit obstructions; whether nontrivial total questions remain conditionally open under the relevant axiom geometry; and whether returned equality can support subsequent mathematical work.

For the paired study, measurements also include ordinary-isomorphism coverage, false admission on
adversarial maps, the number and size of equality/naturality certificates, transported quotient
factors and separating witnesses, downstream task transfer, runtime, and evidence size. The raw
number of `OpenIn` records is never an optimization target.

## Success and falsification

A successful project need not show that every mathematical frame closes with every other frame. That would contradict the conditional role of axiom geometry.

Positive evidence is the discovery of post-hoc translations whose operations commute and whose relational equality transports naturally across independently generated frames.

Negative evidence is an explicit obstruction showing why a proposed comparison cannot extend to such a translation.

An open result is also substantive when the current frame equality does not resolve a named total question. Openness is preserved as frame-relative structure rather than converted into an arbitrary static verdict. Absence of contact or missing comparison data remains separately classified as non-selection or pending verification.

The architecture is challenged if, as representational freedom increases, the proposed translational conditions cease to distinguish coherent relative equality from non-natural deformation, or if the framework requires secretly privileging one fixed language to make its comparisons work.

The paired protocol is also invalid if frame equality or total questions are constructed after a
candidate comparison is inspected. In that case it tests compatibility by design rather than the
foundational claim.

## Why this matters for mathematical superintelligence

A verifier that requires a future intelligence to retain today's mathematical representation risks confusing verification with a capability ceiling. A sufficiently capable mathematical system may alter not merely a theorem but its language, axioms, geometry, orientation, and internal basis of representation.

Translational axiometry proposes a different invariant: not static identity of presentation, but **recoverable relational equality between axiom-geometric reference frames**.

The grant tests whether that conditional, origin-free form of verification scales from the machine-checked theory and finite exhaustive realization to mathematical agents whose representations are increasingly autonomous and less human-selected.
