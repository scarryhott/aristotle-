# Grant: Translational Axiometry for Mathematical Superintelligence

## Research objective

Develop and test **translational axiometry as a verification architecture for mathematical superintelligence**.

The foundational proposal is prior to the verification application: **axioms are relative to their geometries/reference frames, while truth-level relational identity is sought through translation rather than inherited from a privileged origin language.** A novel mathematical frame is first admitted conditionally in its own unified axiom-geometry. It is not judged by silently treating an older frame as neutral.

The central question is:

> **Can truth remain auditable across changing mathematical frames when local/global, `0`/`∞`, or other relative presentations need not be equal in quality or quantity, but may be equal in the truth of a translational closure relation?**

The project does not claim ordinary arithmetic `0 = ∞`. It distinguishes relative presentation from truth-level closure equality:

```text
local != global             as relative presentations
0 != ∞                      as relative presentations
local = global in closure   at truth-level relational identity
0 = ∞ in closure            at truth-level relational identity
```

The thesis is therefore not that a closed truth is preserved unchanged. Closure is **interactive continual completion**: a truthful relation translates into a further relation, whose independently audited completion may become the basis of the next axiometry.

```text
origin-independent translation
    → relative axiom ↔ geometry frames
    → natural choice / interaction
    → translation + independent return
    → truth-level relational completion
    → further relation / next frame
    → externally auditable consequence
    → mathematical-ASI verification.
```

Classical formal verification asks whether a proof checks inside a trusted formal presentation. Translational verification asks the additional question:

> **When independently generated axiom-geometries stand in their own mathematical forms, what truth-level relational identity can be recovered between them without declaring either frame the absolute definition of the other?**

The grant does not seek a final absolute frame. It tests whether translation, natural choice, relational return, and completion remain useful as mathematical agents gain enough freedom to generate substantially new formal frames.

## What counts as an Aristotle-generated frame

For this grant, an **Aristotle-generated axiom-geometric frame** is not merely a Lean file that Aristotle produces from a representation supplied by the experimenter.

A qualifying frame is an artifact

```text
F_A = (A_A, G_A, ~_A, O_A, Q_A)
```

whose substantive mathematical organization is produced by an independent Aristotle session from a frame-neutral mathematical objective:

- `A_A`: its local primitive assumptions/axioms;
- `G_A`: the mathematical geometry or structure those assumptions organize;
- `~_A`: the equality admitted by that local axiom-geometry;
- `O_A`: its primitive and derived operations;
- `Q_A`: total questions registered before cross-frame disclosure.

To qualify as Aristotle-generated:

1. the session is not given another frame's representation, target coordinates, desired `(T,phi,pi)`, or canonical translator;
2. the frame is evaluated internally under its own declared axiom-geometry;
3. its complete artifact and registered questions are content-addressed and frozen before another frame or translator is disclosed;
4. the later translator/verifier may inspect but may not repair or redefine the frozen frame.

Thus two qualifying sessions satisfy

```text
objective → Aristotle A → F_A → internal audit → freeze
objective → Aristotle B → F_B → internal audit → freeze

F_A, F_B, Q_A, Q_B ≺ disclosure ≺ native translation.
```

The evidence freeze is methodological. It prevents retrospective repair of one episode; it is not a metaphysical claim that axiometry itself must remain frozen after closure.

## Formal foundation already established

The observation-free translational development does not define closure from an observation map, preserved truth-status enum, entropy quantity, or canonical coordinate system. Closure is instead treated as the truth condition for an auditable relation to continue through translation and return into a further relation.

For languages `l,m`, the formal translational frame contains

```text
W_l : Y_l → B_l
T_lm : Y_l → Y_m
phi_lm : B_l → B_m

W_m(T_lm u) = phi_lm(W_l u).
```

No language is the absolute origin. Pairwise translations obey identity and composition laws; orientation, reversal `J`, and curvature representative `C` travel with translation.

The metaphysical reading is stronger than ordinary covariance: the common truth-level identity of relative frames is not assumed first and then transported. The commuting square is a formal witness that a chosen relation remains recoverable through translation. It does **not** imply that a finished truth-object is preserved unchanged or that the local presentations become quantitatively identical.

Within a supplied translational frame, closure equality is

```text
u ≡_C v  iff  W_l(u) = W_l(v).
```

Translation preserves and reflects this local equality. The broader programme now explicitly distinguishes that supplied-frame law from closure-native axiometric evolution, where a completed relation can generate a new frame used by the next interaction.

The separately reported NRRF633 result shows that, conditional on an existing translational frame, a returning and grounded relational definition is uniquely closure equality. The separately reported NRRF639 result connects translational completion and IVI. Sources absent from this checkout are not reconstructed or presented as locally re-audited.

A runtime reference frame is represented by its admitted equality. A comparison becomes `GeomEquiv` only when it preserves and reflects both frames' equalities:

```text
x ~_F y  ↔  T(x) ~_G T(y).
```

Resolution and openness are frame-relative:

```text
ResolvedIn(F,Q)  ↔  Q factors through F's equality quotient
OpenIn(F,Q)      ↔  Q separates an explicit pair that F equates.
```

Non-selection, missing comparison data, rejection, and pending verification are not `OpenIn`. `W` returns relational content, not a TRUE/FALSE/OPEN value.

## Choice, admission, and transformation cost

A potential gate is not treated as a closed entropy barrier. It is a **truth-condition interface on a choice**:

```text
choice
  → proposed translation
  → independent return / consequence
  → naturality / recovery / reflection audit
  → admitted continuation | obstruction | OPEN.
```

Naturality constrains a chosen interaction after the choice; it does not preselect the choice. A self-certified receipt or an outcome derived from the gate verdict cannot make admission true. The native Level-1 and Level-2 controls enforce this distinction by separating structural translation, independent calibration, and held-out external consequences.

The requested **universal transformation cost** is likewise not identified with entropy or the bounded sorting-cost fixture. Its target is the transformation burden of relational identity itself, independent of language or definition basis. Any eventual cost must factor through translational identity:

```text
presentation-level transformation
    → closure/translational identity class
    → invariant transformation cost.
```

The repository does not yet claim a universal scalar formula. Current runtimes retain proof-relevant constituents—residue, obligations, failures, return requirements, abstentions, and external-audit burden—from which such an invariant may later be derived.

See [`TRUTH_CONDITION_TRANSLATIONAL_CLOSURE.md`](TRUTH_CONDITION_TRANSLATIONAL_CLOSURE.md).

## Existing self-contained verification

The repository already contains executed bounded verification rather than only a proposed implementation.

Its supplied-frame causal order is:

```text
assumed local axiom geometry
    ≺ internal audit and frozen equality/questions
    ≺ raw candidate (T,phi,pi)
    ≺ GeomEquiv
    ≺ admitted translation
    ≺ W/E/J/C + operation naturality
    ≺ ResolvedIn / OpenIn
    ≺ held-out transfer / next basis.
```

The completed suite includes:

- isolated classical mathematical-agent proxies;
- a strong ordinary proof/isomorphism baseline on identical frozen inputs;
- external axiom-geometry interaction with typed relational lineage;
- generative axiom-geometry isolation with post-freeze candidate search;
- a pre-quotient maze assay deriving completed reach, exact equality realization, saturation topology, `LocalIVI_W`, return monodromy, and receipt-after-resolution from explicit return paths;
- recovery-versus-translation and developmental-bridge controls;
- Level-1 independent receipt calibration and Level-2 held-out external-consequence controls;
- a bounded closure-native axiometric-evolution cycle in which completion generates successor frames used by later changed-axiom interactions;
- explicit equality-collapse, operation-twist, cardinality, non-isomorphism, pending, leakage, self-certification, and interface-boundary controls;
- deterministic evidence replay and Lean/experiment CI.

The strong classical baseline accepts genuine ordinary isomorphisms, including noncanonical orientation changes. The translational arm does not claim classical mathematics is incapable of expressing closure; it adds explicit frame-equality, preservation/reflection, naturality, quotient-question, obstruction, lineage, and transfer certificates.

The bounded generative lane enumerates 1,440 post-freeze forms and admits six fully natural translations corresponding to the six ordinary isomorphisms retained independently by the classical baseline. Preserved raw D4/S3 and D4/Q8 controls expose cardinality and operation-level obstructions without normalizing the frames into compatibility.

The bounded maze lane separately begins before quotient resolution while retaining a supplied Setoid-like frame equality. Six return lines complete the registered reach relation into the exact frozen fibres, while the classical Floyd-Warshall/SCC baseline reproduces the same finite relation counts. The differential is explicit closure lineage, not computational impossibility for classical mathematics.

The bounded closure-native evolution lane executes

```text
F0 → interaction → completion → derived F1
   → changed-axiom interaction → completion → derived F2.
```

Successor frames are generated from completion digests, preserve many→one→many lineage, and retain missing/leaked external-outcome controls. This is the first native bounded control of the longitudinal closure grammar; it is not a universal theorem or an Aristotle Phase C2 result.

## Current Aristotle frontier evidence

The preregistered frontier experiment has progressed beyond proposal-only status.

Executed stages include:

- **Phase A:** two isolated Aristotle-generated local frames from one neutral packet;
- **Phase B:** a third isolated native translation artifact with explicit `MAPPED`, `AMBIGUOUS`, and `UNMAPPED` entries;
- **Phase B2:** identity-independent validation, with 34 mapped roles passing and a concrete frame-structure obstruction retained;
- **Phase B3:** candidate equality accepted only on the frozen 34-role subinterface, with whole-frame equality and `GeomEquiv` blocked;
- **Phase C1:** independently generated local return evidence over exactly the admitted roles, without promotion to assembled cross-frame return, completion, IVI, topology, receipts, or transfer.

The next open frontier step is to test whether the independently generated local returns assemble into translational completion and recoverability while preserving the frozen obstruction and every earlier abstention.

## The ASI verification target

The proposed verifier has **two complementary formal layers**:

```text
Layer 1 — local formal verification
F_A ⊢ P_A
F_B ⊢ P_B
```

Lean/kernel verification establishes correctness relative to each frame's own formal assumptions.

```text
Layer 2 — cross-frame translational verification
F_A ↔[T,phi,pi] F_B
```

The second layer asks whether independently constituted frames admit a relational comparison preserving/reflection their own equalities and satisfying registered naturality obligations. The closure-native extension then asks whether completed translation can generate the next axiometric frame rather than merely compare two supplied frames.

The project therefore extends rather than replaces trusted-kernel verification. The ASI problem is not that Lean ceases to verify local proofs; it is that a sufficiently capable mathematical agent may alter the language, axioms, geometry, equality, orientation, and representation in which later mathematics is constituted. Translational axiometry asks what truth-level relation can remain verifiable **between and through** those changing formal frames.

## What the grant funds

The grant funds three coupled activities.

### 1. Frontier Aristotle completion experiment

Continue the frozen native-translation protocol through assembled return, translational completion, local/cross-frame IVI, topology/receipt checks, and held-out mathematical transfer without repairing any earlier artifact.

```text
Aristotle A → F_A → audit → freeze
Aristotle B → F_B → audit → freeze
                    ↓
          frozen native translation T_AB
                    ↓
     primitive/held-out validation + recovery
                    ↓
          candidate equality on admitted interface
                    ↓
         independent return generation
                    ↓
 completion + local/cross-frame IVI + topology/receipts/transfer
```

A natural translation, explicit equality obstruction, downstream naturality obstruction, genuine frame-relative `OpenIn`, or registered interface boundary are all substantive outcomes.

The next direct step is narrower than structural reconstruction: independently
preregister an answer-level correspondence and non-local return for the frozen
packet, then evaluate its registered relational answers. C2 remains a
structural-interface result and T1 an open truth boundary; neither may be
relabelled as a truth verdict. If an admitted truth relation retains residue,
form depth may nominate a candidate next question, but independent warrant and
provenance—not the current verifier or a desired answer—must admit it.

### 2. Closure-native axiometric evolution and Lean formalization

Use completed frontier relations to test the stronger longitudinal claim:

```text
F_t
  → choice / interaction
  → translation + independent return
  → completion
  → derived F_(t+1)
  → changed-axiom next interaction.
```

Every proposed succession must pass two separate checks:

```text
valid succession = truth completion for the frozen registered language
                    AND independently replayable published lineage.
```

The successor verifier may verify at its new level but cannot serve as the
evidence that validates its own external succession. Transformation cost is
recorded separately from truth: a costly translation may still be truthful and
an inexpensive one may still fail.

Frontier-generated structures and obstructions feed back into the formal theory. The formal work will generalize interfaces exposed by frontier frames, characterize minimal conditions for valid translation and further relation, prove obstruction theorems when comparison fails, and develop the language/definition-invariant transformation-cost target only where the mathematics warrants it.

### 3. Verification evaluation against strong classical controls

Every frontier experiment retains the ordinary proof/isomorphism baseline on the same frozen artifacts and compute budget. The translational architecture earns added value only if its explicit cross-frame lineage, obstruction localization, frame-qualified resolution/openness, longitudinal frame derivation, or downstream transfer provides information not already recovered as cheaply by the strong classical baseline.

## Five deliverables

1. **Qualifying Aristotle-generated frames and frozen provenance.** Independently generated and internally audited axiom-geometries frozen before cross-frame disclosure.
2. **Natural translational comparisons or precise obstructions.** Native translations, equality/subinterface certificates, return evidence, and explicit failure boundaries without canonical normalization.
3. **Completion, question succession, and truth-level continuation evidence.** Assembled independent returns, answer-level truth evaluation, independently warranted residue/form-depth question admission, local/cross-frame IVI, topology/receipts, and held-out mathematical transfer where the data support them.
4. **Frontier-driven Lean extensions.** Machine-checked generalizations or obstruction theorems motivated by actual Aristotle-generated frames, including closure-native evolution rather than only supplied-frame covariance.
5. **Strong comparative evaluation.** Ordinary proof/isomorphism baselines, adversarial transformations, evidence size/runtime accounting, anti-leakage controls, and tests for hidden canonical normalization.

## Success and falsification

Success does not mean every axiom-geometry translates to every other axiom-geometry.

Positive evidence is an independently generated relation whose native translation survives identity-independent validation, whose return is independently generated, and whose completion supports a further auditable relation without collapsing the frames into one privileged presentation.

Negative evidence is an explicit obstruction identifying where equality equivalence, return, completion, external consequence, or downstream naturality fails.

Frame-relative openness is substantive only when a precommitted total question separates occurrences admitted equal by its named frame. Missing or incomplete evidence remains pending or OPEN under its registered condition rather than being converted into closure.

The architecture is challenged if increasingly autonomous frames can only be compared by forcing them into one privileged coordinate system; if equality or questions must be rewritten after candidate disclosure; if a gate or completion certifies its own external consequence; if closure reduces to frozen recovery with no movement into a further relation; or if the strong classical baseline consistently recovers the same cross-frame evidence with equal or lower cost.

## Why this matters for mathematical superintelligence

A mathematical superintelligence may eventually generate formal mathematics whose internal organization was not anticipated by its verifier. Requiring such mathematics to retain today's representation risks turning verification into a representational capability ceiling.

The proposed research asks whether a stronger principle is viable:

> **Assume each novel mathematical frame conditionally in its own unified axiom-geometry; verify it locally with a trusted kernel; then test what truth-level relational identity exists through natural choice, translation, independent return, and completion—without treating any local presentation as the absolute definition of truth.**

The repository already supplies machine-checked conditional theory, bounded executable verification, native closure-cycle controls, and live Aristotle-generated frontier evidence. The grant supplies the regime required to test, falsify, and further formalize that architecture under substantially greater representational freedom.
