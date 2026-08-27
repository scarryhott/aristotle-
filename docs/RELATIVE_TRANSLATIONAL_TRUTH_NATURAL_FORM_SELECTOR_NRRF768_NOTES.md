# NRRF768 — Relative translational truth natural-form selector

NRRF768 closes a real gap in the local formal chain. The earlier modules had
return equality, relative translation, polar reversal, a curvature map, trading
problems, continual histories, and public-paper receipt boundaries. They did
not have the operator that chooses one presentation of every returned identity
and carries that whole choice naturally between relative frames.

The construction assumes no profit maximizer and manufactures no
representative by quotienting. A supplied context could carry its own later
empirical rule; no such rule is derived or privileged here. The formal order
is:

```text
preselection return equality
  → authored/contextual natural form
  → relative-translation/naturality audit
  → interaction and local completion witness
  → empirical assessment
  → further contextual choice.
```

## What was missing

In NRRF627,

```text
CEq W x y  :=  W x = W y.
```

`TransFrame.C` was only required to be idempotent, invisible to `W`, and
natural under translation. It was not required to select exactly one member of
every `CEq` class. This distinction is non-vacuous: `standardFrame.C` and
`flipFrame.C` are the identity even though their separated `0` and `∞`
presentations are different occurrences with the same return.

The provisional natural-form note outside the built Lean roots described a
section, but did not prove its covariance, its topological reading, its
relative freedom, or its connection to trading. NRRF768 supplies those laws in
the current build instead of assuming the reported NRRF760/761 modules, which
are not present in this checkout.

## Completion and topological identity

For a return `W : X → B`, NRRF768 constructs

```text
closureSetoid W        with x ~ y iff W x = W y
Completion W           = X / ~
completionReturn W     : Completion W → B.
```

For every NRRF627 frame language, `completionEquiv` proves

```text
Completion (A.W l) ≃ B l.
```

This uses the already supplied presentation `A.E l 0 b`; it does not use
`Classical.choice`.

Relative occurrence translation descends through that equality as

```text
completionMap A l m : Completion (A.W l) → Completion (A.W m).
```

`completionTranslationEquiv`, `completionMap_id`, and `completionMap_comp`
prove that these maps are reversible and coherent. The whole completion square
commutes:

```text
completionEquiv A m ∘ completionMap A l m
  = A.phi l m ∘ completionEquiv A l.
```

The module also derives an actual equality-saturation `TopologicalSpace`. A set
is open exactly when it cannot split a return-equality class:

```text
IsOpen U  iff
  ∀ x y, W x = W y → (x ∈ U ↔ y ∈ U).
```

`ceq_iff_same_open_neighborhoods` then proves the exact topological identity:

```text
W x = W y
  ↔ every derived open contains x exactly when it contains y.
```

The quotient and topology are downstream representations of the prior return
relation; neither is installed as an unexplained primitive.
`translation_continuous` and `translationHomeomorph` additionally prove that
every relative occurrence translation is a homeomorphism between these derived
topologies. Thus the equality, its completion, and its topological identity all
translate through the same frame relation.

## The natural-form selector

`NaturalFormSelector A` is a supplied family

```text
F.select : ∀ l, B l → Y l
```

with the two equations

```text
A.W l (F.select l b) = b

A.T l m (F.select l b)
  = F.select m (A.phi l m b).
```

The first says that the form is a section of completion. The second says that
translating the language/perspective while holding the authored context fixed
carries the selected presentation; it does not run a new external chooser.

Its representative operator is

```text
H_F(l,x) = F.select l (A.W l x).
```

NRRF768 proves

```text
A.W l (H_F(l,x)) = A.W l x
H_F(l,H_F(l,x)) = H_F(l,x)
H_F(l,x) = H_F(l,y)  ↔  CEq (A.W l) x y
A.T l m (H_F(l,x)) = H_F(m,A.T l m x).
```

Thus `H_F` is stronger than the old unconstrained `C`: it chooses one form
through each class, is exact on those classes, and translates naturally.
`NaturalFormSelector.toRestructuring` places it back inside the existing
NRRF627 interface.

## Relative authorship and freedom

`RelativeFormSeed` supplies a temporary origin and a pointwise authored pole:

```text
s.origin : L
s.pole   : B s.origin → Pole.
```

At another language and identity its orientation is

```text
orientationAt(s,l,b)
  = A.pi s.origin l (s.pole (A.phi l s.origin b)),
```

and its selected presentation is

```text
F_s(l,b) = A.E l (orientationAt(s,l,b)) b.
```

The pointwise function matters: different returned identities may choose
different poles. `selectorOfSeed_translateOrigin` and
`translateOrigin_cancel` prove that moving the temporary origin transports the
same form rather than privileging a new origin.

Freedom is explicit and proof-relevant. Reversing a seed gives a different
selector in a separated frame, while the two choices remain `CEq`-equal and
topologically indistinguishable. NRRF768 does not claim that every two
arbitrary forms are connected by a unique movement; such a claim requires a
separate witness of transitivity or torsorial action.

That witness now has a precise type. `NaturalFormMovement F G` supplies an
invertible, return-preserving internal translation which commutes with every
language translation and carries every representative selected by `F` to the
one selected by `G`. Witnessed identity, composition, and reversal operations
are defined, and `reversalMovement` realizes polar reversal. No groupoid laws,
universal or unique torsor, or movement between arbitrary forms are assumed.

`ContextualNaturalForms` makes the philosophical ordering literal: context
supplies the seed first, and `selectorAt_natural` audits the resulting choice.
There is no default context, canonical selector, scalar cost, or optimizer in
the structure.

`ContextualSelectorMove` relates two contexts only when such a form movement is
supplied. `ContextualNaturalFormLoop` then reuses the project's sensor/selection
loop but requires a witnessed contextual movement at every actual step;
`run_carries_selection` proves that continual choices form one translated
trajectory. The sensor and update rule remain authored inputs. In particular,
closure does not derive the runtime policy “numeric HOLD reverses; OPEN
retains.”

## Trading bridge

`SelectedTradingFormWitness F P` connects an already selected form to the
existing trading problem. It still requires:

- an actual admissible network interaction;
- local preservation of the interface completion;
- agreement of the selected form with the actual source quote before the
  interaction;
- an explicit interaction-equivariance witness carrying that selected source
  form to the translated source reading;
- translation of that reading to the target reading; and
- agreement of the selected form with the target quote presentation.

`selected_frame_closes` derives the NRRF627 occurrence equation from the
source selection, its explicit interaction transport, selector naturality, and
the actual target. `toLocalTradeWitness` supplies NRRF766's stage-local
`ClosesAt` witness. It does not by itself create a receipt admission or append
a history stage.

Selection alone does not produce a local witness, a future observation, an
authenticated fill, a settled result, or profit.

## Important consequence for profit

`verdict_cannot_distinguish_forms` proves that any verdict declared to respect
closure must agree on two natural forms over the same returned identity.
Therefore empirical P&L cannot both vary between those forms and be treated as
a function only of that closure identity. If prices make the two orientations
perform differently, P&L is downstream frame/interaction data. Moving it
requires a later market interaction or a different completed relation, not
merely relabelling a representative inside one class.

## Machine-checked boundary

The registered module is
`lean/NRRF768RelativeTranslationalTruthNaturalFormSelector.lean`.

It builds with warnings treated as errors, contains no `sorry`, uses no
`Classical.choice`, and its printed theorem dependencies are limited to the
standard axioms `propext` and `Quot.sound`.
