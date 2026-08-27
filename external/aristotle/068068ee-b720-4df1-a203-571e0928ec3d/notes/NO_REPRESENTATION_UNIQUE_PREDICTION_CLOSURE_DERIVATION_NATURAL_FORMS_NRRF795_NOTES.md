# NRRF795 — No representation is needed: the unique prediction *is* the closure derivation of the natural forms

Module: `NRRF795NoRepresentationUniquePredictionClosureDerivationNaturalForms.lean`
(registered in `lakefile.toml`; builds with no `sorry` and with a machine-checked axiom audit at
the end of the file).

## The correction

> We don't need a representation; instead the unique prediction is precisely the closure
> derivation of natural forms.

Two claims are packed into that sentence, and both are proved here as statements about the
finite-dimensional model of local relations already used in NRRF683 / NRRF791 / NRRF793:

1. the closure derivation of the natural forms is **unique** — so it is a prediction, not one
   option among several;
2. a **representation** — a faithful linear encoding of the relations into some carrier, with the
   readings performed downstream of it — changes nothing about the prediction, and is itself not
   fixed by the prediction. It is surplus.

## §1  The derivation, bundled, and unique

`ClosureDerivation` bundles exactly the closure conditions, nothing else:

* a linear scalar reading `scale` that is blind to the order in which two translations compose
  (`scale (A * B) = scale (B * A)`) and is normalised on the identity relation (`scale 1 = 3`);
* a linear vector reading `hairRead` that returns nothing on the return-symmetric sector and reads
  a ball direction faithfully (`hairRead (axialMat v) = 2 v`).

No sector, form or coordinate is posited in the structure. Then:

* `closureDerivation_exists` — the closure performs one: `theDerivation`, whose readings are the
  divergence `divgLin` and the curl `curlLin`;
* `ClosureDerivation.scale_eq`, `ClosureDerivation.hairRead_eq` — the readings of *any* closure
  derivation are the divergence and the curl (via the forcing theorems of NRRF793);
* `closureDerivation_unique` (and the `Subsingleton` instance) — there is exactly one such object;
* `unique_prediction` — stated without the bundle: there is a **unique** pair of linear readings
  satisfying the four closure conditions, namely `(divg, curl)`.

So the derivation of the natural forms is not a modelling choice; it is the single admissible
outcome of the closure conditions.

## §2  Representations: transparent, and undetermined

`Representation W` is a faithful linear encoding `LocalRel →ₗ[ℝ] W`. `RepDerivation W` performs
the readings on the carrier `W`, imposing the same four closure conditions downstream of the
encoding.

* `RepDerivation.toClosureDerivation` — every representation-mediated derivation collapses to a
  bare one, by composition with the encoding;
* `repDerivation_scale_eq`, `repDerivation_hairRead_eq` — whatever the carrier and whatever the
  encoding, the readings obtained are again the divergence and the curl;
* `prediction_representation_independent` — two derivations through arbitrary representations over
  arbitrary carriers agree on every relation;
* `idRepDerivation` — the representation-free reading is not excluded: it is the identity encoding;
* `Representation.rescale`, `doubleRepDerivation`, `representation_underdetermined` — two
  *distinct* faithful encodings (`id` and `2 · id`, with the readings renormalised) make exactly
  the same prediction on every relation, so the prediction does not fix the representation;
* `representation_surplus_carrier` — a strictly larger carrier (`LocalRel × ℝ`) also carries a
  representation-mediated derivation returning the same forms; the extra room is never read.

The representation is therefore structure the prediction cannot see, and which the prediction
cannot pin down: it is not what the closure predicts.

## §3  Nothing is lost by dropping it

* `state_from_natural_forms` — a relation is reassembled from its own forms and its residue:
  `(divg A / 3) • 1 + axialMat (hair A) + shearPart A = A`, with no encoding in the statement;
* `state_determined_by_forms` — equal scale reading, equal hair reading and equal residue force
  equality of the relations;
* `forms_realizable` — every pair (scale value, ball direction) is the pair of readings of an
  actual relation, so the prediction is not bought by sparse readings;
* `residue_is_neutral` — what the two readings miss is exactly the neutral (shear) sector, and by
  `NRRF791.neutral_nontrivial` that sector is nonzero: the prediction is honestly bounded, not
  total.

`nrrf795_answer` collects all of these clauses into one theorem.

## What is *not* claimed

* "Representation" here means exactly the faithful linear encoding defined in §2 of the module. No
  claim is made about representation theory in any other sense, nor about any external physical
  proposal.
* "Unique" and "forced" always mean: unique relative to the closure conditions written into the
  structures — order-blindness with normalisation, return-blindness with ball-normalisation.
* All results are statements about this finite-dimensional model of local relations, not about any
  physical device or measurement.
