# Approximate external Gram bundle format v1

`approximate-gram-format-v1` is an untrusted preprocessing format for numerical
Gram-PEP artifacts. It is separate from both existing exact formats:

- scalar `external-format-v1` remains unchanged;
- general-dimensional `external-gram-format-v1` remains unchanged.

The preprocessing tool emits two ordinary exact Gram bundles and sends both
through the existing strict exact Gram importer and Lean auditor.

## Two distinct tracks

For every candidate quantity supplied by the source:

1. **raw exact interpretation** converts the original finite base-10 string to
   the exact rational it denotes, without tolerance, repair, or rounding;
2. **reconstructed candidate** applies the recorded deterministic rational
   reconstruction policy and produces a separate exact candidate.

A reconstructed bundle being accepted never means that the raw numerical
artifact was accepted.

## Decimal grammar

Every mathematical scalar must be a JSON string, for example:

```json
"0.3333333333"
"-2.5e-1"
"1"
```

The parser accepts finite base-10 decimal and scientific notation strings. It
rejects:

- JSON native numbers and floats;
- `NaN`, `Infinity`, and variants;
- surrounding whitespace;
- duplicate keys; and
- unknown fields.

Parsing uses `Decimal` and `Fraction` and never passes through a binary Python
float.

Discrete metadata remains discrete: counts and typed indices are JSON integers,
and ordering labels and assumption names are strings.

## Top-level object

```json
{
  "schema_version": 1,
  "source": "one-step near-exact Gram-PEP decimal artifact",
  "declared": { ... integer counts ... },
  "ordering": { ... labels ... },
  "policy": {
    "method": "limit_denominator",
    "max_denominator": 1000,
    "max_abs_error": "2e-10"
  },
  "expect": {
    "raw": "rejected",
    "reconstructed": "accepted"
  },
  "model": { ... decimal strings ... },
  "primal": { ... decimal strings ... },
  "upper": { ... decimal strings ... }
}
```

`expect` is optional and supports `accepted`, `rejected`, or `unchecked` for
each track. It controls generated regression theorems only; it never changes a
candidate.

## Covered quantities

Every rational-valued field of `external-gram-format-v1` becomes a decimal
string in this approximate format, including:

- symbolic point-position and gradient coefficients;
- every affine assumption coefficient;
- every primal Gram entry and function value;
- every primal factor weight and vector coordinate;
- the upper bound and objective coefficients;
- every interpolation and assumption multiplier;
- every dual-matrix entry; and
- every dual-factor weight and vector coordinate.

Ordering arrays, declared counts, assumption names, interpolation point indices,
and assumption indices are preserved exactly as discrete source metadata.

## Reconstruction policy

The current method is:

```text
limit_denominator
```

with explicit:

- `max_denominator`;
- `max_abs_error`.

For each source entry the report records:

```text
path
source string
source exact rational
reconstructed rational
signed delta
absolute error
changed flag
```

Generation fails if any reconstructed denominator or absolute error violates
the policy. There is no silent repair.

## Generated artifacts

For the included example the tool emits:

```text
data/fixtures/gram_generated/one_step_near_exact_raw.json
data/fixtures/gram_generated/one_step_near_exact_reconstructed.json
data/fixtures/gram_generated/one_step_near_exact_reconstruction_report.json
data/fixtures/gram_generated/one_step_near_exact_comparison_manifest.json
LeanPEP/Imported/GramOneStepApproxRaw.lean
LeanPEP/Imported/GramOneStepApproxReconstructed.lean
LeanPEP/Imported/GramOneStepApproxComparison.lean
```

The two JSON bundles conform exactly to `external-gram-format-v1`; neither
contains the policy or reconstruction report. `import_exact_gram_bundle.py`
remains the only JSON-to-Lean route for both tracks.

The manifest records canonical SHA-256 values for:

- the approximate source;
- the raw exact bundle;
- the reconstructed exact bundle;
- the reconstruction report; and
- the comparison manifest itself in the generated Lean provenance object.

The hashes bind provenance but do not replace mathematical checking.

## Included near-exact example

The source preserves exact rank-one factorizations for its raw primal and dual
matrices, so raw rejection is not caused by a floating-point eigenvalue test.
Under exact decimal semantics the raw candidate has three strictly negative
ordered interpolation slacks:

```text
(0,1): -8888888889 / 200000000000000000000
(0,2): -26666666667 / 200000000000000000000
(1,2): -8888888889 / 100000000000000000000
```

Its primal objective also exceeds its raw bound by exactly:

```text
1 / 10000000000
```

The recorded reconstruction recovers the accepted exact one-step `1/6` Gram
bundle. This proves facts only about the reconstructed exact object.

## Trust boundary

Untrusted or low-trust components include:

- the numerical solver;
- decimal serialization;
- rational reconstruction;
- this Python parser and code generator.

Lean independently rechecks, for each track:

- metadata and ordering lengths;
- model realization;
- primal Gram PSD factorization;
- all ordered scalar interpolation constraints;
- formulation assumptions;
- the complete upper certificate and dual PSD factorization; and
- exact primal attainment of the certified bound.

The result remains a finite Gram-PEP conclusion. It does not yet provide the
general smooth-convex interpolation theorem or validate a concrete PEPit model
translation.
