# Lean-PEP exact external bundle format, schema v1

This format transports a complete finite-gradient-descent PEP lower/upper
candidate into Lean. It is intentionally narrow: every numeric field is an
exact rational, the trajectory is one-dimensional, and the upper certificate
uses the generic affine-square syntax already verified by Lean.

## Trust model

The Python converter is not trusted as a theorem prover. It performs strict
shape and index validation, then emits ordinary Lean definitions. Lean checks
the generated module again through:

1. metadata and declared count auditing;
2. exact primal interpolation checking;
3. exact generic upper-certificate checking; and
4. exact equality of the primal objective and the certified bound.

A converter defect can therefore cause generation failure or Lean rejection,
but it cannot make an invalid certificate satisfy the Lean theorems.

## Exact rationals

Every rational is an object:

```json
{ "num": -5, "den": 16 }
```

Requirements:

- `num` is a JSON integer;
- `den` is a positive JSON integer;
- JSON floating-point numbers are rejected, even when they look integral;
- the converter reduces the fraction before emitting Lean syntax.

Solver floating-point output must first undergo rational reconstruction. The
reconstructed candidate is then checked exactly by Lean.

## Top-level object

```json
{
  "schema_version": 1,
  "source": "human-readable provenance",
  "steps": 2,
  "declared_point_count": 4,
  "declared_constraint_count": 16,
  "expect": "accepted",
  "primal": { ... },
  "upper": { ... }
}
```

Fields:

- `schema_version`: must equal `1`;
- `source`: provenance label, stored in generated metadata;
- `steps`: the finite trajectory length `N`;
- `declared_point_count`: externally declared count, expected to be `N + 2`;
- `declared_constraint_count`: externally declared ordered scalar constraint
  count, expected to be `(N + 2)^2`;
- `expect`: optional; `accepted`, `rejected`, or `unchecked`; this controls
  whether the generated module contains a `native_decide` regression theorem;
- `primal`: exact sampled gradients and function values;
- `upper`: exact generic upper certificate.

Unknown and duplicate fields are rejected. Incorrect declared counts are not
silently repaired: they are emitted and rejected by Lean's metadata audit.

## Primal data

```json
"primal": {
  "grad": [q0, q1, ..., qN],
  "value": [f0, f1, ..., fN]
}
```

Both arrays must have exactly `N + 1` entries. Positions are not imported. Lean
generates them from the normalized gradient-descent semantics:

```text
x_0 = 1,
x_k = 1 - sum_{t < k} g_t.
```

This prevents an external file from supplying positions inconsistent with the
algorithm.

## Points

The optimum is:

```json
{ "kind": "star" }
```

An iterate is:

```json
{ "kind": "iter", "index": 2 }
```

Iterate indices must lie in `0..N`.

## Upper certificate

```json
"upper": {
  "bound": { "num": 1, "den": 10 },
  "objective": 2,
  "interp_terms": [ ... ],
  "square_terms": [ ... ]
}
```

The intended identity is

```text
bound - f_objective
  = sum lambda_ij * slack_ij
  + sum mu_k * affine_k(g)^2.
```

Each interpolation term is:

```json
{
  "weight": { "num": 1, "den": 4 },
  "i": { "kind": "star" },
  "j": { "kind": "iter", "index": 0 }
}
```

Each square term is:

```json
{
  "weight": { "num": 2, "den": 3 },
  "form": {
    "const": { "num": -5, "den": 16 },
    "grad": [
      { "num": 5, "den": 16 },
      { "num": 1, "den": 1 },
      { "num": 1, "den": 4 }
    ]
  }
}
```

The affine form is

```text
const + sum_i grad[i] * g_i.
```

Lean independently verifies nonnegative weights and every coefficient of the
quadratic identity.

## Generation

From the project root:

```bash
python3 tools/import_exact_bundle.py \
  data/fixtures/external/two_step_exact.json \
  LeanPEP/Imported/TwoStepExact.lean \
  --namespace LeanPEP.Imported.TwoStepExact
```

To verify that a committed generated module is current without rewriting it:

```bash
python3 tools/import_exact_bundle.py \
  data/fixtures/external/two_step_exact.json \
  LeanPEP/Imported/TwoStepExact.lean \
  --namespace LeanPEP.Imported.TwoStepExact \
  --check
```

The generated metadata contains a SHA-256 digest of canonicalized source JSON.
The digest is provenance information; mathematical validity still comes from
Lean's exact checks.
