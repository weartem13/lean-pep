# Exact external Gram bundle format v1

`external-gram-format-v1` is a strict exact JSON boundary for finite
general-dimensional Gram PEP bundles.  It is independent of the existing
scalar `external-format-v1`; the scalar schema and importer remain unchanged.

The format carries one fixed rational formulation, one exact rational primal
candidate, one primal PSD factor certificate, one general Gram upper
certificate, one dual PSD factor certificate, ordering/provenance metadata,
and an optional expected regression outcome.

The Python importer is not trusted as a prover.  It validates JSON shape and
emits ordinary Lean definitions.  Lean independently checks every mathematical
obligation.

## Exact rational encoding

Every rational is an object with exactly two integer fields:

```json
{ "num": -5, "den": 18 }
```

`den` must be positive.  JSON native floats, decimal numbers, `NaN`, and
infinities are rejected.  Duplicate keys and unknown fields are rejected at
every object boundary.

## Top-level object

```json
{
  "schema_version": 1,
  "source": "one-step exact Gram-PEP bundle",
  "declared": { ... },
  "ordering": { ... },
  "model": { ... },
  "primal": { ... },
  "upper": { ... },
  "expect": "accepted"
}
```

`expect` is optional and may be `accepted`, `rejected`, or `unchecked`.  It
controls only generated regression theorems; it does not alter the bundle.

## Ordering and typed dimensions

```json
"ordering": {
  "points": ["star", "x0", "x1"],
  "gram_basis": ["x0", "g0", "g1"]
}
```

The actual Lean dimensions are derived from these arrays:

- `p = len(points)`;
- `m = len(gram_basis)`.

Both lists must be nonempty, contain nonempty strings, and contain no duplicate
labels.  The labels preserve source provenance.  The mathematical semantics
are determined by the typed `Fin p` and `Fin m` arrays generated from the
bundle.

The Gram-basis ordering refers to the abstract vectors whose inner products
form the primal Gram matrix.  It must not be confused with:

- the array of scalar interpolation slacks;
- the dual PSD matrix;
- an explicit function Hessian such as the Nesterov chain matrix.

## Declared metadata

```json
"declared": {
  "point_count": 3,
  "gram_basis_count": 3,
  "ordered_pair_count": 9,
  "assumption_count": 1,
  "primal_factor_count": 1,
  "upper_interp_term_count": 3,
  "upper_assumption_term_count": 1,
  "dual_factor_count": 3
}
```

Declared counts are intentionally not used to size Lean arrays.  The importer
uses the actual arrays to build typed terms and preserves the declarations for
Lean metadata auditing.  This lets Lean diagnose a source declaration such as
`ordered_pair_count = 8` when the typed model has `3 × 3 = 9` ordered pairs.

Lean also compares the lengths of the point, Gram-basis, and assumption label
orders with the typed formulation.

## Fixed formulation

```json
"model": {
  "position": [ ... p vectors of length m ... ],
  "gradient": [ ... p vectors of length m ... ],
  "assumptions": [
    {
      "name": "initial_radius",
      "expr": {
        "const": { "num": 1, "den": 1 },
        "value_coeff": [ ... p rationals ... ],
        "gram_coeff": [ ... m by m rational matrix ... ]
      }
    }
  ]
}
```

A vector of length `m` is a coefficient expression over the declared Gram
basis.  `position[i]` and `gradient[i]` fix the symbolic sampled position and
gradient for point `i`.

Each assumption is an affine-linear expression

```text
const + Σ_i value_coeff[i] f_i + Σ_ab gram_coeff[a,b] G_ab
```

that must evaluate nonnegatively on the imported primal datum.  Assumption
names are retained in metadata; upper-certificate assumption terms use their
zero-based array indices.

## Primal candidate

```json
"primal": {
  "gram": [ ... m by m exact rational matrix ... ],
  "value": [ ... p exact rational function values ... ],
  "gram_factor": {
    "factors": [
      {
        "weight": { "num": 1, "den": 1 },
        "vector": [ ... m exact rationals ... ]
      }
    ]
  }
}
```

The imported `DataQ` uses the model's exact positions and gradients, together
with the supplied Gram matrix and function values.  Lean nevertheless checks
model/data agreement explicitly, so a hand-written Lean bundle cannot bypass
that obligation.

The factor certificate represents

```text
G = Σ_r weight_r * vector_r * vector_rᵀ,
weight_r ≥ 0.
```

Lean checks target symmetry, every factor weight, and every target/factorized
matrix entry exactly.  No floating-point eigenvalue test is used.

Lean then checks all `p²` ordered smooth-convex interpolation slacks as exact
scalars and every additional model assumption.

## Upper certificate

```json
"upper": {
  "bound": { "num": 1, "den": 6 },
  "objective": { ... affine-linear expression ... },
  "interp_terms": [
    { "weight": { "num": 1, "den": 2 }, "i": 0, "j": 2 }
  ],
  "assumption_terms": [
    { "weight": { "num": 1, "den": 6 }, "index": 0 }
  ],
  "dual_matrix": [ ... m by m exact rational matrix ... ],
  "dual_factor": { "factors": [ ... ] }
}
```

Lean checks:

1. every interpolation multiplier is nonnegative;
2. every assumption multiplier is nonnegative;
3. the dual matrix has an accepted exact PSD factorization; and
4. the coefficient identity

```text
bound - objective
  = Σ interpolation terms
  + Σ assumption terms
  + <dual_matrix, primal_gram>
```

holds at every constant, function-value, and ordered Gram-entry coefficient.

The primal Gram matrix and the dual PSD matrix are distinct objects.

## Closed-loop acceptance

`checkExactGramBundleQ` accepts exactly when all of the following hold:

1. metadata and ordering lengths match the typed bundle;
2. primal sampled positions and gradients realize the model;
3. the primal Gram PSD factor is accepted;
4. every ordered interpolation slack is nonnegative;
5. every formulation assumption is nonnegative;
6. the upper certificate is accepted; and
7. the imported primal objective equals the certified bound exactly.

The real soundness theorem reconstructs:

- realization of the model by the entrywise real cast;
- real `CoreFeasible` primal data, including real PSD from the same exact
  factorization;
- real feasibility of every imported assumption;
- exact primal attainment of the bound; and
- the universal real upper theorem for every real datum satisfying the same
  model, core constraints, and assumptions.

This is a finite Gram-PEP conclusion.  It is not yet the general
smooth-convex interpolation theorem connecting every feasible finite Gram
datum to an actual function.

## Complete audit report

`auditExactGramBundleQ` does not stop at the first failure.  It contains:

- every metadata/count mismatch;
- every model/data position or gradient coefficient mismatch;
- the complete nested primal PSD audit;
- every negative interpolation slack;
- every negative formulation-assumption value;
- the complete structured upper-certificate audit; and
- the exact primal-objective/certified-bound mismatch, if any.

All residuals are exact rationals.

## Import and regeneration

```bash
python3 tools/import_exact_gram_bundle.py \
  data/fixtures/gram_external/one_step_exact.json \
  LeanPEP/Imported/GramOneStepExact.lean \
  --namespace LeanPEP.Imported.GramOneStepExact
```

Regenerate all scalar, approximate, and Gram examples with:

```bash
PYTHONDONTWRITEBYTECODE=1 bash tools/regenerate_imported_examples.sh
```

## Approximate Gram input

The exact schema remains unchanged.  Numerical decimal artifacts use the
separate `approximate-gram-format-v1` preprocessing boundary documented in
`docs/approximate-gram-format-v1.md`.  That pipeline emits one raw exact bundle
and one separately reconstructed exact candidate, then sends both through this
exact importer and the same Lean auditor.
