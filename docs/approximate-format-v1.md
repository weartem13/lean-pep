# Lean-PEP approximate bundle format, schema v1

This format is an untrusted numerical entry point layered in front of the
unchanged exact bundle schema documented in `external-format-v1.md`.

Its purpose is to keep two mathematically different statements separate:

1. **raw exact audit** — audit the solver's finite base-10 strings exactly,
   without tolerance, repair, or silent rounding; and
2. **reconstructed candidate audit** — apply a recorded deterministic rational
   reconstruction policy, then audit that new exact candidate.

Acceptance of the reconstructed candidate does not mean that the raw numerical
candidate was accepted.

## Numeric representation

Every candidate decimal is a JSON string:

```json
"0.1999999998"
"2e-1"
"-3.125E-1"
```

The grammar accepts ordinary finite base-10 notation and scientific notation.
It rejects:

- JSON native numbers such as `0.2`;
- `NaN`, `Infinity`, and `-Infinity`;
- surrounding whitespace; and
- malformed decimal strings.

Python parses the strings through `Decimal` and converts them directly to
`Fraction`. It never passes through a binary `float`. For example,
`"0.1999999998"` is interpreted exactly as
`999999999 / 5000000000`.

Integer metadata and point indices remain JSON integers. Only candidate
quantities that denote rationals are decimal strings.

## Top-level object

```json
{
  "schema_version": 1,
  "source": "solver run identifier",
  "steps": 2,
  "declared_point_count": 4,
  "declared_constraint_count": 16,
  "expect": {
    "raw": "rejected",
    "reconstructed": "accepted"
  },
  "policy": {
    "method": "limit_denominator",
    "max_denominator": 1000,
    "max_abs_error": "5e-10"
  },
  "primal": { ... },
  "upper": { ... }
}
```

Required fields are:

- `schema_version`: exactly `1`;
- `source`: nonempty provenance label;
- `steps`, `declared_point_count`, and `declared_constraint_count`: the same
  metadata carried by exact schema v1;
- `policy`: reconstruction method and exact bounds;
- `primal`: approximate gradient and value arrays; and
- `upper`: approximate generic upper certificate.

`expect` is optional regression metadata. Each track may be `accepted`,
`rejected`, or `unchecked`. It never determines mathematical acceptance; the
Lean checker does.

Unknown and duplicate fields are rejected.

## Primal and upper-certificate shape

The object shape, vector lengths, point syntax, index bounds, and ordered
certificate terms are identical to exact schema v1. The only difference is that
rational leaves are decimal strings instead of `{ "num", "den" }` objects.

Example primal data:

```json
"primal": {
  "grad": ["2e-1", "0.2", "0.2000000000"],
  "value": ["1.799999998e-1", "0.14", "1e-1"]
}
```

Example upper term:

```json
{
  "weight": "0.4166666667",
  "i": { "kind": "star" },
  "j": { "kind": "iter", "index": 1 }
}
```

Positions are still not imported. Lean generates
`x_k = 1 - sum_{t < k} g_t` from the normalized finite-GD semantics.

## Reconstruction policy

Schema v1 supports one method:

```json
{
  "method": "limit_denominator",
  "max_denominator": 1000,
  "max_abs_error": "5e-10"
}
```

For each candidate rational `q`, the preparer computes Python
`Fraction.limit_denominator(max_denominator)`. The result is emitted only when:

- its denominator is at most `max_denominator`; and
- its exact absolute difference from `q` is at most `max_abs_error`.

If any entry violates the error policy, generation fails. There is no silent
fallback, tolerance widening, or partial repair.

## Generated artifacts

`tools/prepare_approx_bundle.py` emits five deterministic artifacts:

1. a **raw exact schema-v1 bundle** containing the exact rational values of the
   source strings;
2. a **reconstructed exact schema-v1 bundle** containing the policy output;
3. a **reconstruction report JSON**;
4. a **comparison manifest JSON**; and
5. a small **Lean comparison module** that runs the existing exact auditor on
   both bundles.

The two exact JSON files contain no approximate-format extension and are sent
through the existing `tools/import_exact_bundle.py` path.

## Reconstruction report

Every candidate rational produces one report entry with:

- `path`: deterministic JSON path;
- `source`: the original decimal string;
- `source_exact`: its exact rational interpretation;
- `reconstructed`: the proposed exact rational;
- `delta`: reconstructed minus source-exact;
- `absolute_error`: exact nonnegative residual; and
- `changed`: whether reconstruction altered the exact value.

The report also records the policy, entry counts, and SHA-256 hashes of:

- the canonical approximate source;
- the raw exact JSON; and
- the reconstructed exact JSON.

The comparison manifest additionally records the reconstruction-report hash.
The generated Lean comparison module embeds all of those hashes plus the
comparison-manifest hash. Hashes establish artifact provenance; they are not a
substitute for Lean's mathematical checks.

## Example command

From the project root:

```bash
python3 tools/prepare_approx_bundle.py \
  data/fixtures/approximate/two_step_near_exact.json \
  --raw-exact data/fixtures/generated/two_step_near_exact_raw.json \
  --reconstructed-exact data/fixtures/generated/two_step_near_exact_reconstructed.json \
  --report data/fixtures/generated/two_step_near_exact_reconstruction_report.json \
  --manifest data/fixtures/generated/two_step_near_exact_comparison_manifest.json \
  --comparison-lean LeanPEP/Imported/TwoStepApproxComparison.lean \
  --raw-namespace LeanPEP.Imported.TwoStepApproxRaw \
  --reconstructed-namespace LeanPEP.Imported.TwoStepApproxReconstructed \
  --comparison-namespace LeanPEP.Imported.TwoStepApproxComparison
```

Use `--check` to verify that all five outputs are current without rewriting
them. `tools/regenerate_imported_examples.sh` runs the complete approximate and
exact generation pipeline.

## Trust boundary

The approximate parser, rational reconstructor, report generator, and exact
JSON-to-Lean generator are untrusted preprocessing tools. They may fail, reject
a valid input, mistranslate provenance, or produce an exact candidate that Lean
rejects.

They do not extend the trusted mathematical kernel. The raw and reconstructed
tracks both terminate in the existing Lean components:

- exact rational finite-PEP semantics;
- exact primal checker and violation report;
- exact upper-certificate checker;
- exact objective equality check; and
- rational-to-real soundness bridge.

A raw rejection reports a defect in that exact candidate only. A reconstructed
acceptance proves facts about the reconstructed exact bundle only. Neither fact,
by itself, establishes a theorem-level statement about all smooth convex
functions.
