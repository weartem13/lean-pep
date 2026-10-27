# PEPit one-step gradient-descent adapter v1

## Scope

This adapter is intentionally narrow. It recognizes one version-pinned PEPit
formulation:

```text
function class     SmoothConvexFunction(L = 1)
algorithm          x1 = x0 - g0
initial condition  ||x0 - x_star||^2 <= 1
performance        f1 - f_star
steps              1
```

The inspected producer revision is:

```text
PEPit commit 5a061a1b2dbe450b6bac42e2442942748f3b1f32
```

A different PEPit revision, function class, step size, ordering, symbolic
constraint, or objective is rejected by this adapter profile. Supporting a new
profile requires a separately named adapter and new regression artifacts; it
must not silently reuse this profile.

## Source artifact

`pepit-sdp-artifact-v1` records four independent layers.

### Producer provenance

The artifact records the package version, Git commit, wrapper, solver, solver
status, and one of two capture modes:

```text
live_pepit

deterministic_regression_fixture
```

The committed regression fixture is explicitly marked
`deterministic_regression_fixture`. It is not presented as a solver run carried
out in the artifact-building sandbox. `tools/export_pepit_one_step_artifact.py`
provides the optional live exporter; it requires PEPit, NumPy, CVXPY, and a
configured solver environment.

### Exact symbolic formulation snapshot

The source records:

- sampled-point order `[star, x0, x1]`;
- sampled function-value order `[f_star, f0, f1]`;
- PEPit leaf-point order `[x_star, x0, g0, g1]`;
- every sampled point and gradient decomposition in that leaf basis;
- the initial condition and all six non-diagonal ordered smooth-convex
  interpolation constraints as affine coefficients in function values and
  source Gram entries;
- the prepared scalar-constraint order; and
- the objective `f1 - f_star`.

The adapter independently reconstructs the expected formulation and compares
all of these fields. It also recomputes a canonical SHA-256 model fingerprint
from the normalized exact formulation. A declared fingerprint is checked
separately from the recomputed fingerprint.

Starting with v0.11C2, the generated Lean module also contains the exact native
symbolic arrays themselves.  Lean reconstructs the supported formulation from
`LinearExprQ` operations and compares entrywise:

- the `3 × 4` point and gradient decomposition matrices;
- every constraint label, kind, sense, and ordered point pair;
- every constant, sampled-value, and `4 × 4` source Gram coefficient;
- the objective coefficients; and
- the `3 × 4` transform from `[x_star, x0, g0, g1]` to
  `[x0-x_star, g0, g1]`.

Consequently, a matching declared fingerprint string is no longer sufficient
for Lean source acceptance.  The fingerprint remains useful provenance, while
the typed source audit supplies the entrywise formulation check.

### Numerical solver arrays

The source records decimal strings for:

- the PEPit leaf-basis primal Gram matrix;
- sampled function values;
- every scalar dual multiplier;
- the dual residual matrix;
- primal and dual objective values; and
- an explicit rational-reconstruction policy.

Every decimal is parsed through `Decimal` and `Fraction`; there is no binary
float conversion inside the adapter or reconstruction pipeline.

### Factorization hints

PEPit supplies primal and dual matrices, not exact rational PSD factorization
proofs. The source therefore has a separately labelled
`factorization_hints` section. These hints are untrusted numerical
postprocessing. They do not decide formulation-adapter acceptance. The existing
raw and reconstructed exact Gram audits independently check every factor
weight and every target/factorized matrix entry.

The optional live exporter obtains numerical hints by eigendecomposing matrices
after projection to the canonical centered basis. Passing those hints is not
promised: the exact downstream audit is deliberately allowed to reject them.

## Source-to-Lean translation

The PEPit leaf basis is:

```text
[x_star, x0, g0, g1]
```

The target Gram basis is:

```text
[x0 - x_star, g0, g1]
```

The adapter centers every sampled position at `x_star`, transforms the primal
Gram matrix, objective, normalization, dual residual matrix, and factor hints,
and emits an ordinary `approximate-gram-format-v1` artifact. It does not add a
new mathematical checker.

The resulting artifact follows the already verified pipeline:

```text
PEPit source artifact
  -> formulation/order/fingerprint comparison
  -> approximate-gram-format-v1
     -> raw exact external-gram-format-v1
     -> reconstructed external-gram-format-v1
  -> existing ExactGramBundleQ audits
```

Raw and reconstructed tracks retain distinct semantics. Reconstructed
acceptance never validates the raw solver artifact.

## Committed regressions

### Supported source fixture

`data/fixtures/pepit/one_step_gd_solver_artifact.json` uses a nonzero source origin,
so the adapter regression exercises actual centering rather than relying on
`x_star = 0` in the source basis. The formulation audit accepts it. Its raw
exact Gram bundle is rejected, while the deterministic reconstruction recovers
the previously verified one-step exact Gram bundle with value `1/6`.

### Constraint-order mismatch

`data/fixtures/pepit/one_step_gd_bad_constraint_order.json` swaps two ordered
interpolation constraints. It preserves the same numerical matrix/value data,
but the source formulation audit reports:

```text
problem.constraint_order
problem.model_fingerprint.declared
problem.model_fingerprint.computed
```

The adapter therefore rejects the source formulation even though its numerical
payload can still be transformed and inspected.

### Typed symbolic-coefficient mismatch

`data/fixtures/pepit/one_step_gd_bad_symbolic_coefficient.json` preserves the
canonical producer metadata, ordering, and declared model fingerprint, but
changes one source interpolation coefficient from `-1` to `-9/10`.  The adapted
mathematical Gram payload is deliberately unchanged.  Python reports a
recomputed-fingerprint mismatch, while Lean's typed source audit reports the
exact constraint coefficient location and values.  This regression separates
source-provenance checking from downstream certificate checking.

## Trust boundary

Low-trust or untrusted components include:

- PEPit and the SDP solver;
- the live exporter;
- the source JSON parser;
- the basis translator;
- factorization-hint generation;
- rational reconstruction; and
- Lean source generation.

Lean independently checks the generated target model, primal Gram PSD
factorization, every ordered interpolation slack, formulation assumptions,
upper/dual certificate, exact objective attainment, and reconstructed real
soundness theorem.  It also entrywise checks the supported PEPit-native
symbolic source arrays and basis transform.  The exporter and adapter remain
untrusted: the Lean profile is specific to this pinned one-step formulation and
does not prove the correctness of arbitrary PEPit internals or solver output.

## Commands

Regenerate all committed adapter outputs:

```bash
PYTHONDONTWRITEBYTECODE=1 bash tools/regenerate_imported_examples.sh
```

Run the optional live exporter in an environment containing the pinned PEPit
revision and solver dependencies:

```bash
python3 tools/export_pepit_one_step_artifact.py \
  data/fixtures/pepit/live_one_step_gd_solver_artifact.json \
  --wrapper cvxpy \
  --solver CLARABEL \
  --pepit-commit 5a061a1b2dbe450b6bac42e2442942748f3b1f32
```

Then run the adapter and existing Gram pipeline. The committed regeneration
script demonstrates the complete sequence.

Run the dependency-free adapter regressions and the Lean smoke gate:

```bash
python3 -m unittest tools.test_adapt_pepit_one_step -v
lake build LeanPEP
lake env lean tests/lean/smoke/V11ASmokeTest.lean
lake env lean tests/lean/smoke/V11BSmokeTest.lean
lake env lean tests/lean/smoke/V11CSmokeTest.lean
lake env lean tests/lean/smoke/V11C2SmokeTest.lean
```
