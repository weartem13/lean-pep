# PG2 certificate consumer

The consumer checks a unit-normalized PG instance with two steps using the source, trace, raw-binding, reconstruction-policy, upper-bound and PSD checks. It then applies the parameterized actual-function bridge. Offline recovery and checking require Python 3.10+ and its standard library; numerical capture is a separate optional operation.

## Recommended entry

From the extracted public source directory, choose a new output location outside that directory:

```sh
OUT=/absolute/path/to/new-lean-pep-run
python3 scripts/setup.py --output "$OUT/setup" --dependencies-only
python3 scripts/verify.py quick --output "$OUT/quick"
```

The setup command validates this distribution's `SOURCE_MANIFEST.json`, toolchain and lockfile. It fetches the nine pinned official dependency revisions and asks the matching Mathlib cache tool for the imports used by the full maintained library, tests and cases. Its `--cache /path/to/packages` alternative delegates pin/clean checks and copying to the consumer. Both require an initially absent project `.lake/build`; neither takes project objects from another checkout. `--fresh-toolchain` installs the locked Lean toolchain in the external output directory. Without that flag an existing installation of the exact locked toolchain may be reused.

The quick entry builds the generic Core and checks `data/cases/pg/two-step-reuse/capture.json` with its supplied `selected_exact.json`. On success the report has `actual_upper_verified=true`, `selected_endpoint=structured`, and `bound=62500/499999`; the generated theorem is `LeanPEP.Imported.Public.PG2.actual_upper`. [Quickstart](quickstart.md) gives the result locations and the full-maintenance command.

## Direct consumer API

For another supported PG2 input, use operator-supplied absolute paths. Every output directory must be new and outside `SOURCE`:

```sh
python3 "$SOURCE/tools/replay_pg_certificate.py" recover --source-root "$SOURCE" --input "$CAPTURE" --output "$RECOVERY" --namespace LeanPEP.Imported.Consumer.PG2
python3 "$SOURCE/tools/replay_pg_certificate.py" verify --source-root "$SOURCE" --input "$CAPTURE" --candidate "$CANDIDATE" --output "$VERIFY" --namespace LeanPEP.Imported.Consumer.PG2
```

Recovery applies the fixed source-affine PG2 strategy: form exact constant/value equations from rounded raw seeds, construct a source-derived Gram residual and synthesize exact PSD factors, with 64 denominator trials starting at 500000 and descending. The input is accepted by its source semantics, native axes, ordered rows, full 158-item direct policy and exact checks. The policy is fixed at `M=1000000`, `eta=1/1000000`, with the original factor policy. Optional `--expected-sha256` checks input integrity. A failed attempt does not publish `selected_exact.json`.

`verify` checks a supplied exact candidate and renders a fresh `Replay.lean`. Both modes invoke Lean, inspect printed axiom dependencies, and publish selected data only after successful Lean acceptance. The capture and candidate inputs remain unchanged. Recovery is a bounded strategy for this source family; the CLI uses the fixed PG2 basis, 20 labels/references, unit-scale `leZero` capture rows and supported value-slot mapping. The lower Rows interface has additional representation capabilities, described in [architecture](architecture.md).

## Generic proof interface

The consumer imports `LeanPEP.ActualFunction.ProximalGradientCaptureAuditCore`. Its 57 project modules are bound to their source bytes and imports by [the content review](pg-core-content-review.json). Missing sources, unreviewed modules, modified reviewed content or a changed dependency closure are rejected. This is a maintained engineering review; Lean checks the resulting proof objects. Concrete certificate applications and regression modules remain outside that generic closure, while the complete library entry preserves them.

The resulting actual-function theorem is about the second iterate in an arbitrary complete real Hilbert space, with real-valued convex `h`, the analytic smooth-convex contract for `f,g`, positive `L`, nonnegative `R`, a composite minimizer, the radius condition, and a two-step proximal-gradient run of step size `1/L`. It bounds the final composite gap by `L*R^2` times the checked rational bound. The generated concrete checking proof closes the interface's `hc` premise; no zero-gradient condition at the minimizer or extra subgradient at the initial point is required.

## Execution records

The consumer clears inherited `LEAN_PATH` and `PYTHONPATH` for child commands and records closure status separately from execution status and actual-upper verification. `--timeout` controls Lean/Lake child commands; the candidate calculation remains the fixed finite search. Wall time is recorded. When available, resource high-water marks are converted to bytes; SELF includes Python imports and CHILDREN is not a process-tree sum. [Reproducibility](reproducibility.md) distinguishes the reorganized source validation from retained historical experiments and their timing scope.
