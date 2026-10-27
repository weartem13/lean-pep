# Architecture

`LeanPEP.ActualFunction.ProximalGradientSparseAudit.upper_analytic` consumes `checkBoundQ s c = true` and yields an actual-function upper bound under its complete contract. `ProximalGradientCaptureAudit.upper_analytic` adds trace/raw/policy checking through `checkCapturedQ`. Concrete generated checks close the interface premise before the theorem is offered to a function user.

Source/coordinate/ordering/Rows/performance/sparse transports preserve the submitted bound and certificate expression under their checked conditions. `ProximalGradientPerformance.rows_feasible_iff` characterizes a lifted row system by the base rows and `tau ≤ metric`; `finite_upper_equivalence` uses `tau = metric` in the reverse implication. Actual trajectory embedding, PSD realization and physical `L R²` scaling are separate lemmas, including the original `R=0` branch.

The consumer imports `ProximalGradientCaptureAuditCore`. Its 57 project modules are pinned in `pg-core-content-review.json`; this maintained content/dependency guard is unchanged by the directory cleanup. The full `LeanPEP.lean` aggregate retains the other mathematical developments and regressions. Ten modules outside that aggregate are explicitly listed in `scripts/verification.json`.

Mathematics is parameterized by a positive horizon; executable consumption is the fixed PG2 family. The capture trace requires unit-scale leZero rules and preserves Gram/prepared-row order while mapping value slots. Lower-level Rows positive scaling does not enlarge the capture CLI's scope. Numerical recovery is untrusted; the original exact identity, PSD, source and direct 158-entry policy checks remain authoritative.
