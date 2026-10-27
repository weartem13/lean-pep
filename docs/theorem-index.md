# Theorem index

| Scope | Declaration / file |
|---|---|
| Semantic certificate to actual PG bound | `LeanPEP.ActualFunction.ProximalGradientSparseAudit.upper_analytic`, `LeanPEP/ActualFunction/ProximalGradientSparseAuditCore.lean` |
| Capture-policy entry | `LeanPEP.ActualFunction.ProximalGradientCaptureAudit.upper_analytic`, corresponding CaptureAuditCore file |
| Finite performance lifting | `LeanPEP.Adapters.ProximalGradientPerformance.rows_feasible_iff`, `finite_upper_equivalence` |
| PG exact one-step pair | `LeanPEP.ActualFunction.PGOneCapturedTightness.finite_tightness`, `actual_tightness` |
| GD exact one-step pair | `LeanPEP.ActualFunction.GDOneCapturedTightness.finite_tightness`, `actual_tightness` |
| Target binding example | `LeanPEP.Imported.CompositeRows.forged_local_passes`, `forged_joint_rejected` |
| Synchronized Rows example | `LeanPEP.Imported.CompositeRows.PGOne.bound_check`, `LeanPEP.Imported.CompositeRows.one_rhs_preserved` |

The complete historical mathematical/declaration inventory remains in `reference/v0.14-mathematics.md` and `reference/v0.14-declarations.md`; statements and namespaces were retained. The [declaration/evidence map](evidence/claim-evidence.md) connects the cases to their actual data, proofs and historical execution evidence. PG/GD gap/exact cases are distinct; finite primal attainment and actual function attainment have distinct witnesses.
