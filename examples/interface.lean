import LeanPEP.ActualFunction.ProximalGradientCaptureAuditCore

-- Parameterized contracts; the concrete PG2 check is run by scripts/verify.py quick.
#check LeanPEP.ActualFunction.ProximalGradientSparseAudit.upper_analytic
#check LeanPEP.ActualFunction.ProximalGradientCaptureAudit.upper_analytic
#print axioms LeanPEP.ActualFunction.ProximalGradientSparseAudit.upper_analytic
#print axioms LeanPEP.ActualFunction.ProximalGradientCaptureAudit.upper_analytic
