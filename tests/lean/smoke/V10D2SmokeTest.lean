import LeanPEP

open LeanPEP
open LeanPEP.GramPEP
open LeanPEP.GramPEP.UpperCertificateExamples
open LeanPEP.GramPEP.UpperCertificateAuditExamples

#check NegativeInterpWeightQ
#check NegativeAssumptionWeightQ
#check LinearCoeffLocationQ
#check LinearCoeffMismatchQ
#check UpperCertAuditReportQ
#check auditUpperCertQ
#check auditUpperCertQ_accepted_iff
#check auditUpperCertQ_sound_real
#check mem_negativeInterpWeightsQ_sound
#check mem_negativeAssumptionWeightsQ_sound
#check mem_linearExprMismatchesQ_sound
#check upperCertQ_audit
#check oneStepUpperCertQ_audit
#check cancellingNegativeInterpCertQ_audit
#check cancellingNegativeAssumptionCertQ_audit
#check cancellingNegativeDualCertQ_audit
#check missingDualFactorCertQ_audit
#check wrongBoundCertQ_audit
#check combinedFailureCertQ_audit

#eval auditUpperCertQ upperCertQ
#eval auditUpperCertQ oneStepUpperCertQ
#eval auditUpperCertQ cancellingNegativeInterpCertQ
#eval auditUpperCertQ cancellingNegativeAssumptionCertQ
#eval auditUpperCertQ cancellingNegativeDualCertQ
#eval auditUpperCertQ missingDualFactorCertQ
#eval auditUpperCertQ wrongBoundCertQ
#eval auditUpperCertQ combinedFailureCertQ

example : (auditUpperCertQ upperCertQ).accepted = true := by
  native_decide

example : (auditUpperCertQ combinedFailureCertQ).accepted = false := by
  native_decide
