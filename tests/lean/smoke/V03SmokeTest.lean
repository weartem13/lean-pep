import LeanPEP.Toy.OneStep.AuditReport
import LeanPEP.Toy.OneStep.UpperCertificateChecker

namespace LeanPEP.Toy.OneStep

#eval auditPrimalQ exactWitnessQ
#eval auditPrimalQ pseudoCertQ

#eval checkUpperCertQ exactUpperCertQ
#eval auditUpperCertQ exactUpperCertQ
#eval auditUpperCertQ negativeInterpUpperCertQ
#eval auditUpperCertQ negativeSquareUpperCertQ
#eval auditUpperCertQ wrongBoundUpperCertQ

example : checkUpperCertQ exactUpperCertQ = true := by
  exact exactUpperCertQ_check

example (d : OneStepData) (h : OneStepFeasible d) :
    d.f1 ≤ (1 : ℝ) / 6 := by
  exact oneStep_upper_from_exact_certificate d h

end LeanPEP.Toy.OneStep
