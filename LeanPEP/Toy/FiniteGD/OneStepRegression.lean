import LeanPEP.Toy.FiniteGD.RationalChecker
import LeanPEP.Toy.OneStep.AuditReport

/-!
# Regression checks against the original one-step implementation

The generic checker is exercised on exact copies of the original one-step
witness and pseudo-certificate.  These tests protect the first completed room
while the code base moves to a parameterized trajectory representation.
-/

namespace LeanPEP
namespace Toy
namespace FiniteGD

/-- Embed the original hard-coded one-step rational data into the generic
`N = 1` representation. -/
def fromOneStepQ
    (d : LeanPEP.Toy.OneStep.OneStepDataQ) : DataQ 1 :=
  { grad := ![d.g0, d.g1]
    value := ![d.f0, d.f1] }

/-- The generic checker accepts the original exact `1 / 6` witness. -/
theorem oneStep_exactWitness_generic_check :
    checkFeasibleQ
      (fromOneStepQ LeanPEP.Toy.OneStep.exactWitnessQ) = true := by
  native_decide

/-- The generic checker rejects the original pseudo-certificate. -/
theorem oneStep_pseudoCert_generic_check :
    checkFeasibleQ
      (fromOneStepQ LeanPEP.Toy.OneStep.pseudoCertQ) = false := by
  native_decide

/-- The generic complete audit gives the exact witness an empty report. -/
theorem oneStep_exactWitness_generic_no_violations :
    allViolationsQ
      (fromOneStepQ LeanPEP.Toy.OneStep.exactWitnessQ) = [] := by
  native_decide

/-- The generic audit marks the original pseudo-certificate as rejected. -/
theorem oneStep_pseudoCert_generic_rejected :
    (auditPrimalQ
      (fromOneStepQ LeanPEP.Toy.OneStep.pseudoCertQ)).accepted = false := by
  native_decide

end FiniteGD
end Toy
end LeanPEP
