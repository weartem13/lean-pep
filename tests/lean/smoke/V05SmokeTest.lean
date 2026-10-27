import LeanPEP

namespace LeanPEP.Toy

-- The same generic checker accepts upper certificates at two trajectory lengths.
#eval FiniteGD.checkUpperCertQ FiniteGD.oneStepUpperCertQ
#eval FiniteGD.checkUpperCertQ FiniteGD.twoStepUpperCertQ

#eval FiniteGD.auditUpperCertQ FiniteGD.oneStepUpperCertQ
#eval FiniteGD.auditUpperCertQ FiniteGD.twoStepUpperCertQ

-- Three independent exact rejection paths.
#eval FiniteGD.auditUpperCertQ FiniteGD.badNegativeInterpUpperCertQ
#eval FiniteGD.auditUpperCertQ FiniteGD.badNegativeSquareUpperCertQ
#eval FiniteGD.auditUpperCertQ FiniteGD.badWrongBoundUpperCertQ

example :
    FiniteGD.checkUpperCertQ FiniteGD.oneStepUpperCertQ = true := by
  exact FiniteGD.oneStepUpperCertQ_check

example :
    FiniteGD.checkUpperCertQ FiniteGD.twoStepUpperCertQ = true := by
  exact FiniteGD.twoStepUpperCertQ_check

example (d : FiniteGD.DataR 1) (h : FiniteGD.Feasible d) :
    d.value 1 ≤ (1 : ℝ) / 6 := by
  exact FiniteGD.oneStep_upper_from_generic_certificate d h

example (d : FiniteGD.DataR 2) (h : FiniteGD.Feasible d) :
    d.value 2 ≤ (1 : ℝ) / 10 := by
  exact FiniteGD.twoStep_upper_from_generic_certificate d h

-- The generic certificate theorem re-proves the bound used by the N = 2 room.
example (d : TwoStep.TwoStepData) (h : FiniteGD.Feasible d) :
    d.value 2 ≤ (1 : ℝ) / 10 := by
  exact FiniteGD.twoStep_upper_from_generic_certificate d h

end LeanPEP.Toy
