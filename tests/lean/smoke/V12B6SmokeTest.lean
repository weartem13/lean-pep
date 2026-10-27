import LeanPEP

#check LeanPEP.Toy.FiniteGD.ParametricUpper.slackPolyQ_constCoeff
#check LeanPEP.Toy.FiniteGD.ParametricUpper.interpPolySumQ_constCoeff
#check LeanPEP.Toy.FiniteGD.ParametricUpper.squarePolySumQ_constCoeff
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdSquareFormQ_constCoeff
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdConstantContributionQ_closed
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdCertificateRhs_constCoeff_eq_constantSumQ
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdCertificate_constCoeff_eq_target_iff
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdConstantCoefficientIdentityQ_0
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdConstantCoefficientIdentityQ_4
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdConstantCoefficientIdentityQ_8

namespace LeanPEP.Toy.FiniteGD.V12B6Smoke

open LeanPEP.Toy.FiniteGD.ParametricUpper

/-- The constant coefficient is reduced to the generated finite rational sum. -/
example (N : ℕ) :
    (certificateRhsPolyQ (gdUpperCertQ N)).constCoeff = gdConstantSumQ N :=
  gdCertificateRhs_constCoeff_eq_constantSumQ N

/-- The fourth generated certificate satisfies the reduced scalar identity. -/
example : gdConstantSumQ 4 = gdBoundQ 4 :=
  gdConstantCoefficientIdentityQ_4

/-- Constant-channel equality is equivalent to the exposed finite-sum goal. -/
example (N : ℕ) :
    (certificateRhsPolyQ (gdUpperCertQ N)).constCoeff =
        (upperTargetPolyQ (gdBoundQ N) (gdObjective N)).constCoeff ↔
      gdConstantCoefficientIdentityQ N :=
  gdCertificate_constCoeff_eq_target_iff N

end LeanPEP.Toy.FiniteGD.V12B6Smoke
