import LeanPEP

#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdConstantTailQ
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdConstantContributionQ_castSucc
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdConstantContributionQ_last
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdConstantTailQ_zero_eq_bound
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdConstantSumQ_eq_fin_sum
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdConstantContributions_sum
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdConstantCoefficientIdentityQ_all
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdCertificate_constCoeff

namespace LeanPEP.Toy.FiniteGD.V12B7Smoke

open LeanPEP.Toy.FiniteGD.ParametricUpper

/-- Every nonfinal contribution is an adjacent tail difference. -/
example (N : ℕ) (k : Fin N) :
    gdConstantContributionQ N k.castSucc =
      gdConstantTailQ N k.val - gdConstantTailQ N (k.val + 1) :=
  gdConstantContributionQ_castSucc N k

/-- The full finite constant sum equals the closed-form bound. -/
example (N : ℕ) :
    gdConstantSumQ N = gdBoundQ N :=
  gdConstantCoefficientIdentityQ_all N

/-- The certificate and target constant coefficients agree for every `N`. -/
example (N : ℕ) :
    (certificateRhsPolyQ (gdUpperCertQ N)).constCoeff =
      (upperTargetPolyQ (gdBoundQ N) (gdObjective N)).constCoeff :=
  gdCertificate_constCoeff N

end LeanPEP.Toy.FiniteGD.V12B7Smoke
