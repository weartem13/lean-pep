import LeanPEP

#check LeanPEP.Toy.FiniteGD.ParametricUpper.pointValuePolyQ_gradCoeff
#check LeanPEP.Toy.FiniteGD.ParametricUpper.slackPolyQ_gradCoeff
#check LeanPEP.Toy.FiniteGD.ParametricUpper.slackPolyQ_star_iter_gradCoeff
#check LeanPEP.Toy.FiniteGD.ParametricUpper.slackPolyQ_iter_iter_gradCoeff
#check LeanPEP.Toy.FiniteGD.ParametricUpper.interpPolySumQ_gradCoeff
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdStarTermsQ_gradCoeff
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdChainTermsQ_gradCoeff
#check LeanPEP.Toy.FiniteGD.ParametricUpper.squarePolySumQ_gradCoeff
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdGradientSquareContributionQ
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdGradientSquareSumQ
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdCertificateRhs_gradCoeff_eq_gradientSumQ
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdGradientCoefficientIdentityQ
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdCertificate_gradCoefficients_eq_target_iff
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdGradientCoefficientIdentityQ_4
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdGradientCoefficientIdentityQ_8

namespace LeanPEP.Toy.FiniteGD.V12B8Smoke

open LeanPEP.Toy.FiniteGD.ParametricUpper

/-- Star interpolation is the entire gradient-linear interpolation channel. -/
example (N : ℕ) (r : Fin (N + 1)) :
    (interpPolySumQ (gdInterpTermsQ N)).gradCoeff r =
      gdStarWeightQ N r :=
  gdInterpTermsQ_gradCoeff N r

/-- The checker-verified `N = 4` identity satisfies the reduced pointwise
finite-sum obligation. -/
example : gdGradientCoefficientIdentityQ 4 :=
  gdGradientCoefficientIdentityQ_4

/-- The reduced family recovers exact generated/target coefficient equality
for the checker-verified `N = 8` regression. -/
example (r : Fin 9) :
    (certificateRhsPolyQ (gdUpperCertQ 8)).gradCoeff r =
      (upperTargetPolyQ (gdBoundQ 8) (gdObjective 8)).gradCoeff r :=
  (gdCertificate_gradCoefficients_eq_target_iff 8).2
    gdGradientCoefficientIdentityQ_8 r

end LeanPEP.Toy.FiniteGD.V12B8Smoke
