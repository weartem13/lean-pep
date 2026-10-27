import LeanPEP

#check LeanPEP.Toy.FiniteGD.ParametricUpper.pointValuePolyQ_quadCoeff
#check LeanPEP.Toy.FiniteGD.ParametricUpper.slackPolyQ_quadCoeff
#check LeanPEP.Toy.FiniteGD.ParametricUpper.interpPolySumQ_quadCoeff
#check LeanPEP.Toy.FiniteGD.ParametricUpper.squarePolySumQ_quadCoeff
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdQuadraticInterpSumQ
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdQuadraticSquareContributionQ
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdQuadraticSquareSumQ
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdCertificateRhs_quadCoeff_eq_quadraticSumsQ
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdQuadraticCoefficientIdentityQ
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdCertificate_quadCoefficients_eq_target_iff
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdQuadraticCoefficientIdentityQ_of_identity
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdQuadraticCoefficientIdentityQ_4
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdQuadraticCoefficientIdentityQ_8

namespace LeanPEP.Toy.FiniteGD.V12B11Smoke

open LeanPEP.Toy.FiniteGD.ParametricUpper

/-- One generated ordered quadratic coefficient is the sum of the explicit
interpolation and affine-square contributions. -/
example (N : ℕ) (r s : Fin (N + 1)) :
    (certificateRhsPolyQ (gdUpperCertQ N)).quadCoeff r s =
      gdQuadraticInterpSumQ N r s +
        gdQuadraticSquareSumQ N r s :=
  gdCertificateRhs_quadCoeff_eq_quadraticSumsQ N r s

/-- The existing exact checker regression at `N = 4` satisfies the reduced
ordered quadratic identity. -/
example : gdQuadraticCoefficientIdentityQ 4 :=
  gdQuadraticCoefficientIdentityQ_4

/-- Any future proof of the full generated polynomial identity immediately
supplies the reduced ordered quadratic family. -/
example (N : ℕ) (h : gdCertificateIdentityQ N) :
    gdQuadraticCoefficientIdentityQ N :=
  gdQuadraticCoefficientIdentityQ_of_identity N h

end LeanPEP.Toy.FiniteGD.V12B11Smoke
