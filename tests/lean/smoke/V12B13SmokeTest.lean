import LeanPEP

#check LeanPEP.Toy.FiniteGD.ParametricUpper.slackPolyQ_star_iter_quadCoeff_self
#check LeanPEP.Toy.FiniteGD.ParametricUpper.slackPolyQ_consecutive_quadCoeff_self
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdQuadraticInterpSumQ_self_of_lt
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdQuadraticInterpSumQ_self_last
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdQuadraticSquareSumQ_self_decompose
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdSquareWeightQ_add_nextTail_eq_chainWeightQ
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdQuadraticSquareSumQ_self_of_lt
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdQuadraticSquareSumQ_self_last
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdQuadraticCoefficientIdentityQ_diagonal
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdQuadraticCoefficientIdentityQ_all
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdCertificate_quadCoeff
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdCertificateIdentityQ_all
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdUpperCertQ_check_all
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gd_upper_all

namespace LeanPEP.Toy.FiniteGD.V12B13Smoke

open LeanPEP.Toy.FiniteGD.ParametricUpper

/-- Every diagonal ordered quadratic coefficient vanishes at arbitrary
trajectory length. -/
example (N : ℕ) (r : Fin (N + 1)) :
    gdQuadraticInterpSumQ N r r +
      gdQuadraticSquareSumQ N r r = 0 :=
  gdQuadraticCoefficientIdentityQ_diagonal N r

/-- The same theorem covers every ordered quadratic entry. -/
example (N : ℕ) (r s : Fin (N + 1)) :
    gdQuadraticInterpSumQ N r s +
      gdQuadraticSquareSumQ N r s = 0 :=
  gdQuadraticCoefficientIdentityQ_all N r s

/-- The unchanged generic checker accepts the generated certificate at every
trajectory length. -/
example (N : ℕ) :
    checkUpperCertQ (gdUpperCertQ N) = true :=
  gdUpperCertQ_check_all N

/-- Universal normalized finite-GD upper theorem obtained from the accepted
closed-form certificate. -/
example (N : ℕ) (d : DataR N) (hfeasible : Feasible d) :
    d.value (gdObjective N) ≤ (gdBoundQ N : ℝ) :=
  gd_upper_all N d hfeasible

end LeanPEP.Toy.FiniteGD.V12B13Smoke
