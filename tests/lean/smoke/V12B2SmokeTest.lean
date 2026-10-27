import LeanPEP

#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdCenterQ
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdBoundQ
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdObjective
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdChainWeightQ
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdStarWeightQ
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdCenteredGradQ
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdCenteredPrefixQ
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdSquareFormQ
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdSquareWeightQ
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdInterpTermsQ
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdSquareTermsQ
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdUpperCertQ
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gd_upper_of_check
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdUpperCertQ_check_0
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdUpperCertQ_check_4
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdUpperCertQ_check_8

namespace LeanPEP.Toy.FiniteGD.V12B2Smoke

open LeanPEP.Toy.FiniteGD
open LeanPEP.Toy.FiniteGD.ParametricUpper

/-- The generated four-step certificate proves its exact finite-PEP upper
bound through the unchanged generic checker soundness theorem. -/
example
    (d : DataR 4)
    (h : Feasible d) :
    d.value (gdObjective 4) ≤ (gdBoundQ 4 : ℝ) :=
  gd_upper_of_check 4 gdUpperCertQ_check_4 d h

/-- A larger generated instance exercises the same constructor and checker. -/
example
    (d : DataR 8)
    (h : Feasible d) :
    d.value (gdObjective 8) ≤ (gdBoundQ 8 : ℝ) :=
  gd_upper_of_check 8 gdUpperCertQ_check_8 d h

end LeanPEP.Toy.FiniteGD.V12B2Smoke
