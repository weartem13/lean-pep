import LeanPEP

#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdChainWeightQ_nonneg
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdStarWeightQ_nonneg
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdSquareWeightQ_nonneg
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdInterpTermsQ_weights_nonneg
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdSquareTermsQ_weights_nonneg
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdCertificateIdentityQ
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdUpperCertQ_valid_of_identity
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdUpperCertQ_check_eq_true_iff_identity
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdUpperCertQ_check_of_identity
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gd_upper_of_identity
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdCertificateIdentityQ_0
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdCertificateIdentityQ_4
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdCertificateIdentityQ_8

namespace LeanPEP.Toy.FiniteGD.V12B3Smoke

open LeanPEP.Toy.FiniteGD
open LeanPEP.Toy.FiniteGD.ParametricUpper

/-- The reduction is quantified over arbitrary trajectory length. -/
example
    (N : ℕ)
    (hidentity : gdCertificateIdentityQ N)
    (d : DataR N)
    (hfeasible : Feasible d) :
    d.value (gdObjective N) ≤ (gdBoundQ N : ℝ) :=
  gd_upper_of_identity N hidentity d hfeasible

/-- A previously checked generated instance yields the exposed identity. -/
example : gdCertificateIdentityQ 8 :=
  gdCertificateIdentityQ_8

end LeanPEP.Toy.FiniteGD.V12B3Smoke
