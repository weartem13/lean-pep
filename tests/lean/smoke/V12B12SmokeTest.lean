import LeanPEP

#check LeanPEP.Toy.FiniteGD.ParametricUpper.slackPolyQ_quadCoeff_swap
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdQuadraticInterpSumQ_swap
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdQuadraticSquareSumQ_swap
#check LeanPEP.Toy.FiniteGD.ParametricUpper.slackPolyQ_star_iter_quadCoeff_of_lt
#check LeanPEP.Toy.FiniteGD.ParametricUpper.slackPolyQ_consecutive_quadCoeff_of_ne
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdQuadraticInterpSumQ_of_lt
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdQuadraticSquareContributionQ_eq_neg_half_gradient_of_lt
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdQuadraticSquareSumQ_eq_neg_half_gradient_of_lt
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdQuadraticCoefficientIdentityQ_of_lt
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdQuadraticCoefficientIdentityQ_offDiagonal
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdCertificate_quadCoeff_of_ne
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdCertificate_quadCoefficients_offDiagonal

namespace LeanPEP.Toy.FiniteGD.V12B12Smoke

open LeanPEP.Toy.FiniteGD.ParametricUpper

/-- One strict upper-triangular ordered quadratic coefficient vanishes for an
arbitrary trajectory length. -/
example (N : ℕ) (r s : Fin (N + 1)) (hrs : r.val < s.val) :
    gdQuadraticInterpSumQ N r s +
      gdQuadraticSquareSumQ N r s = 0 :=
  gdQuadraticCoefficientIdentityQ_of_lt N r s hrs

/-- Both ordered off-diagonal directions are covered. -/
example (N : ℕ) (r s : Fin (N + 1)) (hrs : r ≠ s) :
    gdQuadraticInterpSumQ N r s +
      gdQuadraticSquareSumQ N r s = 0 :=
  gdQuadraticCoefficientIdentityQ_offDiagonal N r s hrs

/-- Concrete generated coefficient regression beyond the original hand-written
small-step certificates. -/
example :
    (certificateRhsPolyQ (gdUpperCertQ 8)).quadCoeff
        (⟨2, by decide⟩ : Fin 9) (⟨5, by decide⟩ : Fin 9) =
      (upperTargetPolyQ (gdBoundQ 8) (gdObjective 8)).quadCoeff
        (⟨2, by decide⟩ : Fin 9) (⟨5, by decide⟩ : Fin 9) :=
  gdCertificate_quadCoeff_of_ne 8
    (⟨2, by decide⟩ : Fin 9) (⟨5, by decide⟩ : Fin 9) (by decide)

end LeanPEP.Toy.FiniteGD.V12B12Smoke
