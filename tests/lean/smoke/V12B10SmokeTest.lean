import LeanPEP

#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdGradientConstantSuffixQ_eq_tail_of_lt
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdGradientSuffixIdentityQ_of_lt
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdGradientSuffixIdentityQ_all
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdGradientCoefficientIdentityQ_all
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdCertificate_gradCoeff
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdCertificate_gradCoefficients

namespace LeanPEP.Toy.FiniteGD.V12B10Smoke

open LeanPEP.Toy.FiniteGD.ParametricUpper

/-- The strict suffix after sampled-gradient index `2` is the tail potential
at index `3`. -/
example :
    gdGradientConstantSuffixQ 8 (⟨2, by omega⟩ : Fin 9) =
      gdConstantTailQ 8 3 :=
  gdGradientConstantSuffixQ_eq_tail_of_lt 8
    (⟨2, by omega⟩ : Fin 9) (by decide)

/-- A nonfinal sampled-gradient index satisfies the exact local cancellation. -/
example :
    gdStarWeightQ 8 (⟨5, by omega⟩ : Fin 9) +
      (gdGradientSquareContributionQ 8
          (⟨5, by omega⟩ : Fin 9)
          (⟨5, by omega⟩ : Fin 9) -
        2 * gdGradientConstantSuffixQ 8
          (⟨5, by omega⟩ : Fin 9)) = 0 :=
  gdGradientSuffixIdentityQ_of_lt 8
    (⟨5, by omega⟩ : Fin 9) (by decide)

/-- The complete gradient-linear family is closed for arbitrary trajectory
length. -/
example (N : ℕ) : gdGradientCoefficientIdentityQ N :=
  gdGradientCoefficientIdentityQ_all N

/-- The generated and target sampled-gradient coefficients agree pointwise. -/
example (N : ℕ) (r : Fin (N + 1)) :
    (certificateRhsPolyQ (gdUpperCertQ N)).gradCoeff r =
      (upperTargetPolyQ (gdBoundQ N) (gdObjective N)).gradCoeff r :=
  gdCertificate_gradCoeff N r

end LeanPEP.Toy.FiniteGD.V12B10Smoke
