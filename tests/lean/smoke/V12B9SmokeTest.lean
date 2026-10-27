import LeanPEP

#check LeanPEP.Toy.FiniteGD.ParametricUpper.prefixAffine_gradCoeff
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdSquareFormQ_gradCoeff
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdSquareFormQ_gradCoeff_self
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdSquareFormQ_gradCoeff_of_lt
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdSquareFormQ_gradCoeff_of_gt
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdGradientSquareContributionQ_self
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdGradientSquareContributionQ_of_lt
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdGradientSquareContributionQ_of_gt
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdGradientConstantSuffixQ
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdGradientSquareSumQ_decompose
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdGradientCoefficientIdentityQ_iff_suffix
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdGradientSuffixIdentityQ_last
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdGradientSuffixIdentityQ_4
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdGradientSuffixIdentityQ_8

namespace LeanPEP.Toy.FiniteGD.V12B9Smoke

open LeanPEP.Toy.FiniteGD.ParametricUpper

/-- A later reverse-LDL factor sees an earlier sampled gradient through the
reciprocal prefix coefficient. -/
example :
    (gdSquareFormQ 8 (⟨5, by omega⟩ : Fin 9)).gradCoeff
        (⟨2, by omega⟩ : Fin 9) = (1 : ℚ) / 12 := by
  rw [gdSquareFormQ_gradCoeff_of_lt]
  · norm_num
  · norm_num

/-- At the final sampled-gradient index the strict suffix is empty and the
star term cancels the diagonal square contribution. -/
example (N : ℕ) :
    gdStarWeightQ N (Fin.last N) +
      (gdGradientSquareContributionQ N (Fin.last N) (Fin.last N) -
        2 * gdGradientConstantSuffixQ N (Fin.last N)) = 0 :=
  gdGradientSuffixIdentityQ_last N

/-- Existing checker-verified identities pass through the new suffix
reduction. -/
example : gdGradientSuffixIdentityQ 8 :=
  gdGradientSuffixIdentityQ_8

end LeanPEP.Toy.FiniteGD.V12B9Smoke
