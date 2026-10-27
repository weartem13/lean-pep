import LeanPEP

#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdBoundQ_eq_half_centerQ
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdStarWeightQ_zero_zero
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdStarWeightQ_zero_eq_chainWeightQ_zero
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdStarWeightQ_succ_eq_chainWeightQ_sub
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdStarWeightQ_last_eq_one_sub_chainWeightQ_last

namespace LeanPEP.Toy.FiniteGD.V12B4Smoke

open LeanPEP.Toy.FiniteGD.ParametricUpper

/-- The first star coefficient starts the interpolation flow. -/
example :
    gdStarWeightQ 4 ⟨0, by omega⟩ =
      gdChainWeightQ 4 ⟨0, by omega⟩ :=
  gdStarWeightQ_zero_eq_chainWeightQ_zero 4 (by omega)

/-- An interior coefficient is an exact flow increment. -/
example :
    gdStarWeightQ 4 ⟨2, by omega⟩ =
      gdChainWeightQ 4 ⟨2, by omega⟩ -
        gdChainWeightQ 4 ⟨1, by omega⟩ :=
  gdStarWeightQ_succ_eq_chainWeightQ_sub 4 1 (by omega)

/-- The final coefficient closes the flow at total mass one. -/
example :
    gdStarWeightQ 4 ⟨4, by omega⟩ =
      1 - gdChainWeightQ 4 ⟨3, by omega⟩ :=
  gdStarWeightQ_last_eq_one_sub_chainWeightQ_last 4 (by omega)

end LeanPEP.Toy.FiniteGD.V12B4Smoke
