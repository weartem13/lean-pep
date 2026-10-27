import LeanPEP

#check LeanPEP.ActualFunction.ParametricGDActual.unitGDIterate
#check LeanPEP.ActualFunction.ParametricGDActual.sampledGradient
#check LeanPEP.ActualFunction.ParametricGDActual.sampledValue
#check LeanPEP.ActualFunction.ParametricGDActual.actualPoint
#check LeanPEP.ActualFunction.ParametricGDActual.prefixVector_sampledGradient
#check LeanPEP.ActualFunction.ParametricGDActual.pointPosition_sampledGradient
#check LeanPEP.ActualFunction.ParametricGDActual.actualPoint_iter_succ
#check LeanPEP.ActualFunction.ParametricGDActual.interpolationSlack_sampled
#check LeanPEP.ActualFunction.ParametricGDActual.feasible_of_firstOrder
#check LeanPEP.ActualFunction.IsOneSmoothConvexFirstOrder.parametricGD_upper_exact_radius
#check LeanPEP.ActualFunction.IsOneSmoothConvexFirstOrder.parametricGD_upper_unit_radius
#check LeanPEP.ActualFunction.IsOneSmoothConvexAnalytic.parametricGD_upper_exact_radius
#check LeanPEP.ActualFunction.IsOneSmoothConvexAnalytic.parametricGD_upper_unit_radius

namespace LeanPEP.ActualFunction.V12C2Smoke

open LeanPEP.Toy.FiniteGD.ParametricUpper
open LeanPEP.ActualFunction.ParametricGDActual

variable
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {g : E → E}

/-- The public recurrence theorem exposes the actual unit-step update at every
nonfinal sampled index. -/
example (N : ℕ) (xStar x0 : E) (k : Fin N) :
    actualPoint N xStar g x0
        (LeanPEP.Toy.FiniteGD.Point.iter ⟨k.val + 1, by omega⟩) =
      actualPoint N xStar g x0
          (LeanPEP.Toy.FiniteGD.Point.iter ⟨k.val, by omega⟩) -
        g (actualPoint N xStar g x0
          (LeanPEP.Toy.FiniteGD.Point.iter ⟨k.val, by omega⟩)) :=
  actualPoint_iter_succ N xStar g x0 k

/-- The first-order arbitrary-length theorem is directly callable. -/
example
    (h : IsOneSmoothConvexFirstOrder f g)
    (N : ℕ) {xStar x0 : E}
    (hstationary : g xStar = 0) :
    f (unitGDIterate g x0 N) - f xStar ≤
      (gdBoundQ N : ℝ) * ‖x0 - xStar‖ ^ 2 :=
  h.parametricGD_upper_exact_radius N hstationary

/-- The unit-radius presentation is directly callable. -/
example
    (h : IsOneSmoothConvexFirstOrder f g)
    (N : ℕ) {xStar x0 : E}
    (hstationary : g xStar = 0)
    (hradius : ‖x0 - xStar‖ ^ 2 ≤ 1) :
    f (unitGDIterate g x0 N) - f xStar ≤ (gdBoundQ N : ℝ) :=
  h.parametricGD_upper_unit_radius N hstationary hradius

end LeanPEP.ActualFunction.V12C2Smoke
