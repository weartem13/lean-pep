import LeanPEP

open scoped NNReal

#check LeanPEP.ActualFunction.ParametricGDScaling.normalizedFunction
#check LeanPEP.ActualFunction.ParametricGDScaling.normalizedGradient
#check LeanPEP.ActualFunction.ParametricGDScaling.normalizedFirstOrder
#check LeanPEP.ActualFunction.ParametricGDScaling.smoothGDIterate
#check LeanPEP.ActualFunction.ParametricGDScaling.smoothGDIterate_succ
#check LeanPEP.ActualFunction.IsSmoothConvexFirstOrder.parametricGD_upper_exact_radius
#check LeanPEP.ActualFunction.IsSmoothConvexFirstOrder.parametricGD_upper_radius
#check LeanPEP.ActualFunction.IsSmoothConvexFirstOrder.parametricGD_upper_unit_radius
#check LeanPEP.ActualFunction.IsSmoothConvexAnalytic.parametricGD_upper_exact_radius
#check LeanPEP.ActualFunction.IsSmoothConvexAnalytic.parametricGD_upper_radius
#check LeanPEP.ActualFunction.IsSmoothConvexAnalytic.parametricGD_upper_unit_radius

namespace LeanPEP.ActualFunction.V12C3Smoke

open LeanPEP.Toy.FiniteGD.ParametricUpper
open LeanPEP.ActualFunction.ParametricGDScaling

variable
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {L : ℝ≥0} {f : E → ℝ} {g : E → E}

/-- The public recurrence exposes the step size `1 / L`. -/
example (x0 : E) (k : ℕ) :
    smoothGDIterate L g x0 (k + 1) =
      smoothGDIterate L g x0 k -
        (L : ℝ)⁻¹ • g (smoothGDIterate L g x0 k) :=
  smoothGDIterate_succ L g x0 k

/-- The general first-order exact-radius theorem is directly callable. -/
example
    (h : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ))
    (N : ℕ) {xStar x0 : E}
    (hstationary : g xStar = 0) :
    f (smoothGDIterate L g x0 N) - f xStar ≤
      (L : ℝ) * ‖x0 - xStar‖ ^ 2 * (gdBoundQ N : ℝ) :=
  h.parametricGD_upper_exact_radius hL N hstationary

/-- The external-radius presentation is directly callable. -/
example
    (h : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ))
    (N : ℕ) {xStar x0 : E} {R : ℝ}
    (hstationary : g xStar = 0)
    (hradius : ‖x0 - xStar‖ ^ 2 ≤ R ^ 2) :
    f (smoothGDIterate L g x0 N) - f xStar ≤
      (L : ℝ) * R ^ 2 * (gdBoundQ N : ℝ) :=
  h.parametricGD_upper_radius hL N hstationary hradius

end LeanPEP.ActualFunction.V12C3Smoke
