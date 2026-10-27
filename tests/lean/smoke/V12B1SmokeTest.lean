import LeanPEP

open scoped NNReal

#check LeanPEP.ActualFunction.IsSmoothConvexAnalytic
#check LeanPEP.ActualFunction.IsSmoothConvexFirstOrder
#check LeanPEP.ActualFunction.IsSmoothConvexAnalytic.gradient_eq
#check LeanPEP.ActualFunction.IsSmoothConvexAnalytic.differentiable
#check LeanPEP.ActualFunction.IsSmoothConvexAnalytic.lowerModel
#check LeanPEP.ActualFunction.IsSmoothConvexAnalytic.upperModel
#check LeanPEP.ActualFunction.IsSmoothConvexAnalytic.toFirstOrder
#check LeanPEP.ActualFunction.IsOneSmoothConvexAnalytic.toSmooth
#check LeanPEP.ActualFunction.IsOneSmoothConvexFirstOrder.toSmooth
#check LeanPEP.ActualFunction.SmoothScaling.scaledPoint
#check LeanPEP.ActualFunction.SmoothScaling.normalizedFunction
#check LeanPEP.ActualFunction.SmoothScaling.normalizedGradient
#check LeanPEP.ActualFunction.SmoothScaling.normalizedFirstOrder
#check LeanPEP.ActualFunction.IsOneSmoothConvexFirstOrder.oneStepGD_upper_at_update
#check LeanPEP.ActualFunction.IsSmoothConvexAnalytic.oneStepGD_upper_at_update_of_pos_radius
#check LeanPEP.ActualFunction.IsSmoothConvexAnalytic.oneStepGD_upper_at_update
#check LeanPEP.ActualFunction.IsSmoothConvexAnalytic.oneStepGD_upper
#check LeanPEP.ActualFunction.IsSmoothConvexAnalytic.oneStepGD_upper_exact_radius

namespace LeanPEP.ActualFunction.V12B1Smoke

open LeanPEP.ActualFunction

/-- The general analytic contract reaches the exact `L`-first-order models. -/
example
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {L : ℝ≥0} {f : E → ℝ} {g : E → E}
    (h : IsSmoothConvexAnalytic L f g) :
    IsSmoothConvexFirstOrder L f g :=
  h.toFirstOrder

/-- Positive coordinate and function-value scaling produces the normalized
first-order contract consumed by the existing one-step certificate. -/
example
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {L : ℝ≥0} {f : E → ℝ} {g : E → E}
    {xStar : E} {R : ℝ}
    (h : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hR : 0 < R) :
    IsOneSmoothConvexFirstOrder
      (SmoothScaling.normalizedFunction f xStar L R)
      (SmoothScaling.normalizedGradient g xStar L R) :=
  SmoothScaling.normalizedFirstOrder h hL hR

/-- The exact normalized certificate is available directly from first-order
models; no second differentiability proof is needed after normalization. -/
example
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {g : E → E}
    (h : IsOneSmoothConvexFirstOrder f g)
    {xStar x0 : E}
    (hstationary : g xStar = 0)
    (hradius : ‖x0 - xStar‖ ^ 2 ≤ 1) :
    f (x0 - g x0) - f xStar ≤ (1 : ℝ) / 6 :=
  h.oneStepGD_upper_at_update hstationary hradius

/-- The public theorem supports arbitrary positive smoothness and a
nonnegative radius bound. -/
example
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {L : ℝ≥0} {f : E → ℝ} {g : E → E}
    (h : IsSmoothConvexAnalytic L f g)
    (hL : 0 < (L : ℝ))
    {xStar x0 : E} {R : ℝ}
    (hR : 0 ≤ R)
    (hstationary : g xStar = 0)
    (hradius : ‖x0 - xStar‖ ^ 2 ≤ R ^ 2) :
    f (x0 - (L : ℝ)⁻¹ • g x0) - f xStar ≤
      (L : ℝ) * R ^ 2 / 6 :=
  h.oneStepGD_upper_at_update hL hR hstationary hradius

/-- The explicit-iterate form keeps the actual GD update as a hypothesis. -/
example
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {L : ℝ≥0} {f : E → ℝ} {g : E → E}
    (h : IsSmoothConvexAnalytic L f g)
    (hL : 0 < (L : ℝ))
    {xStar x0 x1 : E} {R : ℝ}
    (hR : 0 ≤ R)
    (hstationary : g xStar = 0)
    (hstep : x1 = x0 - (L : ℝ)⁻¹ • g x0)
    (hradius : ‖x0 - xStar‖ ^ 2 ≤ R ^ 2) :
    f x1 - f xStar ≤ (L : ℝ) * R ^ 2 / 6 :=
  h.oneStepGD_upper hL hR hstationary hstep hradius

/-- The exact-distance corollary removes the external radius parameter. -/
example
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {L : ℝ≥0} {f : E → ℝ} {g : E → E}
    (h : IsSmoothConvexAnalytic L f g)
    (hL : 0 < (L : ℝ))
    {xStar x0 : E}
    (hstationary : g xStar = 0) :
    f (x0 - (L : ℝ)⁻¹ • g x0) - f xStar ≤
      (L : ℝ) * ‖x0 - xStar‖ ^ 2 / 6 :=
  h.oneStepGD_upper_exact_radius hL hstationary

end LeanPEP.ActualFunction.V12B1Smoke
