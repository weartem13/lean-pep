import LeanPEP

#check LeanPEP.ActualFunction.IsOneSmoothConvexAnalytic.oneStepGD_upper_of_inner_radius
#check LeanPEP.ActualFunction.IsOneSmoothConvexAnalytic.oneStepGD_upper
#check LeanPEP.ActualFunction.IsOneSmoothConvexAnalytic.oneStepGD_upper_at_update

namespace LeanPEP.ActualFunction.V12A4Smoke

open LeanPEP.ActualFunction

/-- The certificate-facing form consumes exactly the A3 feasibility
hypotheses and returns the actual function-value gap. -/
example
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {g : E → E} {xStar x0 x1 : E}
    (hfun : IsOneSmoothConvexAnalytic f g)
    (hstationary : g xStar = 0)
    (hstep : x1 = x0 - g x0)
    (hradius : inner ℝ (x0 - xStar) (x0 - xStar) ≤ 1) :
    f x1 - f xStar ≤ (1 : ℝ) / 6 :=
  hfun.oneStepGD_upper_of_inner_radius hstationary hstep hradius

/-- The standard norm-squared statement is available as the public theorem
surface. -/
example
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {g : E → E} {xStar x0 x1 : E}
    (hfun : IsOneSmoothConvexAnalytic f g)
    (hstationary : g xStar = 0)
    (hstep : x1 = x0 - g x0)
    (hradius : ‖x0 - xStar‖ ^ 2 ≤ 1) :
    f x1 - f xStar ≤ (1 : ℝ) / 6 :=
  hfun.oneStepGD_upper hstationary hstep hradius

/-- The update can also be substituted directly. -/
example
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {g : E → E} {xStar x0 : E}
    (hfun : IsOneSmoothConvexAnalytic f g)
    (hstationary : g xStar = 0)
    (hradius : ‖x0 - xStar‖ ^ 2 ≤ 1) :
    f (x0 - g x0) - f xStar ≤ (1 : ℝ) / 6 :=
  hfun.oneStepGD_upper_at_update hstationary hradius

end LeanPEP.ActualFunction.V12A4Smoke
