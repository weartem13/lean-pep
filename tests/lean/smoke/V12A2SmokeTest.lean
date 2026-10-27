import LeanPEP

#check LeanPEP.ActualFunction.IsOneSmoothConvexAnalytic.lowerModel
#check LeanPEP.ActualFunction.IsOneSmoothConvexAnalytic.upperModel
#check LeanPEP.ActualFunction.IsOneSmoothConvexAnalytic.toFirstOrder
#check LeanPEP.ActualFunction.IsOneSmoothConvexAnalytic.interpolationSlack_nonneg
#check LeanPEP.ActualFunction.IsOneSmoothConvexAnalytic.pairwise_interpolation

namespace LeanPEP.ActualFunction.V12A2Smoke

open LeanPEP.ActualFunction

/-- The bridge theorem exposes the exact first-order contract without adding
it as an assumption to the analytic structure. -/
example
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {g : E → E}
    (h : IsOneSmoothConvexAnalytic f g) :
    IsOneSmoothConvexFirstOrder f g :=
  h.toFirstOrder

/-- The analytic interface now reaches the pairwise PEP interpolation
inequality directly. -/
example
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {g : E → E}
    (h : IsOneSmoothConvexAnalytic f g) (x y : E) :
    0 ≤ interpolationSlack f g x y :=
  h.interpolationSlack_nonneg x y

end LeanPEP.ActualFunction.V12A2Smoke
