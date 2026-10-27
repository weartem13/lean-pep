import LeanPEP

open LeanPEP

#check LeanPEP.ActualFunction.IsOneSmoothConvexAnalytic
#check LeanPEP.ActualFunction.IsOneSmoothConvexFirstOrder
#check LeanPEP.ActualFunction.IsOneSmoothConvexAnalytic.gradient_eq
#check LeanPEP.ActualFunction.IsOneSmoothConvexAnalytic.differentiable
#check LeanPEP.ActualFunction.interpolationSlack
#check LeanPEP.ActualFunction.interpolationSlack_nonneg
#check LeanPEP.ActualFunction.pairwise_interpolation

namespace LeanPEP.ActualFunction.V12A1Smoke

/-- The zero function with zero gradient satisfies both exact first-order
models on every real inner-product space. -/
def zeroFirstOrder
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    IsOneSmoothConvexFirstOrder
      (fun _ : E => 0)
      (fun _ : E => 0) := by
  constructor
  · intro x y
    simp
  · intro x y
    have hinner : 0 ≤ inner ℝ (y - x) (y - x) := real_inner_self_nonneg
    simpa using
      mul_nonneg (by norm_num : 0 ≤ ((1 : ℝ) / 2)) hinner

/-- The new theorem is usable on a concrete actual-function contract. -/
example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) :
    0 ≤ interpolationSlack (fun _ : E => 0) (fun _ : E => 0) x y :=
  interpolationSlack_nonneg zeroFirstOrder x y

end LeanPEP.ActualFunction.V12A1Smoke
