import LeanPEP.ActualFunction.OneStepGram

/-!
# One-step actual-function upper theorem

This file completes the v0.12A soundness bridge for the normalized one-step
unit-gradient method.  The previous layers provide:

* an analysis-facing contract for actual `1`-smooth convex functions;
* exact pairwise interpolation inequalities;
* an exact real Gram datum for the samples `(x★, x₀, x₁)`;
* positive semidefiniteness and every ordered interpolation constraint; and
* realization of the fixed one-step model and its radius assumption.

Here we feed that package to the already accepted exact rational upper
certificate `GramPEP.UpperCertificateExamples.oneStepUpperCertQ`.  The
certificate theorem returns the finite-datum objective bound, and the final
step reduces the datum's function-value fields back to the actual values
`f x₁` and `f x★`.

This proves a universal upper bound only.  It does not provide an actual lower
witness, interpolation completeness, or an exact worst-case theorem over the
actual function class.
-/

namespace LeanPEP
namespace ActualFunction
namespace IsOneSmoothConvexAnalytic

open GramPEP.UpperCertificateExamples

variable
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {g : E → E}

/-- Certificate-facing one-step upper theorem, with the initial radius written
as an inner-product square to match the exact Gram formulation. -/
theorem oneStepGD_upper_of_inner_radius
    (h : IsOneSmoothConvexAnalytic f g)
    {xStar x0 x1 : E}
    (hstationary : g xStar = 0)
    (hstep : x1 = x0 - g x0)
    (hradius : inner ℝ (x0 - xStar) (x0 - xStar) ≤ 1) :
    f x1 - f xStar ≤ (1 : ℝ) / 6 := by
  have hfeasible :=
    OneStepGram.oneStepData_feasible h hstationary hstep hradius
  have hcertificate :=
    oneStep_upper
      (OneStepGram.oneStepData f g xStar x0 x1)
      hfeasible.1 hfeasible.2.1 hfeasible.2.2
  simpa [OneStepGram.oneStepData, OneStepGram.oneStepSamples,
    FiniteGram.dataOfModel] using hcertificate

/-- Standard norm-squared form of the normalized one-step actual-function
upper theorem. -/
theorem oneStepGD_upper
    (h : IsOneSmoothConvexAnalytic f g)
    {xStar x0 x1 : E}
    (hstationary : g xStar = 0)
    (hstep : x1 = x0 - g x0)
    (hradius : ‖x0 - xStar‖ ^ 2 ≤ 1) :
    f x1 - f xStar ≤ (1 : ℝ) / 6 := by
  apply h.oneStepGD_upper_of_inner_radius hstationary hstep
  simpa [real_inner_self_eq_norm_sq] using hradius

/-- The same theorem with the unit-gradient update substituted directly into
the conclusion. -/
theorem oneStepGD_upper_at_update
    (h : IsOneSmoothConvexAnalytic f g)
    {xStar x0 : E}
    (hstationary : g xStar = 0)
    (hradius : ‖x0 - xStar‖ ^ 2 ≤ 1) :
    f (x0 - g x0) - f xStar ≤ (1 : ℝ) / 6 :=
  h.oneStepGD_upper hstationary rfl hradius

end IsOneSmoothConvexAnalytic
end ActualFunction
end LeanPEP
