import LeanPEP.Imported.CompositeBoundedCompletionRegression
import LeanPEP.ActualFunction.ProximalGradientCompletionAudit

/-! D11 uses the EXISTING D10 actual-function bridge. The box solver and its
coefficient compiler do not participate in this upper-bound proof. -/
noncomputable section
open scoped NNReal
namespace LeanPEP.ActualFunction.ProximalGradientBoundedCompletionAudit
open LeanPEP.GramPEP

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem three_step_upper [CompleteSpace E]
    {L : ℝ≥0} {R : ℝ} {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsSmoothConvexAnalytic L f g) (hh : ConvexOn ℝ Set.univ h)
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar + h xStar ≤ f y + h y)
    (hrun : ProximalGradientScaling.IsSmoothProxRun 3 L h g x)
    (hradius : ‖x 0 - xStar‖ ^ 2 ≤ R ^ 2) :
    f (x 3) + h (x 3) - (f xStar + h xStar) ≤ (L : ℝ) * R ^ 2 / 12 := by
  have hout := ProximalGradientCompletionAudit.upper_analytic
    Imported.CompositeBoundedCompletion.PGThree.sourceQ
    Imported.CompositeBoundedCompletion.PGThree.traceQ
    Imported.CompositeBoundedCompletion.PGThree.policyQ
    Imported.CompositeBoundedCompletion.PGThree.rawUpperQ
    Imported.CompositeBoundedCompletion.PGThree.reconstructedUpperQ
    Imported.CompositeBoundedCompletion.PGThree.completedUpperQ
    Imported.CompositeBoundedCompletion.PGThree.completed_check
    hf hh hL hR hmin hrun hradius
  have hb : (Imported.CompositeBoundedCompletion.PGThree.completedUpperQ.bound : ℝ) = 1/12 := by
    norm_num [Imported.CompositeBoundedCompletion.PGThree.completedUpperQ]
  rw [hb] at hout
  calc
    f (x 3) + h (x 3) - (f xStar + h xStar) ≤ (L : ℝ) * R ^ 2 * (1/12) := hout
    _ = (L : ℝ) * R ^ 2 / 12 := by ring

end LeanPEP.ActualFunction.ProximalGradientBoundedCompletionAudit
