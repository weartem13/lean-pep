import LeanPEP.Adapters.ProximalGradientCompletion
import LeanPEP.Imported.CompositeCompletionRegression
import LeanPEP.ActualFunction.ProximalGradientCaptureAudit

/-! D10: independently accepted fixed-residual completions use the unchanged D9
actual-function theorem, with the completed bound and no extra error term. -/
noncomputable section
open scoped NNReal
namespace LeanPEP.ActualFunction.ProximalGradientCompletionAudit
open LeanPEP.GramPEP LeanPEP.GramPEP.RationalReconstructionAudit
open LeanPEP.Adapters.ProximalGradientSparse (SourceQ)
open LeanPEP.Adapters.ProximalGradientCapture (TraceQ)
open LeanPEP.Adapters.ProximalGradientCompletion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem upper_firstOrder {n k : ℕ} (s : SourceQ n k) (t : TraceQ n k) (policy : PolicyQ)
    (raw seed completed : UpperCertQ s.model)
    (hc : checkCompletedQ s t policy raw seed completed = true)
    {L : ℝ≥0} {R : ℝ} {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsSmoothConvexFirstOrder L f g) (hh : ConvexOn ℝ Set.univ h)
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar + h xStar ≤ f y + h y)
    (hrun : ProximalGradientScaling.IsSmoothProxRun (n+1) L h g x)
    (hradius : ‖x 0 - xStar‖ ^ 2 ≤ R ^ 2) :
    f (x (n+1)) + h (x (n+1)) - (f xStar + h xStar) ≤ (L : ℝ) * R ^ 2 * (completed.bound : ℝ) :=
  ProximalGradientCaptureAudit.upper_firstOrder s t policy raw completed
    (captured_check s t policy raw seed completed hc) hf hh hL hR hmin hrun hradius

theorem upper_analytic [CompleteSpace E] {n k : ℕ} (s : SourceQ n k) (t : TraceQ n k)
    (policy : PolicyQ) (raw seed completed : UpperCertQ s.model)
    (hc : checkCompletedQ s t policy raw seed completed = true)
    {L : ℝ≥0} {R : ℝ} {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsSmoothConvexAnalytic L f g) (hh : ConvexOn ℝ Set.univ h)
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar + h xStar ≤ f y + h y)
    (hrun : ProximalGradientScaling.IsSmoothProxRun (n+1) L h g x)
    (hradius : ‖x 0 - xStar‖ ^ 2 ≤ R ^ 2) :
    f (x (n+1)) + h (x (n+1)) - (f xStar + h xStar) ≤ (L : ℝ) * R ^ 2 * (completed.bound : ℝ) :=
  upper_firstOrder s t policy raw seed completed hc hf.toFirstOrder hh hL hR hmin hrun hradius

theorem three_step_upper [CompleteSpace E]
    {L : ℝ≥0} {R : ℝ} {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsSmoothConvexAnalytic L f g) (hh : ConvexOn ℝ Set.univ h)
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar + h xStar ≤ f y + h y)
    (hrun : ProximalGradientScaling.IsSmoothProxRun 3 L h g x)
    (hradius : ‖x 0 - xStar‖ ^ 2 ≤ R ^ 2) :
    f (x 3) + h (x 3) - (f xStar + h xStar) ≤ (L : ℝ) * R ^ 2 / 12 := by
  have hout := upper_analytic Imported.CompositeCompletion.PGThree.sourceQ
    Imported.CompositeCompletion.PGThree.traceQ Imported.CompositeCompletion.PGThree.policyQ
    Imported.CompositeCompletion.PGThree.rawUpperQ Imported.CompositeCompletion.PGThree.reconstructedUpperQ
    Imported.CompositeCompletion.PGThree.completedUpperQ Imported.CompositeCompletion.PGThree.completed_check
    hf hh hL hR hmin hrun hradius
  have hb : (Imported.CompositeCompletion.PGThree.completedUpperQ.bound : ℝ) = 1/12 := by
    norm_num [Imported.CompositeCompletion.PGThree.completedUpperQ]
  rw [hb] at hout
  calc
    f (x 3) + h (x 3) - (f xStar + h xStar) ≤ (L : ℝ) * R ^ 2 * (1/12) := hout
    _ = (L : ℝ) * R ^ 2 / 12 := by ring

end LeanPEP.ActualFunction.ProximalGradientCompletionAudit
