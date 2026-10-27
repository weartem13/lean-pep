import LeanPEP.ActualFunction.ProximalGradientReconstructionAuditCore
import LeanPEP.Adapters.ProximalGradientReconstruction
import LeanPEP.Imported.CompositeCandidatesRegression
import LeanPEP.ActualFunction.ProximalGradientSparseAudit

/-! D8: only the bound of the independently accepted candidate is used.
An error budget is NOT an extra error term in the rate, nor does acceptance
of a reconstructed candidate imply acceptance of the original decimal data. -/
noncomputable section
open scoped NNReal
namespace LeanPEP.ActualFunction.ProximalGradientReconstructionAudit
open LeanPEP.GramPEP LeanPEP.GramPEP.RationalReconstructionAudit
open LeanPEP.Adapters.ProximalGradientSparse (SourceQ)
open LeanPEP.Adapters.ProximalGradientReconstruction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem three_step_upper [CompleteSpace E]
    {L : ℝ≥0} {R : ℝ} {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsSmoothConvexAnalytic L f g) (hh : ConvexOn ℝ Set.univ h)
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar + h xStar ≤ f y + h y)
    (hrun : ProximalGradientScaling.IsSmoothProxRun 3 L h g x)
    (hradius : ‖x 0-xStar‖^2 ≤ R^2) :
    f (x 3) + h (x 3) - (f xStar + h xStar) ≤ (L : ℝ)*R^2/12 := by
  have hout := upper_analytic Imported.CompositeCandidates.PGThree.sourceQ
    Imported.CompositeCandidates.PGThree.policyQ Imported.CompositeCandidates.PGThree.rawUpperQ
    Imported.CompositeCandidates.PGThree.reconstructedUpperQ Imported.CompositeCandidates.PGThree.reconstructed_check
    hf hh hL hR hmin hrun hradius
  have hb : (Imported.CompositeCandidates.PGThree.reconstructedUpperQ.bound : ℝ) = 1/12 := by
    norm_num [Imported.CompositeCandidates.PGThree.reconstructedUpperQ]
  rw [hb] at hout
  calc
    f (x 3) + h (x 3) - (f xStar + h xStar) ≤ (L : ℝ)*R^2*(1/12) := hout
    _ = (L : ℝ)*R^2/12 := by ring

end LeanPEP.ActualFunction.ProximalGradientReconstructionAudit
