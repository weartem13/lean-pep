import LeanPEP.ActualFunction.ProximalGradientSourceAuditCore
import LeanPEP.Adapters.ProximalGradientSource
import LeanPEP.Imported.CompositeSourceRegression
import LeanPEP.ActualFunction.ProximalGradientMinimizer

/-!
# D2: source-bound imported certificates applied to actual composite functions

No live provenance, source parser correctness, coordinate conversion, or finite
primal interpolation completeness is assumed. The composite snapshot is checked
against the old compiler before certificate equality transport. The existing C5
minimizer and C4 scaling bridges supply the actual-function interpretation.
-/

noncomputable section
open scoped NNReal
namespace LeanPEP.ActualFunction.ProximalGradientSourceAudit

open LeanPEP.GramPEP
open LeanPEP.Adapters.ProximalGradientSource
open LeanPEP.Imported.CompositeSource

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem three_step_upper [CompleteSpace E]
    {L : ℝ≥0} {R : ℝ} {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsSmoothConvexAnalytic L f g) (hh : ConvexOn ℝ Set.univ h)
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar + h xStar ≤ f y + h y)
    (hrun : ProximalGradientScaling.IsSmoothProxRun 3 L h g x)
    (hradius : ‖x 0-xStar‖^2 ≤ R^2) :
    f (x 3) + h (x 3) - (f xStar + h xStar) ≤ (L : ℝ)*R^2/12 := by
  have hout := upper_analytic PGThree.sourceQ PGThree.upperQ PGThree.bound_check
    hf hh hL hR hmin hrun hradius
  have hb : (PGThree.upperQ.bound : ℝ) = 1/12 := by norm_num [PGThree.upperQ]
  rw [hb] at hout
  calc
    f (x 3) + h (x 3) - (f xStar + h xStar) ≤ (L : ℝ)*R^2*(1/12) := hout
    _ = (L : ℝ)*R^2/12 := by ring

end LeanPEP.ActualFunction.ProximalGradientSourceAudit
