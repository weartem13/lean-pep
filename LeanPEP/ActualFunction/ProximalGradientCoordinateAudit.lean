import LeanPEP.ActualFunction.ProximalGradientCoordinateAuditCore
import LeanPEP.Adapters.ProximalGradientCoordinates
import LeanPEP.Imported.CompositeCoordinatesRegression
import LeanPEP.ActualFunction.ProximalGradientSourceAudit

/-!
# D3: coordinate-audited native certificates applied to actual PG runs

The old D2 source binding and C5/C4 actual-function bridge are reused without
modification. This is an exact typed-coordinate boundary, not a live capture or
producer authentication claim. No new rate or tightness is asserted.
-/

noncomputable section
open scoped NNReal
namespace LeanPEP.ActualFunction.ProximalGradientCoordinateAudit

open LeanPEP.GramPEP
open LeanPEP.Adapters.ProximalGradientCoordinates
open LeanPEP.Imported.CompositeCoordinates

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

end LeanPEP.ActualFunction.ProximalGradientCoordinateAudit
