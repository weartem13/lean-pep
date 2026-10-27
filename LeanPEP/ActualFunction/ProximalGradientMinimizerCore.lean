import LeanPEP.ActualFunction.CompositeOptimality
import LeanPEP.ActualFunction.ProximalGradientScalingCore

/-! Generic certificate interface, moved unchanged; rate and witness applications
remain in the compatibility module. -/
noncomputable section
open scoped NNReal
namespace LeanPEP.ActualFunction.ProximalGradientScaling
open Proximal ProximalScaling SmoothScaling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The generic certificate still has all three guards, but the reference
point is supplied as an ordinary global minimizer rather than a subgradient. -/
theorem certificate_upper_of_minimizer {n : ℕ}
    (c : GramPEP.UpperCertQ (Profiles.ProximalGradient.modelQ n))
    (hc : GramPEP.checkUpperCertQ c = true) (hempty : c.interpTerms = [])
    (hobj : c.objective = Profiles.ProximalGradient.objectiveQ n)
    {L : ℝ≥0} {R : ℝ} {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsSmoothConvexFirstOrder L f g) (hh : ConvexOn ℝ Set.univ h)
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar + h xStar ≤ f y + h y)
    (hrun : IsSmoothProxRun (n+1) L h g x) (hradius : ‖x 0-xStar‖^2 ≤ R^2) :
    f (x (n+1)) + h (x (n+1)) - (f xStar + h xStar) ≤
      (L : ℝ)*R^2*(c.bound : ℝ) :=
  certificate_upper c hc hempty hobj hf hh hL hR
    (subgradient_of_composite_minimizer hf hh hmin) hrun hradius

end LeanPEP.ActualFunction.ProximalGradientScaling
