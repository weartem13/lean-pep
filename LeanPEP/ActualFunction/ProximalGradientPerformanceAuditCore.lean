import LeanPEP.Adapters.ProximalGradientPerformance
import LeanPEP.ActualFunction.ProximalGradientRowAuditCore

/-! D6: checked single-performance lifting, followed by the unchanged D5/D4/D3/D2
actual-function chain. No new rate and no unverified solver-dual normalization. -/
noncomputable section
open scoped NNReal
namespace LeanPEP.ActualFunction.ProximalGradientPerformanceAudit

open LeanPEP.GramPEP
open LeanPEP.Adapters.ProximalGradientPerformance

theorem finite_upper {n : ℕ} (s : SourceQ n) (c : UpperCertQ s.model)
    (hc : checkBoundQ s c = true)
    (d : DataR (Fin (Profiles.ProximalGradient.valueCount n)) (Profiles.ProximalGradient.basisCount n))
    (hpsd : IsGramPosSemidef d.gram)
    (hcon : AssumptionsFeasibleR (Profiles.ProximalGradient.modelQ n) d) :
    (Profiles.ProximalGradient.objectiveQ n).evalR d ≤ (c.bound : ℝ) := by
  have ht := ((checkBoundQ_eq_true_iff s c).mp hc).2.2.2.2
  exact ProximalGradientRowAudit.finite_upper s.base (eliminatedUpperQ s c) ht d hpsd hcon

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem upper_firstOrder {n : ℕ} (s : SourceQ n) (c : UpperCertQ s.model)
    (hc : checkBoundQ s c = true)
    {L : ℝ≥0} {R : ℝ} {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsSmoothConvexFirstOrder L f g) (hh : ConvexOn ℝ Set.univ h)
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar + h xStar ≤ f y + h y)
    (hrun : ProximalGradientScaling.IsSmoothProxRun (n+1) L h g x)
    (hradius : ‖x 0-xStar‖^2 ≤ R^2) :
    f (x (n+1)) + h (x (n+1)) - (f xStar + h xStar) ≤
      (L : ℝ)*R^2*(c.bound : ℝ) := by
  have ht := ((checkBoundQ_eq_true_iff s c).mp hc).2.2.2.2
  exact ProximalGradientRowAudit.upper_firstOrder s.base (eliminatedUpperQ s c)
    ht hf hh hL hR hmin hrun hradius

theorem upper_analytic [CompleteSpace E] {n : ℕ} (s : SourceQ n) (c : UpperCertQ s.model)
    (hc : checkBoundQ s c = true)
    {L : ℝ≥0} {R : ℝ} {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsSmoothConvexAnalytic L f g) (hh : ConvexOn ℝ Set.univ h)
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar + h xStar ≤ f y + h y)
    (hrun : ProximalGradientScaling.IsSmoothProxRun (n+1) L h g x)
    (hradius : ‖x 0-xStar‖^2 ≤ R^2) :
    f (x (n+1)) + h (x (n+1)) - (f xStar + h xStar) ≤
      (L : ℝ)*R^2*(c.bound : ℝ) :=
  upper_firstOrder s c hc hf.toFirstOrder hh hL hR hmin hrun hradius

end LeanPEP.ActualFunction.ProximalGradientPerformanceAudit
