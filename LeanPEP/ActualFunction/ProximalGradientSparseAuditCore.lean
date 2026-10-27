import LeanPEP.Adapters.ProximalGradientSparse
import LeanPEP.ActualFunction.ProximalGradientPerformanceAuditCore

/-! D7: exact zero-row coverage, followed by the unchanged D6 through D2
actual-function chain. No new rate, solver claim, or arbitrary row completion. -/
noncomputable section
open scoped NNReal
namespace LeanPEP.ActualFunction.ProximalGradientSparseAudit

open LeanPEP.GramPEP
open LeanPEP.Adapters.ProximalGradientSparse

theorem finite_upper {n k : ℕ} (s : SourceQ n k) (c : UpperCertQ s.model)
    (hc : checkBoundQ s c = true)
    (d : DataR (Fin (Profiles.ProximalGradient.valueCount n)) (Profiles.ProximalGradient.basisCount n))
    (hpsd : IsGramPosSemidef d.gram)
    (hcon : AssumptionsFeasibleR (Profiles.ProximalGradient.modelQ n) d) :
    (Profiles.ProximalGradient.objectiveQ n).evalR d ≤ (c.bound : ℝ) := by
  have ht := ((checkBoundQ_eq_true_iff s c).mp hc).2.2.2.2
  exact ProximalGradientPerformanceAudit.finite_upper (completedSourceQ s) (completedUpperQ s c) ht d hpsd hcon

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem upper_firstOrder {n k : ℕ} (s : SourceQ n k) (c : UpperCertQ s.model)
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
  exact ProximalGradientPerformanceAudit.upper_firstOrder (completedSourceQ s) (completedUpperQ s c)
    ht hf hh hL hR hmin hrun hradius

theorem upper_analytic [CompleteSpace E] {n k : ℕ} (s : SourceQ n k) (c : UpperCertQ s.model)
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

end LeanPEP.ActualFunction.ProximalGradientSparseAudit
