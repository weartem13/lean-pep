import LeanPEP.Adapters.ProximalGradientCapture
import LeanPEP.ActualFunction.ProximalGradientReconstructionAuditCore

/-! D9: bind captured symbolic/numerical endpoints, then use the unchanged D8
actual-function bridge. Fixtures are simulated, NOT live solver captures. -/
noncomputable section
open scoped NNReal
namespace LeanPEP.ActualFunction.ProximalGradientCaptureAudit
open LeanPEP.GramPEP LeanPEP.GramPEP.RationalReconstructionAudit
open LeanPEP.Adapters.ProximalGradientSparse (SourceQ)
open LeanPEP.Adapters.ProximalGradientCapture

theorem finite_upper {n k : ℕ} (s : SourceQ n k) (t : TraceQ n k) (policy : PolicyQ)
    (raw reconstructed : UpperCertQ s.model)
    (hc : checkCapturedQ s t policy raw reconstructed = true)
    (d : DataR (Fin (Profiles.ProximalGradient.valueCount n)) (Profiles.ProximalGradient.basisCount n))
    (hpsd : IsGramPosSemidef d.gram)
    (hcon : AssumptionsFeasibleR (Profiles.ProximalGradient.modelQ n) d) :
    (Profiles.ProximalGradient.objectiveQ n).evalR d ≤ (reconstructed.bound : ℝ) :=
  ProximalGradientReconstructionAudit.finite_upper s policy raw reconstructed
    (reconstructed_check s t policy raw reconstructed hc) d hpsd hcon

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem upper_firstOrder {n k : ℕ} (s : SourceQ n k) (t : TraceQ n k) (policy : PolicyQ)
    (raw reconstructed : UpperCertQ s.model)
    (hc : checkCapturedQ s t policy raw reconstructed = true)
    {L : ℝ≥0} {R : ℝ} {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsSmoothConvexFirstOrder L f g) (hh : ConvexOn ℝ Set.univ h)
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar + h xStar ≤ f y + h y)
    (hrun : ProximalGradientScaling.IsSmoothProxRun (n+1) L h g x)
    (hradius : ‖x 0-xStar‖^2 ≤ R^2) :
    f (x (n+1)) + h (x (n+1)) - (f xStar + h xStar) ≤
      (L : ℝ)*R^2*(reconstructed.bound : ℝ) :=
  ProximalGradientReconstructionAudit.upper_firstOrder s policy raw reconstructed
    (reconstructed_check s t policy raw reconstructed hc) hf hh hL hR hmin hrun hradius

theorem upper_analytic [CompleteSpace E] {n k : ℕ} (s : SourceQ n k) (t : TraceQ n k) (policy : PolicyQ)
    (raw reconstructed : UpperCertQ s.model)
    (hc : checkCapturedQ s t policy raw reconstructed = true)
    {L : ℝ≥0} {R : ℝ} {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsSmoothConvexAnalytic L f g) (hh : ConvexOn ℝ Set.univ h)
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar + h xStar ≤ f y + h y)
    (hrun : ProximalGradientScaling.IsSmoothProxRun (n+1) L h g x)
    (hradius : ‖x 0-xStar‖^2 ≤ R^2) :
    f (x (n+1)) + h (x (n+1)) - (f xStar + h xStar) ≤
      (L : ℝ)*R^2*(reconstructed.bound : ℝ) :=
  upper_firstOrder s t policy raw reconstructed hc hf.toFirstOrder hh hL hR hmin hrun hradius

theorem raw_upper_firstOrder {n k : ℕ} (s : SourceQ n k) (t : TraceQ n k) (raw : UpperCertQ s.model)
    (hc : checkCapturedRawQ s t raw = true)
    {L : ℝ≥0} {R : ℝ} {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsSmoothConvexFirstOrder L f g) (hh : ConvexOn ℝ Set.univ h)
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar + h xStar ≤ f y + h y)
    (hrun : ProximalGradientScaling.IsSmoothProxRun (n+1) L h g x)
    (hradius : ‖x 0-xStar‖^2 ≤ R^2) :
    f (x (n+1)) + h (x (n+1)) - (f xStar + h xStar) ≤ (L : ℝ)*R^2*(raw.bound : ℝ) :=
  ProximalGradientReconstructionAudit.raw_upper_firstOrder s raw (captured_raw_check s t raw hc) hf hh hL hR hmin hrun hradius

end LeanPEP.ActualFunction.ProximalGradientCaptureAudit
