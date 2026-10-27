import LeanPEP.Adapters.ProximalGradientReconstruction
import LeanPEP.ActualFunction.ProximalGradientSparseAuditCore

/-! D8: only the bound of the independently accepted candidate is used.
An error budget is NOT an extra error term in the rate, nor does acceptance
of a reconstructed candidate imply acceptance of the original decimal data. -/
noncomputable section
open scoped NNReal
namespace LeanPEP.ActualFunction.ProximalGradientReconstructionAudit
open LeanPEP.GramPEP LeanPEP.GramPEP.RationalReconstructionAudit
open LeanPEP.Adapters.ProximalGradientSparse (SourceQ)
open LeanPEP.Adapters.ProximalGradientReconstruction

theorem finite_upper {n k : ℕ} (s : SourceQ n k) (policy : PolicyQ)
    (raw reconstructed : UpperCertQ s.model)
    (hc : checkReconstructedQ s policy raw reconstructed = true)
    (d : DataR (Fin (Profiles.ProximalGradient.valueCount n)) (Profiles.ProximalGradient.basisCount n))
    (hpsd : IsGramPosSemidef d.gram)
    (hcon : AssumptionsFeasibleR (Profiles.ProximalGradient.modelQ n) d) :
    (Profiles.ProximalGradient.objectiveQ n).evalR d ≤ (reconstructed.bound : ℝ) :=
  ProximalGradientSparseAudit.finite_upper s reconstructed
    (reconstructed_bound_check s policy raw reconstructed hc) d hpsd hcon

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem upper_firstOrder {n k : ℕ} (s : SourceQ n k) (policy : PolicyQ)
    (raw reconstructed : UpperCertQ s.model)
    (hc : checkReconstructedQ s policy raw reconstructed = true)
    {L : ℝ≥0} {R : ℝ} {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsSmoothConvexFirstOrder L f g) (hh : ConvexOn ℝ Set.univ h)
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar + h xStar ≤ f y + h y)
    (hrun : ProximalGradientScaling.IsSmoothProxRun (n+1) L h g x)
    (hradius : ‖x 0-xStar‖^2 ≤ R^2) :
    f (x (n+1)) + h (x (n+1)) - (f xStar + h xStar) ≤
      (L : ℝ)*R^2*(reconstructed.bound : ℝ) :=
  ProximalGradientSparseAudit.upper_firstOrder s reconstructed
    (reconstructed_bound_check s policy raw reconstructed hc) hf hh hL hR hmin hrun hradius

theorem upper_analytic [CompleteSpace E] {n k : ℕ} (s : SourceQ n k) (policy : PolicyQ)
    (raw reconstructed : UpperCertQ s.model)
    (hc : checkReconstructedQ s policy raw reconstructed = true)
    {L : ℝ≥0} {R : ℝ} {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsSmoothConvexAnalytic L f g) (hh : ConvexOn ℝ Set.univ h)
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar + h xStar ≤ f y + h y)
    (hrun : ProximalGradientScaling.IsSmoothProxRun (n+1) L h g x)
    (hradius : ‖x 0-xStar‖^2 ≤ R^2) :
    f (x (n+1)) + h (x (n+1)) - (f xStar + h xStar) ≤
      (L : ℝ)*R^2*(reconstructed.bound : ℝ) :=
  upper_firstOrder s policy raw reconstructed hc hf.toFirstOrder hh hL hR hmin hrun hradius

theorem raw_upper_firstOrder {n k : ℕ} (s : SourceQ n k) (raw : UpperCertQ s.model)
    (hc : checkRawQ s raw = true)
    {L : ℝ≥0} {R : ℝ} {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsSmoothConvexFirstOrder L f g) (hh : ConvexOn ℝ Set.univ h)
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar + h xStar ≤ f y + h y)
    (hrun : ProximalGradientScaling.IsSmoothProxRun (n+1) L h g x)
    (hradius : ‖x 0-xStar‖^2 ≤ R^2) :
    f (x (n+1)) + h (x (n+1)) - (f xStar + h xStar) ≤ (L : ℝ)*R^2*(raw.bound : ℝ) :=
  ProximalGradientSparseAudit.upper_firstOrder s raw hc hf hh hL hR hmin hrun hradius

end LeanPEP.ActualFunction.ProximalGradientReconstructionAudit
