import LeanPEP.Adapters.ProximalGradientSource
import LeanPEP.ActualFunction.ProximalGradientMinimizerCore

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

/-- Source binding AND local certificate validity are necessary. The conclusion
is about old expected-model feasible data, not a producer-selected feasible set. -/
theorem finite_upper {n : ℕ} (s : SourceQ n) (c : UpperCertQ s.model)
    (hc : checkBoundQ s c = true)
    (d : DataR (Fin (Profiles.ProximalGradient.valueCount n)) (Profiles.ProximalGradient.basisCount n))
    (hpsd : IsGramPosSemidef d.gram)
    (hcon : AssumptionsFeasibleR (Profiles.ProximalGradient.modelQ n) d) :
    (Profiles.ProximalGradient.objectiveQ n).evalR d ≤ (c.bound : ℝ) := by
  obtain ⟨c', hu, hi, ho, hb⟩ := checked_certificate s c hc
  have hout := Profiles.ProximalGradient.certificate_upper c' hu hi ho d hpsd hcon
  rw [hb] at hout
  exact hout

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Arbitrary positive horizon: the imported bound is not required to match a
known closed-form bound, but the ORIGINAL composite problem is fixed by audit. -/
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
  obtain ⟨c', hu, hi, ho, hb⟩ := checked_certificate s c hc
  have hout := ProximalGradientScaling.certificate_upper_of_minimizer
    c' hu hi ho hf hh hL hR hmin hrun hradius
  rw [hb] at hout
  exact hout

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

end LeanPEP.ActualFunction.ProximalGradientSourceAudit
