import LeanPEP.Profiles.ProximalGradient
import LeanPEP.Profiles.ProximalGradientOneStep

/-! # Exact migration of the existing one-step composite model

`n = 0` in the positive-horizon compiler means ONE update. No certificate
is regenerated: after proving model/objective equality, the existing C1
certificate and finite tightness theorem are transported unchanged.
-/

namespace LeanPEP.Profiles.ProximalGradient

open LeanPEP.GramPEP

private theorem sample_ext {p m : ℕ} {a b : Composite.SampleQ p m}
    (hv : a.valueIndex = b.valueIndex) (hp : a.position = b.position)
    (ho : a.oracle = b.oracle) : a = b := by
  cases a
  cases b
  cases hv
  cases hp
  cases ho
  rfl

/-- Exact value-slot, point, and gradient ordering at one step. -/
theorem smoothSamplesQ_zero : smoothSamplesQ 0 = ProximalGradientOneStep.smoothSamplesQ := by
  funext i
  apply sample_ext
  · fin_cases i <;> decide +kernel
  · funext r
    fin_cases i <;> fin_cases r <;> decide +kernel
  · funext r
    fin_cases i <;> fin_cases r <;> decide +kernel

/-- In particular, star subgradient is -g_star, not zero. -/
theorem nonsmoothSamplesQ_zero :
    nonsmoothSamplesQ 0 = ProximalGradientOneStep.nonsmoothSamplesQ := by
  funext i
  apply sample_ext
  · fin_cases i <;> decide +kernel
  · funext r
    fin_cases i <;> fin_cases r <;> decide +kernel
  · funext r
    fin_cases i <;> fin_cases r <;> decide +kernel

theorem radiusExprQ_zero : radiusExprQ 0 = ProximalGradientOneStep.radiusExprQ :=
  checkLinearExprEqQ_sound _ _ (by decide +kernel)

theorem objectiveQ_zero : objectiveQ 0 = ProximalGradientOneStep.objectiveQ :=
  checkLinearExprEqQ_sound _ _ (by decide +kernel)

/-- Entire compiled model equality, including all 14 constraints in order. -/
theorem modelQ_zero : modelQ 0 = ProximalGradientOneStep.modelQ := by
  apply ModelQ.ext
  · rfl
  · rfl
  · rw [modelQ_constraints, ProximalGradientOneStep.modelQ_constraints] <;>
      simp only [smoothSamplesQ_zero, nonsmoothSamplesQ_zero, radiusExprQ_zero]

theorem oneStep_exact_certificate :
    ∃ c : UpperCertQ (modelQ 0), c.bound = (1 : ℚ) / 4 ∧
      c.objective = objectiveQ 0 ∧ c.interpTerms = [] ∧ checkUpperCertQ c = true := by
  rw [modelQ_zero, objectiveQ_zero]
  exact ⟨ProximalGradientOneStep.upperCertQ, rfl, rfl, rfl,
    ProximalGradientOneStep.upperCertQ_check⟩

/-- No actual-function existence is inferred from this finite set. -/
def finiteValues (n : ℕ) : Set ℝ :=
  {r | ∃ d : DataR (Fin (valueCount n)) (basisCount n), IsGramPosSemidef d.gram ∧
    AssumptionsFeasibleR (modelQ n) d ∧ (objectiveQ n).evalR d = r}

theorem oneStep_finite_tight : IsGreatest (finiteValues 0) ((1 : ℝ) / 4) := by
  simpa only [finiteValues, modelQ_zero, objectiveQ_zero,
    ProximalGradientOneStep.finiteValues] using ProximalGradientOneStep.finite_tight

end LeanPEP.Profiles.ProximalGradient
