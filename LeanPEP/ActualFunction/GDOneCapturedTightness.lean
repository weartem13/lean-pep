import LeanPEP.Imported.C14GDOneDual
import LeanPEP.Imported.C14GDOnePrimal
import LeanPEP.ActualFunction.HuberWitnessScaling
set_option autoImplicit false
noncomputable section
namespace LeanPEP.ActualFunction.GDOneCapturedTightness
open LeanPEP.GramPEP LeanPEP.GramPEP.UpperCertificateExamples
open LeanPEP.ActualFunction.GDOneCapture
open LeanPEP.Imported.C14GDOneDual
open scoped NNReal

/-- Equal symbolic problems from DIFFERENT recorded solves; no numerical trace equality. -/
theorem symbolic_source_same : sourceQ = LeanPEP.Imported.C14GDOnePrimal.sourceQ := rfl

theorem selected_bound_beta : structuredUpperQ.bound =
    LeanPEP.Adapters.GDOnePrimal.beta LeanPEP.Imported.C14GDOnePrimal.candidateQ := by
  rw [bound_exact, LeanPEP.Imported.C14GDOnePrimal.beta_value]

theorem finite_universal_upper (d : DataR (Fin 3) 3)
    (hm : RealizesModelQ oneStepModelQ d) (hc : CoreFeasible d)
    (ha : AssumptionsFeasibleR oneStepModelQ d) :
    oneStepObjectiveQ.evalR d ≤ (1/6 : ℝ) := by
  have h := checkUpperCertQ_sound_real (centered structuredUpperQ) centered_check d hm hc ha
  change oneStepObjectiveQ.evalR d ≤ (structuredUpperQ.bound : ℝ) at h
  rw [bound_exact] at h
  norm_num at h ⊢
  exact h

abbrev externalPrimalQ := LeanPEP.Imported.C14GDOnePrimal.canonicalQ

theorem external_primal_attainment :
    RealizesModelQ oneStepModelQ (castDataQ externalPrimalQ) ∧
    CoreFeasible (castDataQ externalPrimalQ) ∧
    AssumptionsFeasibleR oneStepModelQ (castDataQ externalPrimalQ) ∧
    oneStepObjectiveQ.evalR (castDataQ externalPrimalQ) = (1/6 : ℝ) := by
  have hf := LeanPEP.Imported.C14GDOnePrimal.finite_primal_verified
  have hv := LeanPEP.Imported.C14GDOnePrimal.objective_verified
  rw [LeanPEP.Imported.C14GDOnePrimal.beta_value] at hv
  exact ⟨hf.1,hf.2.1,hf.2.2,by simpa using hv.1⟩

theorem finite_tightness :
    (∀ d : DataR (Fin 3) 3, RealizesModelQ oneStepModelQ d → CoreFeasible d →
      AssumptionsFeasibleR oneStepModelQ d → oneStepObjectiveQ.evalR d ≤ (1/6 : ℝ)) ∧
    RealizesModelQ oneStepModelQ (castDataQ externalPrimalQ) ∧
    CoreFeasible (castDataQ externalPrimalQ) ∧
    AssumptionsFeasibleR oneStepModelQ (castDataQ externalPrimalQ) ∧
    oneStepObjectiveQ.evalR (castDataQ externalPrimalQ) = (1/6 : ℝ) :=
  ⟨finite_universal_upper, external_primal_attainment⟩

theorem current_certificate_actual_upper
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {L : ℝ≥0} {R : ℝ} {f : E → ℝ} {g : E → E} {xStar x0 x1 : E}
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar ≤ f y) (hstep : x1 = x0-(L : ℝ)⁻¹ • g x0)
    (hradius : ‖x0-xStar‖^2 ≤ R^2) : f x1-f xStar ≤ (L : ℝ)*R^2/6 := by
  have h := LeanPEP.Imported.C14GDOneDual.actual_upper hf hL hR hmin hstep hradius
  rw [bound_exact] at h
  norm_num at h ⊢
  nlinarith

open HuberWitness

theorem analytic_witness_verified {L : ℝ≥0} {R : ℝ}
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) :
    ∃ (f g : ℝ → ℝ) (xStar x0 x1 : ℝ),
      IsSmoothConvexAnalytic L f g ∧ (∀ y, f xStar ≤ f y) ∧
      x1 = x0-(L : ℝ)⁻¹ • g x0 ∧ ‖x0-xStar‖^2 ≤ R^2 ∧
      f x1-f xStar = (L : ℝ)*R^2/6 := by
  refine ⟨scaledWitnessFunction 1 L R, scaledWitnessGradient 1 L R,
    0, scaledWitnessPoint 1 R 0, scaledWitnessPoint 1 R 1,
    scaledWitness_analytic 1 L R, scaledWitness_zero_isGlobalMin 1 L hR,
    scaledWitnessPoint_smoothGD_step 1 hL hR 0 (by omega), ?_, ?_⟩
  · simpa using le_of_eq (scaledWitness_initialRadius hR)
  · have h := scaledWitness_smoothGD_attains_closed_form 1 hL hR
    rw [smoothGDIterate_final 1 hL hR] at h
    norm_num at h ⊢
    exact h

theorem analytic_witness_values (L : ℝ≥0) {R : ℝ} (hR : 0 ≤ R) :
    scaledWitnessPoint 1 R 0 = R ∧ scaledWitnessPoint 1 R 1 = 2*R/3 ∧
    scaledWitnessFunction 1 L R 0 = 0 ∧
    scaledWitnessGradient 1 L R R = (L : ℝ)*R/3 ∧
    scaledWitnessFunction 1 L R R = 5*(L : ℝ)*R^2/18 ∧
    scaledWitnessFunction 1 L R (2*R/3) = (L : ℝ)*R^2/6 := by
  have ht : scaledThreshold 1 R = R/3 := by norm_num [scaledThreshold,threshold]; ring
  have hp : scaledWitnessPoint 1 R 1 = 2*R/3 := by
    norm_num [scaledWitnessPoint,witnessPoint,threshold]; ring
  refine ⟨scaledWitnessPoint_zero 1 R, hp, scaledWitnessFunction_zero 1 L hR, ?_, ?_, ?_⟩
  · unfold scaledWitnessGradient
    rw [ht,huberGradient_of_ge (by linarith : R/3 ≤ R)]
    ring
  · unfold scaledWitnessFunction
    rw [ht,huberFunction_of_ge (by linarith : R/3 ≤ R)]
    ring
  · unfold scaledWitnessFunction
    rw [ht,huberFunction_of_ge (by linarith : R/3 ≤ 2*R/3)]
    ring

theorem actual_tightness
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {L : ℝ≥0} {R : ℝ} (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) :
    (∀ (f : E → ℝ) (g : E → E) (xStar x0 x1 : E), IsSmoothConvexAnalytic L f g →
      (∀ y, f xStar ≤ f y) → x1 = x0-(L : ℝ)⁻¹ • g x0 → ‖x0-xStar‖^2 ≤ R^2 →
      f x1-f xStar ≤ (L : ℝ)*R^2/6) ∧
    ∃ (f g : ℝ → ℝ) (xStar x0 x1 : ℝ), IsSmoothConvexAnalytic L f g ∧
      (∀ y, f xStar ≤ f y) ∧ x1 = x0-(L : ℝ)⁻¹ • g x0 ∧ ‖x0-xStar‖^2 ≤ R^2 ∧
      f x1-f xStar = (L : ℝ)*R^2/6 :=
  ⟨fun _ _ _ _ _ hf hm hs hr => current_certificate_actual_upper hf hL hR hm hs hr,
    analytic_witness_verified hL hR⟩
end LeanPEP.ActualFunction.GDOneCapturedTightness
