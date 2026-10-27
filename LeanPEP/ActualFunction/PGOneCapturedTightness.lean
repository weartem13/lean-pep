import LeanPEP.Imported.C14PGOneUpper
import LeanPEP.Imported.C14PGOnePrimal
import LeanPEP.ActualFunction.ProximalGradientWitnessScaling

set_option autoImplicit false
noncomputable section
namespace LeanPEP.ActualFunction.PGOneCapturedTightness
open LeanPEP.GramPEP
open LeanPEP.Imported.C14PGOneUpper
open scoped NNReal

/-- Both retained endpoint modules have the same full source, including origin,
value maps, ordered rows, zero-row coverage and native tau direction. -/
theorem selected_source_same :
    sourceQ = LeanPEP.Imported.C14PGOnePrimal.sourceQ := rfl

theorem selected_trace_same :
    traceQ = LeanPEP.Imported.C14PGOnePrimal.traceQ := rfl

theorem selected_bound_beta : structuredUpperQ.bound =
    LeanPEP.Adapters.PGOnePrimal.beta LeanPEP.Imported.C14PGOnePrimal.candidateQ := by
  rw [structured_bound, LeanPEP.Imported.C14PGOnePrimal.beta_value]

/-- This upper comes from the CURRENT captured/checker-accepted external dual.
The fixed-rate certificate or a historical finite-tightness theorem is not used. -/
theorem finite_universal_upper (d : DataR (Fin 5) 5)
    (hp : IsGramPosSemidef d.gram)
    (ha : AssumptionsFeasibleR (Profiles.ProximalGradient.modelQ 0) d) :
    (Profiles.ProximalGradient.objectiveQ 0).evalR d ≤ (1/4 : ℝ) := by
  obtain ⟨c, hc, hi, ho, hb⟩ :=
    LeanPEP.Adapters.ProximalGradientCapture.checked_certificate
      sourceQ traceQ policyQ rawUpperQ structuredUpperQ structured_check
  have h := Profiles.ProximalGradient.certificate_upper c hc hi ho d hp ha
  rw [hb, structured_bound] at h
  norm_num at h ⊢
  exact h

abbrev externalPrimalQ := LeanPEP.Imported.C14PGOnePrimal.canonicalQ

theorem external_primal_attainment :
    IsGramPosSemidef (castDataQ externalPrimalQ).gram ∧
    AssumptionsFeasibleR (Profiles.ProximalGradient.modelQ 0) (castDataQ externalPrimalQ) ∧
    (Profiles.ProximalGradient.objectiveQ 0).evalR (castDataQ externalPrimalQ) = (1/4 : ℝ) := by
  have hf := LeanPEP.Imported.C14PGOnePrimal.finite_primal_verified
  have hv := LeanPEP.Imported.C14PGOnePrimal.objective_verified
  rw [LeanPEP.Imported.C14PGOnePrimal.beta_value] at hv
  exact ⟨hf.1, hf.2, by simpa using hv.1⟩

theorem finite_tightness :
    (∀ d : DataR (Fin 5) 5, IsGramPosSemidef d.gram →
      AssumptionsFeasibleR (Profiles.ProximalGradient.modelQ 0) d →
      (Profiles.ProximalGradient.objectiveQ 0).evalR d ≤ (1/4 : ℝ)) ∧
    IsGramPosSemidef (castDataQ externalPrimalQ).gram ∧
    AssumptionsFeasibleR (Profiles.ProximalGradient.modelQ 0) (castDataQ externalPrimalQ) ∧
    (Profiles.ProximalGradient.objectiveQ 0).evalR (castDataQ externalPrimalQ) = (1/4 : ℝ) :=
  ⟨finite_universal_upper, external_primal_attainment⟩

theorem current_certificate_actual_upper
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {L : ℝ≥0} {R : ℝ} {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsSmoothConvexAnalytic L f g) (hh : ConvexOn ℝ Set.univ h)
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar + h xStar ≤ f y + h y)
    (hrun : ProximalGradientScaling.IsSmoothProxRun 1 L h g x)
    (hradius : ‖x 0-xStar‖^2 ≤ R^2) :
    f (x 1)+h (x 1)-(f xStar+h xStar) ≤ (L : ℝ)*R^2/4 := by
  have hu := LeanPEP.Imported.C14PGOneUpper.actual_upper hf hh hL hR hmin hrun hradius
  rw [structured_bound] at hu
  norm_num at hu ⊢
  nlinarith

/-- The lower side is the old explicit ANALYTIC witness, not a realization of
externalPrimalQ. This record includes exactly the universal upper's contract. -/
theorem analytic_witness_verified {L : ℝ≥0} {R : ℝ}
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) :
    ∃ (f h g : ℝ → ℝ) (xStar : ℝ) (x : ℕ → ℝ),
      IsSmoothConvexAnalytic L f g ∧ ConvexOn ℝ Set.univ h ∧
      (∀ y, f xStar+h xStar ≤ f y+h y) ∧
      ProximalGradientScaling.IsSmoothProxRun 1 L h g x ∧
      ‖x 0-xStar‖^2 ≤ R^2 ∧
      f (x 1)+h (x 1)-(f xStar+h xStar) = (L : ℝ)*R^2/4 := by
  refine ⟨ProximalGradientWitnessScaling.smoothFunction L,
    ProximalGradientWitnessScaling.nonsmoothFunction 0 L R,
    ProximalGradientWitnessScaling.smoothGradient L, 0,
    ProximalGradientWitnessScaling.witnessPoint 0 R,
    ProximalGradientWitnessScaling.smooth_analytic L,
    ProximalGradientWitnessScaling.nonsmooth_convex 0 L hR,
    ProximalGradientWitnessScaling.star_isGlobalMin 0 L hR,
    ProximalGradientWitnessScaling.actual_run 0 hL hR,
    ProximalGradientWitnessScaling.radius 0 R, ?_⟩
  simpa using ProximalGradientWitnessScaling.attains 0 L hR

/-- Universal Hilbert upper from this external certificate AND actual attainment
on ℝ in the same class. Includes radius zero and does not impose gStar=0. -/
theorem actual_tightness
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {L : ℝ≥0} {R : ℝ} (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) :
    (∀ (f h : E → ℝ) (g : E → E) (xStar : E) (x : ℕ → E),
      IsSmoothConvexAnalytic L f g → ConvexOn ℝ Set.univ h →
      (∀ y, f xStar+h xStar ≤ f y+h y) →
      ProximalGradientScaling.IsSmoothProxRun 1 L h g x →
      ‖x 0-xStar‖^2 ≤ R^2 →
      f (x 1)+h (x 1)-(f xStar+h xStar) ≤ (L : ℝ)*R^2/4) ∧
    ∃ (f h g : ℝ → ℝ) (xStar : ℝ) (x : ℕ → ℝ),
      IsSmoothConvexAnalytic L f g ∧ ConvexOn ℝ Set.univ h ∧
      (∀ y, f xStar+h xStar ≤ f y+h y) ∧
      ProximalGradientScaling.IsSmoothProxRun 1 L h g x ∧
      ‖x 0-xStar‖^2 ≤ R^2 ∧
      f (x 1)+h (x 1)-(f xStar+h xStar) = (L : ℝ)*R^2/4 := by
  exact ⟨fun _ _ _ _ _ hf hh hm hr hd =>
    current_certificate_actual_upper hf hh hL hR hm hr hd,
    analytic_witness_verified hL hR⟩

/-- Explicit values of the analytic witness. This is not the external Gram. -/
theorem analytic_witness_values (L : ℝ≥0) {R : ℝ} (hR : 0 ≤ R) :
    ProximalGradientWitnessScaling.witnessPoint 0 R 0 = R ∧
    ProximalGradientWitnessScaling.witnessPoint 0 R 1 = R/2 ∧
    ProximalGradientWitnessScaling.smoothFunction L 0 = 0 ∧
    ProximalGradientWitnessScaling.nonsmoothFunction 0 L R 0 = 0 ∧
    ProximalGradientWitnessScaling.smoothFunction L
      (ProximalGradientWitnessScaling.witnessPoint 0 R 1) = (L : ℝ)*R/2 ∧
    ProximalGradientWitnessScaling.nonsmoothFunction 0 L R
      (ProximalGradientWitnessScaling.witnessPoint 0 R 1) = (L : ℝ)*R^2/4-(L : ℝ)*R/2 := by
  refine ⟨ProximalGradientWitnessScaling.witnessPoint_zero 0 R,
    ProximalGradientWitnessScaling.witnessPoint_final 0 R,
    ProximalGradientWitnessScaling.smoothFunction_zero L,
    ProximalGradientWitnessScaling.nonsmoothFunction_zero 0 L R, ?_, ?_⟩
  · rw [ProximalGradientWitnessScaling.witnessPoint_final 0 R]
    unfold ProximalGradientWitnessScaling.smoothFunction
    ring
  · rw [ProximalGradientWitnessScaling.witnessPoint_final 0 R]
    simp only [ProximalGradientWitnessScaling.nonsmoothFunction,
      ProximalGradientWitnessScaling.slope, ProximalGradientWitness.slope,
      Nat.cast_zero, zero_add, mul_one, max_eq_left (by positivity : 0 ≤ R/2)]
    ring

end LeanPEP.ActualFunction.PGOneCapturedTightness
