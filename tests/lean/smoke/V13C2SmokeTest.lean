import LeanPEP

/-! v0.13C2: positive-horizon compiler, actual runs, and exact C1 migration.
The compiler parameter n denotes n+1 updates; n=0 is NOT a zero-step model.
-/

open LeanPEP
open LeanPEP.GramPEP

#check Profiles.ProximalGradient.value_blocks_disjoint
#check Profiles.ProximalGradient.smoothValueIndex_injective
#check Profiles.ProximalGradient.nonsmoothValueIndex_injective
#check Profiles.ProximalGradient.valueIndex_covers
#check Profiles.ProximalGradient.positionVecQ_succ
#check Profiles.ProximalGradient.positionVecQ_gradient_causal
#check Profiles.ProximalGradient.positionVecQ_residual_causal
#check Profiles.ProximalGradient.terminal_gradient_unused
#check Profiles.ProximalGradient.modelQ_constraints
#check Profiles.ProximalGradient.modelQ_constraint_count
#check Profiles.ProximalGradient.certificate_upper
#check Profiles.ProximalGradient.smoothSamplesQ_zero
#check Profiles.ProximalGradient.nonsmoothSamplesQ_zero
#check Profiles.ProximalGradient.modelQ_zero
#check Profiles.ProximalGradient.objectiveQ_zero
#check Profiles.ProximalGradient.oneStep_exact_certificate
#check Profiles.ProximalGradient.oneStep_finite_tight
#check ActualFunction.ProximalGradient.IsProxRun
#check ActualFunction.ProximalGradient.IsResidualRun
#check ActualFunction.ProximalGradient.IsProxRun.restrict
#check ActualFunction.ProximalGradient.IsProxRun.toResidualRun
#check ActualFunction.ProximalGradient.IsResidualRun.toProxRun
#check ActualFunction.ProximalGradient.IsResidualRun.residual_eq
#check ActualFunction.ProximalGradient.isProxRun_iff_residual
#check ActualFunction.ProximalGradient.position_realization
#check ActualFunction.ProximalGradient.smoothSamples_denote
#check ActualFunction.ProximalGradient.nonsmoothSamples_denote
#check ActualFunction.ProximalGradient.radius_eval
#check ActualFunction.ProximalGradient.objective_eval
#check ActualFunction.ProximalGradient.actualData_constraints
#check ActualFunction.ProximalGradient.certificate_upper
#check ActualFunction.ProximalGradient.certificate_upper_of_prox
#check ActualFunction.ProximalGradient.certificate_upper_analytic
#check ActualFunction.ProximalGradient.oneStep_upper_analytic
#check ActualFunction.ProximalGradient.oneDimensionalAnalyticValues_zero
#check ActualFunction.ProximalGradient.oneStep_analytic_tight

example : (Profiles.ProximalGradient.modelQ 0).assumptions.length = 14 := by
  rw [Profiles.ProximalGradient.modelQ_constraint_count]
  norm_num

example : (Profiles.ProximalGradient.modelQ 1).assumptions.length = 26 := by
  rw [Profiles.ProximalGradient.modelQ_constraint_count]
  norm_num

example : (Profiles.ProximalGradient.modelQ 7).assumptions.length = 182 := by
  rw [Profiles.ProximalGradient.modelQ_constraint_count]
  norm_num

/-- Two actual implicit updates, including both residuals. -/
example : Profiles.ProximalGradient.positionVecQ 1 2 =
    ![1, 0, -1, -1, 0, -1, -1] := by
  funext r
  fin_cases r <;> decide +kernel

example (n k : ℕ) (hk : k ≤ n + 1) :
    Profiles.ProximalGradient.positionVecQ n k
      (Profiles.ProximalGradient.gradientBasisIndex (Fin.last (n + 1))) = 0 :=
  Profiles.ProximalGradient.terminal_gradient_unused n k hk

example : (Profiles.ProximalGradient.nonsmoothSamplesQ 2 0).oracle =
    -Profiles.ProximalGradient.starGradientQ 2 := rfl

example : ∃ c : UpperCertQ (Profiles.ProximalGradient.modelQ 0),
    c.bound = (1 : ℚ) / 4 ∧ c.objective = Profiles.ProximalGradient.objectiveQ 0 ∧
      c.interpTerms = [] ∧ checkUpperCertQ c = true :=
  Profiles.ProximalGradient.oneStep_exact_certificate

section Actual
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

example (h : E → ℝ) (g : E → E) (x : ℕ → E) :
    ActualFunction.ProximalGradient.IsProxRun 0 h g x :=
  ActualFunction.ProximalGradient.isProxRun_zero h g x

example {n : ℕ} {h : E → ℝ} {g : E → E} {x : ℕ → E}
    (hh : ConvexOn ℝ Set.univ h)
    (hr : ActualFunction.ProximalGradient.IsProxRun (n + 1) h g x) :
    ActualFunction.ProximalGradient.IsResidualRun (n + 1) h g x
      (ActualFunction.ProximalGradient.residual g x) := hr.toResidualRun hh

example [CompleteSpace E] {n : ℕ}
    (c : UpperCertQ (Profiles.ProximalGradient.modelQ n))
    (hc : checkUpperCertQ c = true) (he : c.interpTerms = [])
    (ho : c.objective = Profiles.ProximalGradient.objectiveQ n)
    {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : ActualFunction.IsOneSmoothConvexAnalytic f g) (hh : ConvexOn ℝ Set.univ h)
    (hs : ActualFunction.Proximal.SubgradientAt h (-g xStar) xStar)
    (hr : ActualFunction.ProximalGradient.IsProxRun (n + 1) h g x)
    (hR : ‖x 0 - xStar‖ ^ 2 ≤ 1) :
    f (x (n + 1)) + h (x (n + 1)) - (f xStar + h xStar) ≤ (c.bound : ℝ) :=
  ActualFunction.ProximalGradient.certificate_upper_analytic c hc he ho hf hh hs hr hR

example [CompleteSpace E] {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : ActualFunction.IsOneSmoothConvexAnalytic f g) (hh : ConvexOn ℝ Set.univ h)
    (hs : ActualFunction.Proximal.SubgradientAt h (-g xStar) xStar)
    (hr : ActualFunction.ProximalGradient.IsProxRun 1 h g x)
    (hR : ‖x 0 - xStar‖ ^ 2 ≤ 1) :
    f (x 1) + h (x 1) - (f xStar + h xStar) ≤ (1 : ℝ) / 4 :=
  ActualFunction.ProximalGradient.oneStep_upper_analytic hf hh hs hr hR
end Actual

example : IsGreatest (ActualFunction.ProximalGradient.oneDimensionalAnalyticValues 0)
    ((1 : ℝ) / 4) := ActualFunction.ProximalGradient.oneStep_analytic_tight

#print axioms Profiles.ProximalGradient.positionVecQ_gradient_causal
#print axioms Profiles.ProximalGradient.modelQ_zero
#print axioms ActualFunction.ProximalGradient.position_realization
#print axioms ActualFunction.ProximalGradient.certificate_upper_analytic
#print axioms ActualFunction.ProximalGradient.oneStep_upper_analytic
#print axioms ActualFunction.ProximalGradient.oneStep_analytic_tight
