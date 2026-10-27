import LeanPEP.ActualFunction.HuberWitnessScaling

open scoped NNReal

open LeanPEP
open LeanPEP.ActualFunction
open LeanPEP.ActualFunction.HuberWitness
open LeanPEP.ActualFunction.ParametricGDScaling

#check scaledThreshold
#check scaledWitnessFunction
#check scaledWitnessGradient
#check scaledWitnessPoint
#check huberGradient_scale
#check huberFunction_scale
#check scaledWitnessFunction_scale_point
#check scaledWitnessGradient_scale_point

#check scaledWitnessFunction_hasDerivAt
#check deriv_scaledWitnessFunction
#check scaledWitnessFunction_differentiable
#check scaledWitnessGradient_monotone
#check scaledWitnessFunction_convexOn
#check scaledWitnessGradient_lipschitz
#check scaledWitness_analytic

#check scaledWitnessPoint_smoothGD_step
#check smoothGDIterate_eq_scaledWitnessPoint
#check smoothGDIterate_final
#check generalBound
#check generalBound_eq_closed
#check scaledWitness_smoothGD_attains_bound
#check scaledWitness_smoothGD_attains_closed_form
#check general_analytic_lower_witness

#check oneDimensionalAnalyticGDValues
#check generalBound_mem_oneDimensionalAnalyticGDValues
#check oneDimensional_analytic_tight
#check analytic_upper_and_oneDimensional_tight

example (N : ℕ) :
    IsSmoothConvexAnalytic (2 : ℝ≥0)
      (scaledWitnessFunction N (2 : ℝ≥0) 3)
      (scaledWitnessGradient N (2 : ℝ≥0) 3) := by
  exact scaledWitness_analytic N (2 : ℝ≥0) 3

example (N : ℕ) :
    scaledWitnessFunction N (2 : ℝ≥0) 3
        (smoothGDIterate (2 : ℝ≥0)
          (scaledWitnessGradient N (2 : ℝ≥0) 3) 3 N) -
      scaledWitnessFunction N (2 : ℝ≥0) 3 0 =
        generalBound N (2 : ℝ≥0) 3 := by
  exact scaledWitness_smoothGD_attains_bound N
    (L := (2 : ℝ≥0)) (R := (3 : ℝ)) (by norm_num) (by norm_num)

example (N : ℕ) :
    IsGreatest
      (oneDimensionalAnalyticGDValues N (2 : ℝ≥0) 3)
      (generalBound N (2 : ℝ≥0) 3) := by
  exact oneDimensional_analytic_tight N
    (L := (2 : ℝ≥0)) (R := (3 : ℝ)) (by norm_num) (by norm_num)

example (N : ℕ) :
    (∀ {f : ℝ → ℝ} {g : ℝ → ℝ} {xStar x0 : ℝ},
      IsSmoothConvexAnalytic (2 : ℝ≥0) f g →
      g xStar = 0 →
      ‖x0 - xStar‖ ^ 2 ≤ (3 : ℝ) ^ 2 →
      f (smoothGDIterate (2 : ℝ≥0) g x0 N) - f xStar ≤
        generalBound N (2 : ℝ≥0) 3) ∧
    IsGreatest
      (oneDimensionalAnalyticGDValues N (2 : ℝ≥0) 3)
      (generalBound N (2 : ℝ≥0) 3) := by
  exact analytic_upper_and_oneDimensional_tight
    (E := ℝ) N (L := (2 : ℝ≥0)) (R := (3 : ℝ))
      (by norm_num) (by norm_num)
