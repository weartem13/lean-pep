import LeanPEP

open LeanPEP LeanPEP.ActualFunction
open scoped NNReal

#check ProximalScaling.IsProxPoint
#check ProximalScaling.isProxPoint_iff_norm
#check ProximalScaling.isProxPoint_one
#check ProximalScaling.scaled_normalizedPoint
#check ProximalScaling.normalized_scaledPoint
#check ProximalScaling.scaledPoint_combination
#check ProximalScaling.normalizedFunction_convex
#check ProximalScaling.normalized_subgradient
#check ProximalScaling.normalized_prox_objective
#check ProximalScaling.normalized_prox_iff
#check ProximalScaling.isProxPoint_of_subgradient
#check ProximalScaling.eq_of_subgradient_of_isProxPoint
#check ProximalGradientScaling.IsSmoothProxRun
#check ProximalGradientScaling.isSmoothProxRun_zero
#check ProximalGradientScaling.isSmoothProxRun_one
#check ProximalGradientScaling.IsSmoothProxRun.restrict
#check ProximalGradientScaling.normalized_forward
#check ProximalGradientScaling.isSmoothProxRun_iff_normalized
#check ProximalGradientScaling.normalized_stationarity
#check ProximalGradientScaling.normalizedPoint_radius
#check ProximalGradientScaling.normalized_objective
#check ProximalGradientScaling.stationary_run
#check ProximalGradientScaling.certificate_upper
#check ProximalGradientScaling.upper_firstOrder
#check ProximalGradientScaling.upper_analytic
#check ProximalGradientScaling.upper_analytic_steps
#check ProximalGradientScaling.upper_analytic_exact_radius
#check ProximalGradientWitnessScaling.smooth_analytic
#check ProximalGradientWitnessScaling.nonsmooth_convex
#check ProximalGradientWitnessScaling.star_subgradient
#check ProximalGradientWitnessScaling.star_isGlobalMin
#check ProximalGradientWitnessScaling.smooth_gradient_at_star_ne_zero
#check ProximalGradientWitnessScaling.witnessPoint_final
#check ProximalGradientWitnessScaling.actual_run
#check ProximalGradientWitnessScaling.attains
#check ProximalGradientWitnessScaling.unit_witness
#check ProximalGradientWitnessScaling.bound_mem
#check ProximalGradientWitnessScaling.analytic_tight_all
#check ProximalGradientWitnessScaling.analytic_upper_and_oneDimensional_tight

section Abstract
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- The public theorem takes a physical run, not Gram feasibility or acceptance.
example (T : ℕ) (hT : 0 < T) {L : ℝ≥0} {R : ℝ}
    {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsSmoothConvexAnalytic L f g) (hh : ConvexOn ℝ Set.univ h)
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) (hs : Proximal.SubgradientAt h (-g xStar) xStar)
    (hrun : ProximalGradientScaling.IsSmoothProxRun T L h g x)
    (hradius : ‖x 0-xStar‖^2 ≤ R^2) :
    f (x T) + h (x T) - (f xStar+h xStar) ≤ (L : ℝ)*R^2/(4*(T : ℝ)) :=
  ProximalGradientScaling.upper_analytic_steps T hT hf hh hL hR hs hrun hradius

example (N : ℕ) (h : E → ℝ) (g : E → E) (x : ℕ → E) :
    ProximalGradientScaling.IsSmoothProxRun N 1 h g x ↔ ProximalGradient.IsProxRun N h g x :=
  ProximalGradientScaling.isSmoothProxRun_one N h g x

example {L : ℝ≥0} {R : ℝ} (hL : 0 < (L : ℝ)) (hR : 0 < R)
    (h : E → ℝ) (center v z : E) :
    ProximalScaling.IsProxPoint L h (SmoothScaling.scaledPoint center R v)
      (SmoothScaling.scaledPoint center R z) ↔
    Proximal.IsUnitProxPoint (SmoothScaling.normalizedFunction h center L R) v z :=
  ProximalScaling.normalized_prox_iff hL hR h center v z

example {N : ℕ} {L : ℝ≥0} {h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hL : 0 < (L : ℝ)) (hs : Proximal.SubgradientAt h (-g xStar) xStar)
    (hrun : ProximalGradientScaling.IsSmoothProxRun N L h g x)
    (hx0 : x 0 = xStar) : x N = xStar :=
  ProximalGradientScaling.stationary_run hL hs hrun hx0 N (le_refl _)
end Abstract

-- T = 8 (n = 7), L = 3, R = 2: the exact value is 3/8.
example : IsGreatest (ProximalGradientScaling.oneDimensionalAnalyticValues 7 3 2) (3/8 : ℝ) := by
  have ht := ProximalGradientWitnessScaling.analytic_tight_all 7
    (L := 3) (R := 2) (by norm_num) (by norm_num)
  norm_num at ht ⊢
  exact ht

-- Arbitrary positive horizon; no bounded enumeration or new checker evaluation.
example (n : ℕ) {L : ℝ≥0} {R : ℝ} (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) :
    IsGreatest (ProximalGradientScaling.oneDimensionalAnalyticValues n L R)
      ((L : ℝ)*R^2/(4*((n : ℝ)+1))) :=
  ProximalGradientWitnessScaling.analytic_tight_all n hL hR

example (n : ℕ) {L : ℝ≥0} (hL : 0 < (L : ℝ)) :
    IsGreatest (ProximalGradientScaling.oneDimensionalAnalyticValues n L 0) 0 := by
  simpa using ProximalGradientWitnessScaling.analytic_tight_all n hL (le_refl (0 : ℝ))

example (n k : ℕ) : ProximalGradientWitnessScaling.witnessPoint n 0 k = 0 :=
  ProximalGradientWitnessScaling.zeroRadius_point n k

example (n : ℕ) {L : ℝ≥0} (hL : 0 < (L : ℝ)) :
    ProximalGradientScaling.IsSmoothProxRun (n+1) L
      (ProximalGradientWitnessScaling.nonsmoothFunction n L 0)
      (ProximalGradientWitnessScaling.smoothGradient L)
      (ProximalGradientWitnessScaling.witnessPoint n 0) :=
  ProximalGradientWitnessScaling.actual_run n hL (le_refl (0 : ℝ))

example {L : ℝ≥0} (hL : 0 < (L : ℝ)) :
    ProximalGradientWitnessScaling.smoothGradient L 0 ≠ 0 :=
  ProximalGradientWitnessScaling.smooth_gradient_at_star_ne_zero hL

example (n : ℕ) :
    ProximalGradientWitnessScaling.witnessPoint n 1 = ProximalGradientWitness.witnessPoint n :=
  (ProximalGradientWitnessScaling.unit_witness n).2.2.2

#print axioms ProximalScaling.normalized_prox_iff
#print axioms ProximalScaling.eq_of_subgradient_of_isProxPoint
#print axioms ProximalGradientScaling.isSmoothProxRun_iff_normalized
#print axioms ProximalGradientScaling.certificate_upper
#print axioms ProximalGradientScaling.upper_analytic_steps
#print axioms ProximalGradientWitnessScaling.actual_run
#print axioms ProximalGradientWitnessScaling.analytic_tight_all
