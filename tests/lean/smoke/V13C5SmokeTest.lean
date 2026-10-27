import LeanPEP

open LeanPEP LeanPEP.ActualFunction
open scoped NNReal

#check ProximalScaling.subgradient_of_isProxPoint
#check ProximalScaling.isProxPoint_iff_subgradient
#check ProximalScaling.isProxPoint_unique
#check Proximal.scaled_forward_residual
#check Proximal.prox_fixedPoint_of_quadratic_support
#check Proximal.subgradient_of_quadratic_support
#check Proximal.subgradient_of_minimizer_of_upperModel
#check Proximal.subgradient_of_composite_minimizer
#check Proximal.composite_minimizer_of_subgradient
#check Proximal.composite_minimizer_iff_subgradient
#check Proximal.composite_minimizer_iff_prox_fixedPoint
#check Proximal.composite_minimizer_iff_subgradient_analytic
#check ProximalGradientScaling.certificate_upper_of_minimizer
#check ProximalGradientScaling.upper_firstOrder_of_minimizer
#check ProximalGradientScaling.upper_analytic_of_minimizer
#check ProximalGradientScaling.upper_analytic_steps_of_minimizer
#check ProximalGradientScaling.upper_analytic_exact_radius_of_minimizer
#check ProximalGradientScaling.stationary_run_of_minimizer
#check ProximalGradientScaling.oneDimensionalMinimizerValues
#check ProximalGradientScaling.oneDimensionalMinimizerValues_eq_analyticValues
#check ProximalGradientScaling.witness_mem_minimizerValues
#check ProximalGradientScaling.minimizer_tight_all
#check ProximalGradientScaling.analytic_upper_and_oneDimensional_minimizer_tight

section InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- The optimality equivalence does not require a complete space.
example {L : ℝ≥0} {f h : E → ℝ} {g : E → E} {xStar : E}
    (hf : IsSmoothConvexFirstOrder L f g) (hh : ConvexOn ℝ Set.univ h) :
    (∀ y, f xStar + h xStar ≤ f y + h y) ↔
      Proximal.SubgradientAt h (-g xStar) xStar :=
  Proximal.composite_minimizer_iff_subgradient hf hh

-- Structural optimality includes L=0; no zero-step-size rate is asserted.
example {f h : E → ℝ} {g : E → E} {xStar : E}
    (hf : IsSmoothConvexFirstOrder 0 f g) (hh : ConvexOn ℝ Set.univ h)
    (hm : ∀ y, f xStar + h xStar ≤ f y + h y) :
    Proximal.SubgradientAt h (-g xStar) xStar :=
  Proximal.subgradient_of_composite_minimizer hf hh hm

example {L : ℝ≥0} {h : E → ℝ} {v x y : E}
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h)
    (hx : ProximalScaling.IsProxPoint L h v x)
    (hy : ProximalScaling.IsProxPoint L h v y) : y = x :=
  ProximalScaling.isProxPoint_unique hL hh hx hy

example {L : ℝ≥0} {f h : E → ℝ} {g : E → E} {xStar : E}
    (hf : IsSmoothConvexFirstOrder L f g) (hh : ConvexOn ℝ Set.univ h)
    (hL : 0 < (L : ℝ)) :
    (∀ y, f xStar + h xStar ≤ f y + h y) ↔
      ProximalScaling.IsProxPoint L h (xStar - (L : ℝ)⁻¹ • g xStar) xStar :=
  Proximal.composite_minimizer_iff_prox_fixedPoint hf hh hL

example {N : ℕ} {L : ℝ≥0} {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsSmoothConvexFirstOrder L f g) (hh : ConvexOn ℝ Set.univ h)
    (hL : 0 < (L : ℝ)) (hm : ∀ y, f xStar + h xStar ≤ f y + h y)
    (hp : ProximalGradientScaling.IsSmoothProxRun N L h g x) (hx0 : x 0 = xStar) :
    x N = xStar :=
  ProximalGradientScaling.stationary_run_of_minimizer hf hh hL hm hp hx0 N (le_refl _)
end InnerProduct

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- No certificate acceptance, Gram feasibility, or explicit subgradient is passed.
example (T : ℕ) (hT : 0 < T) {L : ℝ≥0} {R : ℝ}
    {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsSmoothConvexAnalytic L f g) (hh : ConvexOn ℝ Set.univ h)
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hm : ∀ y, f xStar + h xStar ≤ f y + h y)
    (hp : ProximalGradientScaling.IsSmoothProxRun T L h g x)
    (hr : ‖x 0-xStar‖^2 ≤ R^2) :
    f (x T) + h (x T) - (f xStar + h xStar) ≤ (L : ℝ)*R^2/(4*(T : ℝ)) :=
  ProximalGradientScaling.upper_analytic_steps_of_minimizer T hT hf hh hL hR hm hp hr

example {n : ℕ} {L : ℝ≥0} {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsSmoothConvexAnalytic L f g) (hh : ConvexOn ℝ Set.univ h)
    (hL : 0 < (L : ℝ)) (hm : ∀ y, f xStar + h xStar ≤ f y + h y)
    (hp : ProximalGradientScaling.IsSmoothProxRun (n+1) L h g x) :
    f (x (n+1)) + h (x (n+1)) - (f xStar + h xStar) ≤
      (L : ℝ)*‖x 0-xStar‖^2/(4*((n : ℝ)+1)) :=
  ProximalGradientScaling.upper_analytic_exact_radius_of_minimizer hf hh hL hm hp
end Hilbert

example (n : ℕ) (R : ℝ) :
    ProximalGradientScaling.oneDimensionalMinimizerValues n 0 R =
      ProximalGradientScaling.oneDimensionalAnalyticValues n 0 R :=
  ProximalGradientScaling.oneDimensionalMinimizerValues_eq_analyticValues n 0 R

example (n : ℕ) {L : ℝ≥0} {R : ℝ} (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) :
    IsGreatest (ProximalGradientScaling.oneDimensionalMinimizerValues n L R)
      ((L : ℝ)*R^2/(4*((n : ℝ)+1))) :=
  ProximalGradientScaling.minimizer_tight_all n hL hR

example (n : ℕ) {L : ℝ≥0} (hL : 0 < (L : ℝ)) :
    IsGreatest (ProximalGradientScaling.oneDimensionalMinimizerValues n L 0) 0 := by
  simpa using ProximalGradientScaling.minimizer_tight_all n hL (le_refl (0 : ℝ))

example : IsGreatest (ProximalGradientScaling.oneDimensionalMinimizerValues 7 3 2)
    (3/8 : ℝ) := by
  have ht := ProximalGradientScaling.minimizer_tight_all 7
    (L := 3) (R := 2) (by norm_num) (by norm_num)
  norm_num at ht ⊢
  exact ht

example (n : ℕ) {L : ℝ≥0} {R : ℝ} (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) :
    (L : ℝ)*R^2/(4*((n : ℝ)+1)) ∈
      ProximalGradientScaling.oneDimensionalMinimizerValues n L R :=
  ProximalGradientScaling.witness_mem_minimizerValues n hL hR

#print axioms ProximalScaling.subgradient_of_isProxPoint
#print axioms ProximalScaling.isProxPoint_unique
#print axioms Proximal.subgradient_of_composite_minimizer
#print axioms Proximal.composite_minimizer_iff_prox_fixedPoint
#print axioms ProximalGradientScaling.upper_analytic_steps_of_minimizer
#print axioms ProximalGradientScaling.oneDimensionalMinimizerValues_eq_analyticValues
#print axioms ProximalGradientScaling.minimizer_tight_all
