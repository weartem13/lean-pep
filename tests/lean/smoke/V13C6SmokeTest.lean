import LeanPEP

open LeanPEP LeanPEP.ActualFunction
open scoped NNReal

#check ProximalScaling.exists_norm_lower_bound
#check ProximalScaling.exists_isProxPoint
#check ProximalScaling.existsUnique_isProxPoint
#check ProximalScaling.HasProx
#check ProximalScaling.hasProx_of_finiteDimensional
#check ProximalScaling.proxMap
#check ProximalScaling.proxMap_spec
#check ProximalScaling.proxMap_eq_of_isProxPoint
#check ProximalScaling.proxMap_eq_of_selector
#check ProximalScaling.proxMap_subgradient
#check ProximalGradientCanonical.iterate
#check ProximalGradientCanonical.iterate_zero
#check ProximalGradientCanonical.iterate_succ
#check ProximalGradientCanonical.iterate_isSmoothProxRun
#check ProximalGradientCanonical.run_eq_iterate
#check ProximalGradientCanonical.isSmoothProxRun_iff_eq_iterate
#check ProximalGradientCanonical.exists_all_horizons
#check ProximalGradientCanonical.finiteDimensionalIterate
#check ProximalGradientCanonical.finiteDimensionalIterate_isSmoothProxRun
#check ProximalGradientCanonical.exists_all_horizons_finiteDimensional
#check ProximalGradientCanonical.certificate_upper
#check ProximalGradientCanonical.upper_firstOrder
#check ProximalGradientCanonical.upper_analytic_steps
#check ProximalGradientCanonical.upper_analytic_steps_finiteDimensional
#check ProximalGradientCanonical.upper_analytic_exact_radius_finiteDimensional
#check ProximalGradientCanonical.iterate_at_minimizer
#check ProximalGradientCanonical.iterate_witness
#check ProximalGradientCanonical.oneDimensionalValues_eq_minimizerValues
#check ProximalGradientCanonical.bound_mem
#check ProximalGradientCanonical.tight_all

section AbstractSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- Existence of every finite prefix of one selected infinite run.
example {L : ℝ≥0} {h : E → ℝ} (hp : ProximalScaling.HasProx L h)
    (g : E → E) (x0 : E) :
    ∃ x : ℕ → E, x 0 = x0 ∧ ∀ N, ProximalGradientScaling.IsSmoothProxRun N L h g x :=
  ProximalGradientCanonical.exists_all_horizons hp g x0

-- No smoothness or complete-space assumption is needed for run uniqueness.
example {L : ℝ≥0} {h : E → ℝ} (hp : ProximalScaling.HasProx L h)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h)
    {g : E → E} {x : ℕ → E} {N : ℕ}
    (hx : ProximalGradientScaling.IsSmoothProxRun N L h g x) :
    x N = ProximalGradientCanonical.iterate hp g (x 0) N :=
  ProximalGradientCanonical.run_eq_iterate hp hL hh hx rfl N (le_refl _)

example {L : ℝ≥0} {h : E → ℝ} (hp : ProximalScaling.HasProx L h)
    (g : E → E) (x0 : E) : ProximalGradientCanonical.iterate hp g x0 0 = x0 := rfl

example {L : ℝ≥0} {h : E → ℝ} (hp : ProximalScaling.HasProx L h)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h)
    (p : E → E) (hs : ∀ v, ProximalScaling.IsProxPoint L h v (p v)) :
    ProximalScaling.proxMap hp = p :=
  ProximalScaling.proxMap_eq_of_selector hp hL hh p hs
end AbstractSpace

section FiniteDimension
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

-- No supporting vector, continuity premise, or global composite minimum.
example {L : ℝ≥0} {h : E → ℝ} (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (v : E) : ∃! z, ProximalScaling.IsProxPoint L h v z :=
  ProximalScaling.existsUnique_isProxPoint hL hh v

example {L : ℝ≥0} {h : E → ℝ} (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (g : E → E) (x0 : E) :
    ∃ x : ℕ → E, x 0 = x0 ∧ ∀ N, ProximalGradientScaling.IsSmoothProxRun N L h g x :=
  ProximalGradientCanonical.exists_all_horizons_finiteDimensional hL hh g x0

-- The caller does not supply a run, a HasProx proof, or a stationarity certificate.
example (T : ℕ) (hT : 0 < T) {L : ℝ≥0} {R : ℝ}
    {f h : E → ℝ} {g : E → E} {xStar x0 : E}
    (hf : IsSmoothConvexAnalytic L f g) (hh : ConvexOn ℝ Set.univ h)
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hm : ∀ y, f xStar + h xStar ≤ f y + h y) (hr : ‖x0-xStar‖^2 ≤ R^2) :
    f (ProximalGradientCanonical.finiteDimensionalIterate L h hL hh g x0 T) +
      h (ProximalGradientCanonical.finiteDimensionalIterate L h hL hh g x0 T) -
      (f xStar + h xStar) ≤ (L : ℝ)*R^2/(4*(T : ℝ)) :=
  ProximalGradientCanonical.upper_analytic_steps_finiteDimensional T hT hf hh hL hR hm hr
end FiniteDimension

example (n : ℕ) {L : ℝ≥0} (hL : 0 < (L : ℝ)) (R : ℝ) :
    ProximalGradientCanonical.oneDimensionalValues n L R =
      ProximalGradientScaling.oneDimensionalMinimizerValues n L R :=
  ProximalGradientCanonical.oneDimensionalValues_eq_minimizerValues n hL R

example (n : ℕ) {L : ℝ≥0} {R : ℝ} (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) :
    IsGreatest (ProximalGradientCanonical.oneDimensionalValues n L R)
      ((L : ℝ)*R^2/(4*((n : ℝ)+1))) :=
  ProximalGradientCanonical.tight_all n hL hR

example (n : ℕ) {L : ℝ≥0} (hL : 0 < (L : ℝ)) :
    IsGreatest (ProximalGradientCanonical.oneDimensionalValues n L 0) 0 := by
  simpa using ProximalGradientCanonical.tight_all n hL (le_refl (0 : ℝ))

example : IsGreatest (ProximalGradientCanonical.oneDimensionalValues 7 3 2) (3/8 : ℝ) := by
  have ht := ProximalGradientCanonical.tight_all 7 (L := 3) (R := 2) (by norm_num) (by norm_num)
  norm_num at ht ⊢
  exact ht

example (n : ℕ) {L : ℝ≥0} {R : ℝ} (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (k : ℕ) (hk : k ≤ n+1) :
    ProximalGradientCanonical.finiteDimensionalIterate L
      (ProximalGradientWitnessScaling.nonsmoothFunction n L R)
      hL (ProximalGradientWitnessScaling.nonsmooth_convex n L hR)
      (ProximalGradientWitnessScaling.smoothGradient L) R k =
        ProximalGradientWitnessScaling.witnessPoint n R k :=
  ProximalGradientCanonical.iterate_witness n hL hR k hk

#print axioms ProximalScaling.exists_norm_lower_bound
#print axioms ProximalScaling.existsUnique_isProxPoint
#print axioms ProximalScaling.proxMap_spec
#print axioms ProximalGradientCanonical.run_eq_iterate
#print axioms ProximalGradientCanonical.upper_analytic_steps_finiteDimensional
#print axioms ProximalGradientCanonical.oneDimensionalValues_eq_minimizerValues
#print axioms ProximalGradientCanonical.tight_all
