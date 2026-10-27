import LeanPEP

open LeanPEP LeanPEP.ActualFunction
open scoped NNReal

#check StrongMidpointMinimizer.cauchySeq_of_midpoint_gap
#check StrongMidpointMinimizer.exists_minimizer_of_midpoint_gap
#check ProximalScaling.norm_lower_bound_of_local_upper
#check ProximalScaling.exists_norm_lower_bound_of_continuousAt
#check ProximalScaling.hilbertProxObjective
#check ProximalScaling.hilbertProxObjective_continuous
#check ProximalScaling.hilbertProxObjective_bddBelow
#check ProximalScaling.hilbertProxObjective_midpoint_gap
#check ProximalScaling.exists_isProxPoint_hilbert
#check ProximalScaling.existsUnique_isProxPoint_hilbert
#check ProximalScaling.hasProx_of_continuous
#check ProximalGradientCanonical.hilbertIterate
#check ProximalGradientCanonical.hilbertIterate_zero
#check ProximalGradientCanonical.hilbertIterate_succ
#check ProximalGradientCanonical.hilbertIterate_isSmoothProxRun
#check ProximalGradientCanonical.exists_all_horizons_hilbert
#check ProximalGradientCanonical.run_eq_hilbertIterate
#check ProximalGradientCanonical.hilbertIterate_eq_finiteDimensional
#check ProximalGradientCanonical.certificate_upper_hilbert
#check ProximalGradientCanonical.upper_firstOrder_hilbert
#check ProximalGradientCanonical.upper_analytic_steps_hilbert
#check ProximalGradientCanonical.upper_analytic_exact_radius_hilbert
#check ProximalGradientCanonical.hilbertIterate_at_minimizer
#check ProximalGradientCanonical.witness_nonsmooth_continuous
#check ProximalGradientCanonical.hilbertIterate_witness
#check ProximalGradientCanonical.oneDimensionalHilbertValues
#check ProximalGradientCanonical.oneDimensionalHilbertValues_eq_canonicalValues
#check ProximalGradientCanonical.hilbert_bound_mem
#check ProximalGradientCanonical.hilbert_tight_all

section CompleteNormed
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

-- Generic compact-free minimization need not know that E is an inner product space.
example {Q : E → ℝ} {c : ℝ} (hc : 0 < c) (hQ : Continuous Q)
    (hbdd : BddBelow (Set.range Q))
    (hmid : ∀ x y, Q ((1/2 : ℝ) • x + (1/2 : ℝ) • y) ≤
      (Q x+Q y)/2-c*‖x-y‖^2) : ∃ z, ∀ y, Q z ≤ Q y :=
  StrongMidpointMinimizer.exists_minimizer_of_midpoint_gap hc hQ hbdd hmid
end CompleteNormed

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- There is deliberately no FiniteDimensional hypothesis in this section.
example {L : ℝ≥0} {h : E → ℝ} (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hcont : Continuous h) (v : E) :
    ∃! z, ProximalScaling.IsProxPoint L h v z :=
  ProximalScaling.existsUnique_isProxPoint_hilbert hL hh hcont v

example {L : ℝ≥0} {h : E → ℝ} (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hcont : Continuous h) (g : E → E) (x0 : E) :
    ∃ x : ℕ → E, x 0=x0 ∧ ∀ N, ProximalGradientScaling.IsSmoothProxRun N L h g x :=
  ProximalGradientCanonical.exists_all_horizons_hilbert hL hh hcont g x0

example {L : ℝ≥0} {h : E → ℝ} (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hcont : Continuous h) (g : E → E) (x0 : E) :
    ProximalGradientCanonical.hilbertIterate L h hL hh hcont g x0 0=x0 := rfl

example {L : ℝ≥0} {h : E → ℝ} (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hcont : Continuous h) {g : E → E} {x : ℕ → E}
    {N : ℕ} (hrun : ProximalGradientScaling.IsSmoothProxRun N L h g x) :
    x N = ProximalGradientCanonical.hilbertIterate L h hL hh hcont g (x 0) N :=
  ProximalGradientCanonical.run_eq_hilbertIterate hL hh hcont hrun rfl N (le_refl _)

-- Final rate has no supplied run or HasProx proof; zero radius remains allowed.
example (T : ℕ) (hT : 0 < T) {L : ℝ≥0} {R : ℝ}
    {f h : E → ℝ} {g : E → E} {xStar x0 : E}
    (hf : IsSmoothConvexAnalytic L f g) (hh : ConvexOn ℝ Set.univ h)
    (hcont : Continuous h) (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hm : ∀ y, f xStar+h xStar ≤ f y+h y) (hr : ‖x0-xStar‖^2 ≤ R^2) :
    f (ProximalGradientCanonical.hilbertIterate L h hL hh hcont g x0 T) +
      h (ProximalGradientCanonical.hilbertIterate L h hL hh hcont g x0 T) -
      (f xStar+h xStar) ≤ (L : ℝ)*R^2/(4*(T : ℝ)) :=
  ProximalGradientCanonical.upper_analytic_steps_hilbert T hT hf hh hcont hL hR hm hr

example {L : ℝ≥0} {f h : E → ℝ} {g : E → E} {xStar : E}
    (hf : IsSmoothConvexFirstOrder L f g) (hh : ConvexOn ℝ Set.univ h)
    (hcont : Continuous h) (hL : 0 < (L : ℝ))
    (hm : ∀ y, f xStar+h xStar ≤ f y+h y) (k : ℕ) :
    ProximalGradientCanonical.hilbertIterate L h hL hh hcont g xStar k = xStar :=
  ProximalGradientCanonical.hilbertIterate_at_minimizer hf hh hcont hL hm k
end Hilbert

section FiniteDimension
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

example {L : ℝ≥0} {h : E → ℝ} (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hcont : Continuous h) (g : E → E) (x0 : E) :
    ProximalGradientCanonical.hilbertIterate L h hL hh hcont g x0 =
      ProximalGradientCanonical.finiteDimensionalIterate L h hL hh g x0 :=
  ProximalGradientCanonical.hilbertIterate_eq_finiteDimensional L h hL hh hcont g x0
end FiniteDimension

example (n : ℕ) {L : ℝ≥0} (hL : 0 < (L : ℝ)) (R : ℝ) :
    ProximalGradientCanonical.oneDimensionalHilbertValues n L R =
      ProximalGradientCanonical.oneDimensionalValues n L R :=
  ProximalGradientCanonical.oneDimensionalHilbertValues_eq_canonicalValues n hL R

example (n : ℕ) {L : ℝ≥0} {R : ℝ} (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) :
    IsGreatest (ProximalGradientCanonical.oneDimensionalHilbertValues n L R)
      ((L : ℝ)*R^2/(4*((n : ℝ)+1))) :=
  ProximalGradientCanonical.hilbert_tight_all n hL hR

example (n : ℕ) {L : ℝ≥0} (hL : 0 < (L : ℝ)) :
    IsGreatest (ProximalGradientCanonical.oneDimensionalHilbertValues n L 0) 0 := by
  simpa using ProximalGradientCanonical.hilbert_tight_all n hL (le_refl (0 : ℝ))

example : IsGreatest (ProximalGradientCanonical.oneDimensionalHilbertValues 7 3 2) (3/8 : ℝ) := by
  have ht := ProximalGradientCanonical.hilbert_tight_all 7 (L := 3) (R := 2)
    (by norm_num) (by norm_num)
  norm_num at ht ⊢
  exact ht

example (n : ℕ) {L : ℝ≥0} {R : ℝ} (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (k : ℕ) (hk : k ≤ n+1) :
    ProximalGradientCanonical.hilbertIterate L
      (ProximalGradientWitnessScaling.nonsmoothFunction n L R)
      hL (ProximalGradientWitnessScaling.nonsmooth_convex n L hR)
      (ProximalGradientCanonical.witness_nonsmooth_continuous n L R)
      (ProximalGradientWitnessScaling.smoothGradient L) R k =
        ProximalGradientWitnessScaling.witnessPoint n R k :=
  ProximalGradientCanonical.hilbertIterate_witness n hL hR k hk

#print axioms StrongMidpointMinimizer.cauchySeq_of_midpoint_gap
#print axioms StrongMidpointMinimizer.exists_minimizer_of_midpoint_gap
#print axioms ProximalScaling.exists_norm_lower_bound_of_continuousAt
#print axioms ProximalScaling.existsUnique_isProxPoint_hilbert
#print axioms ProximalGradientCanonical.upper_analytic_steps_hilbert
#print axioms ProximalGradientCanonical.oneDimensionalHilbertValues_eq_canonicalValues
#print axioms ProximalGradientCanonical.hilbert_tight_all
