import LeanPEP

open LeanPEP LeanPEP.ActualFunction
open ProximalScaling ProximalGradientCanonical
open scoped NNReal Topology BigOperators

#check OperatorEnergy.firm_energy_of_inner
#check OperatorEnergy.composition_energy
#check Proximal.subgradient_pair_monotone
#check ProximalScaling.isProxPoint_firm
#check ProximalScaling.isProxPoint_energy
#check ProximalScaling.proxMap_firm
#check ProximalScaling.proxMap_energy
#check ProximalScaling.proxMap_norm_sub_le
#check ProximalScaling.proxMap_lipschitz
#check ProximalScaling.proxMap_continuous
#check ProximalScaling.proxResidual_lipschitz
#check IsOneSmoothConvexFirstOrder.gradient_cocoercive
#check ProximalGradientCanonical.forwardStep
#check ProximalGradientCanonical.forwardBackwardStep
#check ProximalGradientCanonical.iterate_succ_eq_step
#check ProximalGradientCanonical.forwardStep_energy
#check ProximalGradientCanonical.forwardBackwardStep_energy
#check ProximalGradientCanonical.forwardBackwardStep_lipschitz
#check ProximalGradientCanonical.forwardBackwardStep_oracle_error
#check ProximalGradientCanonical.forwardBackwardStep_fixed_iff_minimizer
#check ProximalGradientCanonical.iterate_norm_sub_le
#check ProximalGradientCanonical.iterate_fejer_energy
#check ProximalGradientCanonical.iterate_distance_antitone
#check ProximalGradientCanonical.iterate_sum_step_energy
#check ProximalGradientCanonical.iterate_step_norm_antitone
#check ProximalGradientCanonical.iterate_last_step_norm_sq_le
#check ProximalGradientCanonical.iterate_step_norm_tendsto_zero
#check ProximalGradientCanonical.inexact_iterate_distance_le
#check ProximalGradientCanonical.inexact_gradient_distance_le
#check ProximalGradientCanonical.hilbertIterate_norm_sub_le
#check ProximalGradientCanonical.hilbertIterate_sum_step_energy
#check ProximalGradientCanonical.hilbertIterate_last_step_norm_sq_le
#check ProximalGradientCanonical.hilbertIterate_step_norm_tendsto_zero
#check ProximalGradientCanonical.hilbertIterate_inexact_distance_le

section Conditional
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- Supplied solutions suffice; neither continuity nor completeness is hidden.
example {L : ℝ≥0} {h : E → ℝ} {v w p q : E}
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h)
    (hp : IsProxPoint L h v p) (hq : IsProxPoint L h w q) :
    ‖p-q‖^2 + ‖(v-w)-(p-q)‖^2 ≤ ‖v-w‖^2 :=
  isProxPoint_energy hL hh hp hq

example {L : ℝ≥0} {h : E → ℝ} (hp : HasProx L h)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) : Continuous (proxMap hp) :=
  proxMap_continuous hp hL hh

example {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) (x : E) :
    forwardBackwardStep hp g x = x ↔ ∀ y, f x+h x ≤ f y+h y :=
  forwardBackwardStep_fixed_iff_minimizer hp hf hL hh x

example {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) (x0 y0 : E) (N : ℕ) :
    ‖iterate hp g x0 N-iterate hp g y0 N‖ ≤ ‖x0-y0‖ :=
  iterate_norm_sub_le hp hf hL hh x0 y0 N

-- Zero horizon remains an ordinary energy identity.
example {L : ℝ≥0} {f h : E → ℝ} {g : E → E} {xStar : E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h)
    (hm : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E) :
    ‖iterate hp g x0 0-xStar‖^2 +
      (1/2 : ℝ)*(∑ k ∈ Finset.range 0, ‖iterate hp g x0 (k+1)-iterate hp g x0 k‖^2) ≤
        ‖x0-xStar‖^2 :=
  iterate_sum_step_energy hp hf hL hh hm x0 0

example {L : ℝ≥0} {f h : E → ℝ} {g : E → E} {xStar : E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h)
    (hm : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E) :
    ‖iterate hp g x0 64-iterate hp g x0 63‖^2 ≤ 2*‖x0-xStar‖^2/(63+1 : ℝ) := by
  simpa only [Nat.cast_ofNat] using iterate_last_step_norm_sq_le hp hf hL hh hm x0 63

example {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h)
    (x0 : E) (z : ℕ → E) (eps : ℕ → ℝ) (N : ℕ)
    (he : ∀ k < N, ‖z (k+1)-forwardBackwardStep hp g (z k)‖ ≤ eps k) :
    ‖z N-iterate hp g x0 N‖ ≤ ‖z 0-x0‖ + ∑ k ∈ Finset.range N, eps k :=
  inexact_iterate_distance_le hp hf hL hh x0 z eps N he

example {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h)
    (x0 : E) (z e : ℕ → E) (N : ℕ)
    (he : ∀ k < N, z (k+1) = proxMap hp (z k-(L : ℝ)⁻¹ • (g (z k)+e k))) :
    ‖z N-iterate hp g x0 N‖ ≤ ‖z 0-x0‖ + ∑ k ∈ Finset.range N, (L : ℝ)⁻¹*‖e k‖ :=
  inexact_gradient_distance_le hp hf hL hh x0 z e N he
end Conditional

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- No finite dimension or user-supplied HasProx proof.
example {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hcont : Continuous h) (x0 y0 : E) (N : ℕ) :
    ‖hilbertIterate L h hL hh hcont g x0 N-hilbertIterate L h hL hh hcont g y0 N‖ ≤ ‖x0-y0‖ :=
  hilbertIterate_norm_sub_le hf hL hh hcont x0 y0 N

-- This states vanishing step norms, not pointwise convergence of the trajectory.
example {L : ℝ≥0} {f h : E → ℝ} {g : E → E} {xStar : E}
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hcont : Continuous h)
    (hm : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E) :
    Filter.Tendsto (fun k =>
      ‖hilbertIterate L h hL hh hcont g x0 (k+1)-hilbertIterate L h hL hh hcont g x0 k‖)
      Filter.atTop (𝓝 0) :=
  hilbertIterate_step_norm_tendsto_zero hf hL hh hcont hm x0
end Hilbert

-- The previously verified exact objective rate/tightness remains unchanged.
example : IsGreatest (oneDimensionalHilbertValues 7 3 2) (3/8 : ℝ) := by
  have ht := hilbert_tight_all 7 (L := 3) (R := 2) (by norm_num) (by norm_num)
  norm_num at ht ⊢
  exact ht

example (n : ℕ) {L : ℝ≥0} (hL : 0 < (L : ℝ)) :
    IsGreatest (oneDimensionalHilbertValues n L 0) 0 := by
  simpa using hilbert_tight_all n hL (le_refl (0 : ℝ))

#print axioms Proximal.subgradient_pair_monotone
#print axioms ProximalScaling.proxMap_lipschitz
#print axioms IsOneSmoothConvexFirstOrder.gradient_cocoercive
#print axioms ProximalGradientCanonical.forwardBackwardStep_energy
#print axioms ProximalGradientCanonical.iterate_sum_step_energy
#print axioms ProximalGradientCanonical.iterate_step_norm_tendsto_zero
#print axioms ProximalGradientCanonical.inexact_gradient_distance_le
#print axioms ProximalGradientCanonical.hilbertIterate_step_norm_tendsto_zero
