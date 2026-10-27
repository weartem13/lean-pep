import LeanPEP

open LeanPEP LeanPEP.ActualFunction
open HilbertWeakTopology WeakFejerConvergence ProximalScaling ProximalGradientCanonical Filter
open scoped NNReal Topology

#check HilbertWeakTopology.weakRiesz
#check HilbertWeakTopology.weakRiesz_apply
#check HilbertWeakTopology.weakRiesz_injective
#check HilbertWeakTopology.weakRiesz_tendsto_iff_inner
#check HilbertWeakTopology.dualPairing_injective
#check HilbertWeakTopology.weakSpace_tendsto_iff_dual
#check HilbertWeakTopology.weakSpace_tendsto_iff_inner
#check HilbertWeakTopology.weakSpace_tendsto_of_tendsto
#check HilbertWeakTopology.weakRiesz_surjective
#check HilbertWeakTopology.weakRiesz_closedBall_image
#check HilbertWeakTopology.isCompact_weakRiesz_closedBall
#check HilbertWeakTopology.inner_subfilter_of_weakRiesz_cluster
#check WeakFejerConvergence.fixed_defect_bound
#check WeakFejerConvergence.fixed_of_inner_tendsto_of_residual
#check WeakFejerConvergence.distance_sq_difference
#check WeakFejerConvergence.distance_sq_difference_tendsto
#check WeakFejerConvergence.inner_limits_eq_of_antitone
#check WeakFejerConvergence.fixed_of_weakRiesz_cluster
#check WeakFejerConvergence.weakRiesz_clusters_eq
#check WeakFejerConvergence.exists_weak_tendsto_fixed
#check WeakFejerConvergence.eq_of_strong_and_weak_limits
#check ProximalGradientCanonical.iterate_minimizer_of_weakRiesz_cluster
#check ProximalGradientCanonical.iterate_weak_tendsto
#check ProximalGradientCanonical.iterate_weak_tendsto_inner
#check ProximalGradientCanonical.iterate_weak_tendsto_of_unique
#check ProximalGradientCanonical.hilbertIterate_weak_tendsto_firstOrder
#check ProximalGradientCanonical.hilbertIterate_weak_tendsto
#check ProximalGradientCanonical.hilbertIterate_weak_tendsto_dual
#check ProximalGradientCanonical.run_weak_tendsto
#check ProximalGradientCanonical.run_weak_tendsto_hilbert
#check ProximalGradientCanonical.hilbertIterate_weak_and_objective_tendsto
#check ProximalGradientCanonical.hilbertIterate_strong_weak_limits_eq

section General
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- The actual mathlib weak topology is tested by all continuous linear functionals.
example {α : Type*} {l : Filter α} {u : α → E} {z : E} :
    Tendsto (fun i => toWeakSpace ℝ E (u i)) l (𝓝 (toWeakSpace ℝ E z)) ↔
      ∀ a : StrongDual ℝ E, Tendsto (fun i => a (u i)) l (𝓝 (a z)) :=
  weakSpace_tendsto_iff_dual

-- Demiclosedness is available for filters, not merely increasing subsequences.
-- Nontriviality and boundedness must not be removed.
example {α : Type*} {l : Filter α} [l.NeBot] {T : E → E} {u : α → E} {z : E} {B : ℝ}
    (hT : ∀ x y, ‖T x-T y‖ ≤ ‖x-y‖) (hB : ∀ i, ‖u i-z‖ ≤ B)
    (hw : ∀ v : E, Tendsto (fun i => inner ℝ (u i) v) l (𝓝 (inner ℝ z v)))
    (hr : Tendsto (fun i => ‖T (u i)-u i‖) l (𝓝 0)) : T z = z :=
  fixed_of_inner_tendsto_of_residual hT hB hw hr

example {u : ℕ → E} {z : E}
    (hz : MapClusterPt (weakRiesz z) atTop (fun n => weakRiesz (u n))) :
    ∃ l : Filter ℕ, l.NeBot ∧ l ≤ atTop ∧
      ∀ v : E, Tendsto (fun n => inner ℝ (u n) v) l (𝓝 (inner ℝ z v)) :=
  inner_subfilter_of_weakRiesz_cluster hz
end General

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- No FiniteDimensional, SeparableSpace, or norm-compact orbit premise.
example (center : E) (R : ℝ) :
    IsCompact (weakRiesz '' Metric.closedBall center R) :=
  isCompact_weakRiesz_closedBall center R

example {u : ℕ → E} {z : E} :
    Tendsto (fun n => toWeakSpace ℝ E (u n)) atTop (𝓝 (toWeakSpace ℝ E z)) ↔
      ∀ v : E, Tendsto (fun n => inner ℝ (u n) v) atTop (𝓝 (inner ℝ z v)) :=
  weakSpace_tendsto_iff_inner

example {T : E → E} {u : ℕ → E}
    (hT : ∀ x y, ‖T x-T y‖ ≤ ‖x-y‖)
    (hr : Tendsto (fun n => ‖T (u n)-u n‖) atTop (𝓝 0))
    (hF : ∀ z, T z = z → Antitone (fun n => ‖u n-z‖)) (p : E) (hp : T p = p) :
    ∃ z, T z = z ∧
      Tendsto (fun n => toWeakSpace ℝ E (u n)) atTop (𝓝 (toWeakSpace ℝ E z)) :=
  exists_weak_tendsto_fixed hT hr hF p hp

-- First-order version retains only the original prox solvability proof.
example {L : ℝ≥0} {f h : E → ℝ} {g : E → E} {xStar : E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hm : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E) :
    ∃ z, (∀ y, f z+h z ≤ f y+h y) ∧
      Tendsto (fun n => toWeakSpace ℝ E (iterate hp g x0 n)) atTop (𝓝 (toWeakSpace ℝ E z)) :=
  iterate_weak_tendsto hp hf hL hh hm x0

-- Analysis-facing version constructs its own prox map via the unchanged C7 result.
example {L : ℝ≥0} {f h : E → ℝ} {g : E → E} {xStar : E}
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hc : Continuous h)
    (hm : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E) :
    ∃ z, (∀ y, f z+h z ≤ f y+h y) ∧
      Tendsto (fun n => toWeakSpace ℝ E (hilbertIterate L h hL hh hc g x0 n))
        atTop (𝓝 (toWeakSpace ℝ E z)) :=
  hilbertIterate_weak_tendsto hf hL hh hc hm x0

example {L : ℝ≥0} {f h : E → ℝ} {g : E → E} {xStar : E}
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hc : Continuous h)
    (hm : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E) :
    ∃ z, (∀ y, f z+h z ≤ f y+h y) ∧ ∀ a : StrongDual ℝ E,
      Tendsto (fun n => a (hilbertIterate L h hL hh hc g x0 n)) atTop (𝓝 (a z)) :=
  hilbertIterate_weak_tendsto_dual hf hL hh hc hm x0

-- One sequence and one minimizer; objective convergence is not a weak-continuity assertion.
example {L : ℝ≥0} {f h : E → ℝ} {g : E → E} {xStar : E}
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hc : Continuous h)
    (hm : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E) :
    ∃ z, (∀ y, f z+h z ≤ f y+h y) ∧
      Tendsto (fun n => toWeakSpace ℝ E (hilbertIterate L h hL hh hc g x0 n))
        atTop (𝓝 (toWeakSpace ℝ E z)) ∧
      Tendsto (fun n => f (hilbertIterate L h hL hh hc g x0 n)+
        h (hilbertIterate L h hL hh hc g x0 n)) atTop (𝓝 (f z+h z)) :=
  hilbertIterate_weak_and_objective_tendsto hf hL hh hc hm x0

-- The external sequence must be one coherent infinite run.
example {L : ℝ≥0} {f h : E → ℝ} {g : E → E} {xStar : E}
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hc : Continuous h)
    (hm : ∀ y, f xStar+h xStar ≤ f y+h y) (x : ℕ → E)
    (hr : ∀ N, ProximalGradientScaling.IsSmoothProxRun N L h g x) :
    ∃ z, (∀ y, f z+h z ≤ f y+h y) ∧
      Tendsto (fun n => toWeakSpace ℝ E (x n)) atTop (𝓝 (toWeakSpace ℝ E z)) :=
  run_weak_tendsto_hilbert hf hL hh hc hm x hr

-- A specified reference is the limit only under a separate uniqueness premise.
example {L : ℝ≥0} {f h : E → ℝ} {g : E → E} {xStar : E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hm : ∀ y, f xStar+h xStar ≤ f y+h y)
    (hu : ∀ z, (∀ y, f z+h z ≤ f y+h y) → z = xStar) (x0 : E) :
    Tendsto (fun n => toWeakSpace ℝ E (iterate hp g x0 n)) atTop (𝓝 (toWeakSpace ℝ E xStar)) :=
  iterate_weak_tendsto_of_unique hp hf hL hh hm hu x0

-- Compatibility does NOT infer norm convergence from weak convergence.
example {u : ℕ → E} {z w : E} (hz : Tendsto u atTop (𝓝 z))
    (hw : Tendsto (fun n => toWeakSpace ℝ E (u n)) atTop (𝓝 (toWeakSpace ℝ E w))) : z = w :=
  eq_of_strong_and_weak_limits hz hw
end Hilbert

-- Previous finite-time exact values and zero-radius boundary remain intact.
example : IsGreatest (oneDimensionalHilbertValues 7 3 2) (3/8 : ℝ) := by
  have ht := hilbert_tight_all 7 (L := 3) (R := 2) (by norm_num) (by norm_num)
  norm_num at ht ⊢
  exact ht

example (n : ℕ) {L : ℝ≥0} (hL : 0 < (L : ℝ)) :
    IsGreatest (oneDimensionalHilbertValues n L 0) 0 := by
  simpa using hilbert_tight_all n hL (le_refl (0 : ℝ))

#print axioms HilbertWeakTopology.weakSpace_tendsto_iff_inner
#print axioms HilbertWeakTopology.isCompact_weakRiesz_closedBall
#print axioms HilbertWeakTopology.inner_subfilter_of_weakRiesz_cluster
#print axioms WeakFejerConvergence.fixed_of_inner_tendsto_of_residual
#print axioms WeakFejerConvergence.inner_limits_eq_of_antitone
#print axioms WeakFejerConvergence.exists_weak_tendsto_fixed
#print axioms ProximalGradientCanonical.hilbertIterate_weak_tendsto
#print axioms ProximalGradientCanonical.hilbertIterate_weak_and_objective_tendsto
