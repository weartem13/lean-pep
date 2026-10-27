import LeanPEP

open LeanPEP LeanPEP.ActualFunction
open ProximalScaling ProximalGradientCanonical Filter
open scoped NNReal Topology

#check FejerConvergence.tendsto_of_antitone_dist_of_subsequence
#check FejerConvergence.fixed_of_subsequence_of_residual
#check FejerConvergence.tendsto_fixed_of_subsequence
#check FejerConvergence.exists_tendsto_fixed_of_compact
#check ObjectiveConvergence.gap_tendsto_zero_of_succ_bound
#check ProximalGradientCanonical.iterate_residual_tendsto_zero
#check ProximalGradientCanonical.iterate_tendsto_of_subsequence
#check ProximalGradientCanonical.iterate_tendsto_of_compact
#check ProximalGradientCanonical.iterate_tendsto_finiteDimensional
#check ProximalGradientCanonical.finiteDimensionalIterate_tendsto_firstOrder
#check ProximalGradientCanonical.finiteDimensionalIterate_tendsto
#check ProximalGradientCanonical.finiteDimensionalIterate_tendsto_of_unique
#check ProximalGradientCanonical.run_tendsto_finiteDimensional
#check ProximalGradientCanonical.hilbertIterate_tendsto_of_compact
#check ProximalGradientCanonical.hilbertIterate_tendsto_finiteDimensional
#check ProximalGradientCanonical.run_objective_gap_tendsto_zero
#check ProximalGradientCanonical.run_objective_tendsto
#check ProximalGradientCanonical.iterate_objective_gap_tendsto_zero
#check ProximalGradientCanonical.iterate_objective_tendsto
#check ProximalGradientCanonical.hilbertIterate_objective_gap_tendsto_zero
#check ProximalGradientCanonical.hilbertIterate_objective_tendsto
#check ProximalGradientCanonical.finiteDimensionalIterate_objective_tendsto

-- Pure metric-space interface: no vector operations or dimension assumptions.
example {X : Type*} [MetricSpace X] {u : ℕ → X} {z : X} {φ : ℕ → ℕ}
    (ha : Antitone (fun k => dist (u k) z)) (hs : Tendsto (u ∘ φ) atTop (𝓝 z)) :
    Tendsto u atTop (𝓝 z) :=
  FejerConvergence.tendsto_of_antitone_dist_of_subsequence ha hs

-- The unbounded time-zero value is not constrained by the positive-time bound.
example {a : ℕ → ℝ} {C : ℝ} (ha : ∀ k, 0 ≤ a k)
    (hb : ∀ k, a (k+1) ≤ C/((k : ℝ)+1)) : Tendsto a atTop (𝓝 0) :=
  ObjectiveConvergence.gap_tendsto_zero_of_succ_bound ha hb

section General
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- Strong subsequence assumption is explicit in an arbitrary inner-product space.
example {L : ℝ≥0} {f h : E → ℝ} {g : E → E} {xStar x0 z : E} {φ : ℕ → ℕ}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h)
    (hm : ∀ y, f xStar+h xStar ≤ f y+h y) (hφ : StrictMono φ)
    (hs : Tendsto (iterate hp g x0 ∘ φ) atTop (𝓝 z)) :
    (∀ y, f z+h z ≤ f y+h y) ∧ Tendsto (iterate hp g x0) atTop (𝓝 z) :=
  iterate_tendsto_of_subsequence hp hf hL hh hm x0 hφ hs

-- Value convergence for a coherent external run, without total prox existence.
example {L : ℝ≥0} {f h : E → ℝ} {g : E → E} {xStar : E}
    (hf : IsSmoothConvexFirstOrder L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hm : ∀ y, f xStar+h xStar ≤ f y+h y)
    (x : ℕ → E) (hrun : ∀ N, ProximalGradientScaling.IsSmoothProxRun N L h g x) :
    Tendsto (fun k => f (x k)+h (x k)) atTop (𝓝 (f xStar+h xStar)) :=
  run_objective_tendsto hf hL hh hm x hrun
end General

section FiniteDimensional
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- Automatic existence: no supplied run, continuity, stationarity or HasProx.
example {L : ℝ≥0} {f h : E → ℝ} {g : E → E} {xStar : E}
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hm : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E) :
    ∃ z, (∀ y, f z+h z ≤ f y+h y) ∧
      Tendsto (finiteDimensionalIterate L h hL hh g x0) atTop (𝓝 z) :=
  finiteDimensionalIterate_tendsto hf hL hh hm x0

-- The first-order (not analysis-facing) contract also suffices.
example {L : ℝ≥0} {f h : E → ℝ} {g : E → E} {xStar : E}
    (hf : IsSmoothConvexFirstOrder L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hm : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E) :
    ∃ z, (∀ y, f z+h z ≤ f y+h y) ∧
      Tendsto (finiteDimensionalIterate L h hL hh g x0) atTop (𝓝 z) :=
  finiteDimensionalIterate_tendsto_firstOrder hf hL hh hm x0

-- A prescribed limit requires its own uniqueness hypothesis.
example {L : ℝ≥0} {f h : E → ℝ} {g : E → E} {xStar : E}
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hm : ∀ y, f xStar+h xStar ≤ f y+h y)
    (hu : ∀ z, (∀ y, f z+h z ≤ f y+h y) → z = xStar) (x0 : E) :
    Tendsto (finiteDimensionalIterate L h hL hh g x0) atTop (𝓝 xStar) :=
  finiteDimensionalIterate_tendsto_of_unique hf hL hh hm hu x0

-- Point and objective convergence have independent proofs and combine here.
example {L : ℝ≥0} {f h : E → ℝ} {g : E → E} {xStar : E}
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hm : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E) :
    ∃ z, (∀ y, f z+h z ≤ f y+h y) ∧
      Tendsto (finiteDimensionalIterate L h hL hh g x0) atTop (𝓝 z) ∧
      Tendsto (fun k => f (finiteDimensionalIterate L h hL hh g x0 k)+
        h (finiteDimensionalIterate L h hL hh g x0 k)) atTop (𝓝 (f xStar+h xStar)) := by
  obtain ⟨z, hz, ht⟩ := finiteDimensionalIterate_tendsto hf hL hh hm x0
  exact ⟨z, hz, ht, finiteDimensionalIterate_objective_tendsto hf hL hh hm x0⟩
end FiniteDimensional

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- No finite dimension or compact-orbit hypothesis for objective values.
example {L : ℝ≥0} {f h : E → ℝ} {g : E → E} {xStar : E}
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hc : Continuous h)
    (hm : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E) :
    Tendsto (fun k => f (hilbertIterate L h hL hh hc g x0 k)+
      h (hilbertIterate L h hL hh hc g x0 k)) atTop (𝓝 (f xStar+h xStar)) :=
  hilbertIterate_objective_tendsto hf hL hh hc hm x0

-- Norm convergence in an arbitrary Hilbert space keeps compactness explicit.
example {L : ℝ≥0} {f h : E → ℝ} {g : E → E} {xStar : E}
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hc : Continuous h)
    (hm : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E)
    {K : Set E} (hK : IsCompact K)
    (hmem : ∀ k, hilbertIterate L h hL hh hc g x0 k ∈ K) :
    ∃ z ∈ K, (∀ y, f z+h z ≤ f y+h y) ∧
      Tendsto (hilbertIterate L h hL hh hc g x0) atTop (𝓝 z) :=
  hilbertIterate_tendsto_of_compact hf hL hh hc hm x0 hK hmem
end Hilbert

-- The previous sharp finite-time result is not replaced by an asymptotic claim.
example : IsGreatest (oneDimensionalHilbertValues 7 3 2) (3/8 : ℝ) := by
  have ht := hilbert_tight_all 7 (L := 3) (R := 2) (by norm_num) (by norm_num)
  norm_num at ht ⊢
  exact ht

example (n : ℕ) {L : ℝ≥0} (hL : 0 < (L : ℝ)) :
    IsGreatest (oneDimensionalHilbertValues n L 0) 0 := by
  simpa using hilbert_tight_all n hL (le_refl (0 : ℝ))

#print axioms FejerConvergence.fixed_of_subsequence_of_residual
#print axioms FejerConvergence.exists_tendsto_fixed_of_compact
#print axioms ProximalGradientCanonical.iterate_tendsto_of_subsequence
#print axioms ProximalGradientCanonical.finiteDimensionalIterate_tendsto
#print axioms ProximalGradientCanonical.run_tendsto_finiteDimensional
#print axioms ProximalGradientCanonical.run_objective_gap_tendsto_zero
#print axioms ProximalGradientCanonical.hilbertIterate_objective_tendsto
