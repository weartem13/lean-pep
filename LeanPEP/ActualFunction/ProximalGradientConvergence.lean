import LeanPEP.ActualFunction.FejerConvergence
import LeanPEP.ActualFunction.ProximalGradientStability
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Strong convergence of the existing proximal-gradient iteration

C8 supplies residual decay, nonexpansiveness, and Fejer monotonicity. This file
first proves convergence conditional on a norm-convergent subsequence or a
compact orbit. Only the automatic subsequence extraction uses finite dimension.
The limit is some composite minimizer, not necessarily the reference minimizer
used to bound the orbit. No uniqueness of minimizers, strict convexity, point
convergence rate, new recursive algorithm, or new PEP certificate is assumed.
-/

noncomputable section
open Filter Metric
open scoped NNReal Topology
namespace LeanPEP.ActualFunction.ProximalGradientCanonical
open ProximalScaling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Express C8 asymptotic regularity as decay of the same map's metric residual. -/
theorem iterate_residual_tendsto_zero {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E) :
    Tendsto (fun k => dist (forwardBackwardStep hp g (iterate hp g x0 k))
      (iterate hp g x0 k)) atTop (𝓝 0) := by
  have hfun : (fun k => dist (forwardBackwardStep hp g (iterate hp g x0 k))
      (iterate hp g x0 k)) =
      (fun k => ‖iterate hp g x0 (k+1)-iterate hp g x0 k‖) := by
    funext k
    rw [dist_eq_norm, ← iterate_succ_eq_step hp g x0 k]
  rw [hfun]
  exact iterate_step_norm_tendsto_zero hp hf hL hh hmin x0

/-- A norm cluster point is a minimizer and attracts the entire sequence.
This implication does not require finite dimension or completeness. -/
theorem iterate_tendsto_of_subsequence {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E)
    {z : E} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hsub : Tendsto (iterate hp g x0 ∘ φ) atTop (𝓝 z)) :
    (∀ y, f z+h z ≤ f y+h y) ∧ Tendsto (iterate hp g x0) atTop (𝓝 z) := by
  have hfejer (w : E) (hw : forwardBackwardStep hp g w = w) :
      Antitone (fun k => dist (iterate hp g x0 k) w) := by
    have hm := (forwardBackwardStep_fixed_iff_minimizer hp hf hL hh w).mp hw
    simpa only [dist_eq_norm] using iterate_distance_antitone hp hf hL hh hm x0
  have ht := FejerConvergence.tendsto_fixed_of_subsequence
    (forwardBackwardStep_lipschitz hp hf hL hh).continuous
    (iterate_residual_tendsto_zero hp hf hL hh hmin x0) hfejer hφ.tendsto_atTop hsub
  exact ⟨(forwardBackwardStep_fixed_iff_minimizer hp hf hL hh z).mp ht.1, ht.2⟩

/-- A compact containing set is an explicit premise in an arbitrary space. -/
theorem iterate_tendsto_of_compact {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E)
    {K : Set E} (hK : IsCompact K) (hmem : ∀ k, iterate hp g x0 k ∈ K) :
    ∃ z ∈ K, (∀ y, f z+h z ≤ f y+h y) ∧ Tendsto (iterate hp g x0) atTop (𝓝 z) := by
  obtain ⟨z, hz, φ, hφ, hsub⟩ := hK.tendsto_subseq hmem
  exact ⟨z, hz, iterate_tendsto_of_subsequence hp hf hL hh hmin x0 hφ hsub⟩

/-- The original first-order contract suffices. Finite dimension is used only
for compactness of the Fejer ball. No unique-minimizer assumption is made. -/
theorem iterate_tendsto_finiteDimensional [FiniteDimensional ℝ E]
    {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E) :
    ∃ z, (∀ y, f z+h z ≤ f y+h y) ∧ Tendsto (iterate hp g x0) atTop (𝓝 z) := by
  have hmem (k : ℕ) : iterate hp g x0 k ∈ Metric.closedBall xStar ‖x0-xStar‖ := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    simpa only [iterate_zero] using
      (iterate_distance_antitone hp hf hL hh hmin x0) (Nat.zero_le k)
  obtain ⟨z, _, hz⟩ := iterate_tendsto_of_compact hp hf hL hh hmin x0
    (isCompact_closedBall xStar ‖x0-xStar‖) hmem
  exact ⟨z, hz⟩

/-- Automatic finite-dimensional prox existence and strong convergence, without
a supplied trajectory, HasProx proof, continuity of h, or stationarity witness. -/
theorem finiteDimensionalIterate_tendsto_firstOrder [FiniteDimensional ℝ E]
    {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hf : IsSmoothConvexFirstOrder L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E) :
    ∃ z, (∀ y, f z+h z ≤ f y+h y) ∧
      Tendsto (finiteDimensionalIterate L h hL hh g x0) atTop (𝓝 z) :=
  iterate_tendsto_finiteDimensional (hasProx_of_finiteDimensional hL hh) hf hL hh hmin x0

/-- Analysis-facing version for the unchanged actual finite-dimensional iterate. -/
theorem finiteDimensionalIterate_tendsto [FiniteDimensional ℝ E]
    {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E) :
    ∃ z, (∀ y, f z+h z ≤ f y+h y) ∧
      Tendsto (finiteDimensionalIterate L h hL hh g x0) atTop (𝓝 z) :=
  finiteDimensionalIterate_tendsto_firstOrder hf.toFirstOrder hL hh hmin x0

/-- Only under a separate uniqueness hypothesis may the limit be identified
with the supplied reference minimizer. -/
theorem finiteDimensionalIterate_tendsto_of_unique [FiniteDimensional ℝ E]
    {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y)
    (hunique : ∀ z, (∀ y, f z+h z ≤ f y+h y) → z = xStar) (x0 : E) :
    Tendsto (finiteDimensionalIterate L h hL hh g x0) atTop (𝓝 xStar) := by
  obtain ⟨z, hzmin, hzlim⟩ := finiteDimensionalIterate_tendsto hf hL hh hmin x0
  rw [hunique z hzmin] at hzlim
  exact hzlim

/-- An externally defined infinite run converges too, by the existing prefix
uniqueness theorem. One coherent run for all horizons is explicitly required. -/
theorem run_tendsto_finiteDimensional [FiniteDimensional ℝ E]
    {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) (x : ℕ → E)
    (hrun : ∀ N, ProximalGradientScaling.IsSmoothProxRun N L h g x) :
    ∃ z, (∀ y, f z+h z ≤ f y+h y) ∧ Tendsto x atTop (𝓝 z) := by
  let hp : HasProx L h := hasProx_of_finiteDimensional hL hh
  have hfun : x = iterate hp g (x 0) := by
    funext k
    exact run_eq_iterate hp hL hh (hrun k) rfl k (le_refl k)
  rw [hfun]
  exact iterate_tendsto_finiteDimensional hp hf.toFirstOrder hL hh hmin (x 0)

/-- A Hilbert-space statement with compactness still explicit. Boundedness is
not substituted for compactness in infinite dimension. -/
theorem hilbertIterate_tendsto_of_compact [CompleteSpace E]
    {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hcont : Continuous h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E)
    {K : Set E} (hK : IsCompact K)
    (hmem : ∀ k, hilbertIterate L h hL hh hcont g x0 k ∈ K) :
    ∃ z ∈ K, (∀ y, f z+h z ≤ f y+h y) ∧
      Tendsto (hilbertIterate L h hL hh hcont g x0) atTop (𝓝 z) :=
  iterate_tendsto_of_compact (hasProx_of_continuous hL hh hcont)
    hf.toFirstOrder hL hh hmin x0 hK hmem

/-- In finite dimension the C7 and C6 whole-sequence compatibility transfers
the point convergence result to hilbertIterate. -/
theorem hilbertIterate_tendsto_finiteDimensional [FiniteDimensional ℝ E]
    {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hcont : Continuous h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E) :
    ∃ z, (∀ y, f z+h z ≤ f y+h y) ∧
      Tendsto (hilbertIterate L h hL hh hcont g x0) atTop (𝓝 z) := by
  rw [hilbertIterate_eq_finiteDimensional L h hL hh hcont g x0]
  exact finiteDimensionalIterate_tendsto hf hL hh hmin x0

end LeanPEP.ActualFunction.ProximalGradientCanonical
