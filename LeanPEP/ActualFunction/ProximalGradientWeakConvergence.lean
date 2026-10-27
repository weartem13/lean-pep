import LeanPEP.ActualFunction.WeakFejerConvergence
import LeanPEP.ActualFunction.ProximalGradientConvergence
import LeanPEP.ActualFunction.ProximalGradientObjectiveConvergence

/-!
# Weak convergence of the unchanged proximal-gradient iteration

C8 supplies nonexpansiveness, Fejer monotonicity and vanishing residuals.
Hilbert weak compactness and bounded demiclosedness now close the arbitrary
Hilbert-space point-convergence theorem. C7 supplies total prox solvability
when h is continuous. No separability, finite dimension, norm-compact orbit,
unique minimizer, new recursive algorithm or new certificate is assumed.
The limit is some minimizer, not necessarily the reference point or its
metric projection. Objective convergence remains the independent C9 result.
-/

noncomputable section
open Filter
open scoped NNReal Topology
namespace LeanPEP.ActualFunction.ProximalGradientCanonical
open ProximalScaling HilbertWeakTopology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A weak cluster point of the existing orbit is a composite minimizer.
This is obtained from demiclosedness, NOT weak continuity of the prox map. -/
theorem iterate_minimizer_of_weakRiesz_cluster {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E) {z : E}
    (hz : MapClusterPt (weakRiesz z) atTop (fun n => weakRiesz (iterate hp g x0 n))) :
    ∀ y, f z+h z ≤ f y+h y := by
  have hB (n : ℕ) : ‖iterate hp g x0 n-xStar‖ ≤ ‖x0-xStar‖ := by
    simpa only [iterate_zero] using
      (iterate_distance_antitone hp hf hL hh hmin x0) (Nat.zero_le n)
  have hres : Tendsto (fun n =>
      ‖forwardBackwardStep hp g (iterate hp g x0 n)-iterate hp g x0 n‖) atTop (𝓝 0) := by
    simpa only [dist_eq_norm] using iterate_residual_tendsto_zero hp hf hL hh hmin x0
  have hfixed := WeakFejerConvergence.fixed_of_weakRiesz_cluster
    (forwardBackwardStep_norm_sub_le hp hf hL hh) hB hres hz
  exact (forwardBackwardStep_fixed_iff_minimizer hp hf hL hh z).mp hfixed

/-- Full weak convergence in an arbitrary real Hilbert space, conditional
only on the original total prox-existence proof. -/
theorem iterate_weak_tendsto [CompleteSpace E]
    {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E) :
    ∃ z, (∀ y, f z+h z ≤ f y+h y) ∧
      Tendsto (fun n => toWeakSpace ℝ E (iterate hp g x0 n))
        atTop (𝓝 (toWeakSpace ℝ E z)) := by
  have hres : Tendsto (fun n =>
      ‖forwardBackwardStep hp g (iterate hp g x0 n)-iterate hp g x0 n‖) atTop (𝓝 0) := by
    simpa only [dist_eq_norm] using iterate_residual_tendsto_zero hp hf hL hh hmin x0
  have hfejer (z : E) (hz : forwardBackwardStep hp g z = z) :
      Antitone (fun n => ‖iterate hp g x0 n-z‖) :=
    iterate_distance_antitone hp hf hL hh
      ((forwardBackwardStep_fixed_iff_minimizer hp hf hL hh z).mp hz) x0
  obtain ⟨z, hz, ht⟩ := WeakFejerConvergence.exists_weak_tendsto_fixed
    (forwardBackwardStep_norm_sub_le hp hf hL hh) hres hfejer xStar
    (forwardBackwardStep_fixed_of_minimizer hp hf hL hh hmin)
  exact ⟨z, (forwardBackwardStep_fixed_iff_minimizer hp hf hL hh z).mp hz, ht⟩

/-- Explicit inner-product test characterization of the same weak limit. -/
theorem iterate_weak_tendsto_inner [CompleteSpace E]
    {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E) :
    ∃ z, (∀ y, f z+h z ≤ f y+h y) ∧
      ∀ v : E, Tendsto (fun n => inner ℝ (iterate hp g x0 n) v)
        atTop (𝓝 (inner ℝ z v)) := by
  obtain ⟨z, hz, ht⟩ := iterate_weak_tendsto hp hf hL hh hmin x0
  exact ⟨z, hz, weakSpace_tendsto_iff_inner.mp ht⟩

/-- A separate uniqueness assumption is needed to identify the weak limit with
an arbitrarily supplied reference minimizer. -/
theorem iterate_weak_tendsto_of_unique [CompleteSpace E]
    {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y)
    (hunique : ∀ z, (∀ y, f z+h z ≤ f y+h y) → z = xStar) (x0 : E) :
    Tendsto (fun n => toWeakSpace ℝ E (iterate hp g x0 n))
      atTop (𝓝 (toWeakSpace ℝ E xStar)) := by
  obtain ⟨z, hz, ht⟩ := iterate_weak_tendsto hp hf hL hh hmin x0
  rw [hunique z hz] at ht
  exact ht

/-- C7 discharges total prox existence for continuous full-domain convex h. -/
theorem hilbertIterate_weak_tendsto_firstOrder [CompleteSpace E]
    {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hf : IsSmoothConvexFirstOrder L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hcont : Continuous h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E) :
    ∃ z, (∀ y, f z+h z ≤ f y+h y) ∧
      Tendsto (fun n => toWeakSpace ℝ E (hilbertIterate L h hL hh hcont g x0 n))
        atTop (𝓝 (toWeakSpace ℝ E z)) :=
  iterate_weak_tendsto (hasProx_of_continuous hL hh hcont) hf hL hh hmin x0

/-- Analysis-facing infinite-dimensional weak convergence. No HasProx, given
run, compact orbit, separability or unique minimizer premise is exposed. -/
theorem hilbertIterate_weak_tendsto [CompleteSpace E]
    {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hcont : Continuous h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E) :
    ∃ z, (∀ y, f z+h z ≤ f y+h y) ∧
      Tendsto (fun n => toWeakSpace ℝ E (hilbertIterate L h hL hh hcont g x0 n))
        atTop (𝓝 (toWeakSpace ℝ E z)) :=
  hilbertIterate_weak_tendsto_firstOrder hf.toFirstOrder hL hh hcont hmin x0

/-- Every continuous linear functional sees convergence to the same minimizer. -/
theorem hilbertIterate_weak_tendsto_dual [CompleteSpace E]
    {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hcont : Continuous h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E) :
    ∃ z, (∀ y, f z+h z ≤ f y+h y) ∧
      ∀ a : StrongDual ℝ E, Tendsto
        (fun n => a (hilbertIterate L h hL hh hcont g x0 n)) atTop (𝓝 (a z)) := by
  obtain ⟨z, hz, ht⟩ := hilbertIterate_weak_tendsto hf hL hh hcont hmin x0
  exact ⟨z, hz, weakSpace_tendsto_iff_dual.mp ht⟩

/-- An externally provided coherent infinite run has the same weak limit.
The conditional version retains the old total-prox premise. -/
theorem run_weak_tendsto [CompleteSpace E]
    {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) (x : ℕ → E)
    (hrun : ∀ N, ProximalGradientScaling.IsSmoothProxRun N L h g x) :
    ∃ z, (∀ y, f z+h z ≤ f y+h y) ∧
      Tendsto (fun n => toWeakSpace ℝ E (x n)) atTop (𝓝 (toWeakSpace ℝ E z)) := by
  have hfun : x = iterate hp g (x 0) := by
    funext n
    exact run_eq_iterate hp hL hh (hrun n) rfl n (le_refl n)
  obtain ⟨z, hz, ht⟩ := iterate_weak_tendsto hp hf hL hh hmin (x 0)
  have hmap : (fun n => toWeakSpace ℝ E (x n)) =
      (fun n => toWeakSpace ℝ E (iterate hp g (x 0) n)) := by
    funext n
    exact congrArg (toWeakSpace ℝ E) (congrFun hfun n)
  refine ⟨z, hz, ?_⟩
  rw [hmap]
  exact ht

/-- Continuous h makes the external-run conclusion unconditional in HasProx. -/
theorem run_weak_tendsto_hilbert [CompleteSpace E]
    {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hcont : Continuous h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) (x : ℕ → E)
    (hrun : ∀ N, ProximalGradientScaling.IsSmoothProxRun N L h g x) :
    ∃ z, (∀ y, f z+h z ≤ f y+h y) ∧
      Tendsto (fun n => toWeakSpace ℝ E (x n)) atTop (𝓝 (toWeakSpace ℝ E z)) :=
  run_weak_tendsto (hasProx_of_continuous hL hh hcont) hf.toFirstOrder hL hh hmin x hrun

/-- Weak point convergence and C9 objective convergence for one fixed problem.
The objective limit is NOT inferred from weak continuity of f+h. -/
theorem hilbertIterate_weak_and_objective_tendsto [CompleteSpace E]
    {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hcont : Continuous h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E) :
    ∃ z, (∀ y, f z+h z ≤ f y+h y) ∧
      Tendsto (fun n => toWeakSpace ℝ E (hilbertIterate L h hL hh hcont g x0 n))
        atTop (𝓝 (toWeakSpace ℝ E z)) ∧
      Tendsto (fun n => f (hilbertIterate L h hL hh hcont g x0 n) +
        h (hilbertIterate L h hL hh hcont g x0 n)) atTop (𝓝 (f z+h z)) := by
  obtain ⟨z, hz, ht⟩ := hilbertIterate_weak_tendsto hf hL hh hcont hmin x0
  exact ⟨z, hz, ht, hilbertIterate_objective_tendsto hf hL hh hcont hz x0⟩

/-- C9 strong limits and C10 weak limits agree wherever both are supplied.
This does not turn weak convergence into strong convergence. -/
theorem hilbertIterate_strong_weak_limits_eq [CompleteSpace E]
    {L : ℝ≥0} {h : E → ℝ} {g : E → E}
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) (hcont : Continuous h)
    (x0 : E) {z w : E}
    (hz : Tendsto (hilbertIterate L h hL hh hcont g x0) atTop (𝓝 z))
    (hw : Tendsto (fun n => toWeakSpace ℝ E (hilbertIterate L h hL hh hcont g x0 n))
      atTop (𝓝 (toWeakSpace ℝ E w))) : z = w :=
  WeakFejerConvergence.eq_of_strong_and_weak_limits hz hw

end LeanPEP.ActualFunction.ProximalGradientCanonical
