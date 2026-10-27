import LeanPEP.ActualFunction.ProximalIteration
import LeanPEP.ActualFunction.ProximalGradientMinimizer

/-!
# Exact proximal-gradient rates for an actual selected trajectory

C6 supplies the run instead of asking the caller to provide it. The generic
layer is conditional on proved total prox existence, and the finite-dimensional
layer discharges that premise for every real-valued convex h. All bounds use
the unchanged C5 minimizer interface, hence the original C2 compiler and C3B
certificate. The one-dimensional canonical value set equals C5's supplied-run
set for positive L. No new numerical rate or executable solver is claimed.
-/

noncomputable section
open scoped NNReal
namespace LeanPEP.ActualFunction.ProximalGradientCanonical

open ProximalScaling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Generic certificate application to the constructed trajectory. The three
original certificate guards remain explicit at this generic boundary. -/
theorem certificate_upper {n : ℕ}
    (c : GramPEP.UpperCertQ (Profiles.ProximalGradient.modelQ n))
    (hc : GramPEP.checkUpperCertQ c = true) (hempty : c.interpTerms = [])
    (hobj : c.objective = Profiles.ProximalGradient.objectiveQ n)
    {L : ℝ≥0} {R : ℝ} {f h : E → ℝ} {g : E → E} {xStar x0 : E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hh : ConvexOn ℝ Set.univ h) (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar + h xStar ≤ f y + h y) (hradius : ‖x0-xStar‖^2 ≤ R^2) :
    f (iterate hp g x0 (n+1)) + h (iterate hp g x0 (n+1)) - (f xStar + h xStar) ≤
      (L : ℝ)*R^2*(c.bound : ℝ) :=
  ProximalGradientScaling.certificate_upper_of_minimizer c hc hempty hobj
    hf hh hL hR hmin (iterate_isSmoothProxRun hp g x0 (n+1)) hradius

/-- The original exact bound on the constructed trajectory, without a supplied run. -/
theorem upper_firstOrder {n : ℕ} {L : ℝ≥0} {R : ℝ}
    {f h : E → ℝ} {g : E → E} {xStar x0 : E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hh : ConvexOn ℝ Set.univ h) (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar + h xStar ≤ f y + h y) (hradius : ‖x0-xStar‖^2 ≤ R^2) :
    f (iterate hp g x0 (n+1)) + h (iterate hp g x0 (n+1)) - (f xStar + h xStar) ≤
      (L : ℝ)*R^2/(4*((n : ℝ)+1)) :=
  ProximalGradientScaling.upper_firstOrder_of_minimizer hf hh hL hR hmin
    (iterate_isSmoothProxRun hp g x0 (n+1)) hradius

/-- Arbitrary Hilbert spaces retain the explicit existence premise here.
Finite-dimensionality is used only in the unconditional corollary below. -/
theorem upper_analytic_steps [CompleteSpace E] (T : ℕ) (hT : 0 < T)
    {L : ℝ≥0} {R : ℝ} {f h : E → ℝ} {g : E → E} {xStar x0 : E}
    (hp : HasProx L h) (hf : IsSmoothConvexAnalytic L f g)
    (hh : ConvexOn ℝ Set.univ h) (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar + h xStar ≤ f y + h y) (hradius : ‖x0-xStar‖^2 ≤ R^2) :
    f (iterate hp g x0 T) + h (iterate hp g x0 T) - (f xStar + h xStar) ≤
      (L : ℝ)*R^2/(4*(T : ℝ)) :=
  ProximalGradientScaling.upper_analytic_steps_of_minimizer T hT hf hh hL hR hmin
    (iterate_isSmoothProxRun hp g x0 T) hradius

/-- No supplied trajectory, prox existence, continuity, stationarity or checker
premise. Finite dimension and whole-space convexity prove the missing existence. -/
theorem upper_analytic_steps_finiteDimensional [FiniteDimensional ℝ E]
    (T : ℕ) (hT : 0 < T) {L : ℝ≥0} {R : ℝ}
    {f h : E → ℝ} {g : E → E} {xStar x0 : E}
    (hf : IsSmoothConvexAnalytic L f g) (hh : ConvexOn ℝ Set.univ h)
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar + h xStar ≤ f y + h y) (hradius : ‖x0-xStar‖^2 ≤ R^2) :
    f (finiteDimensionalIterate L h hL hh g x0 T) +
      h (finiteDimensionalIterate L h hL hh g x0 T) - (f xStar + h xStar) ≤
        (L : ℝ)*R^2/(4*(T : ℝ)) :=
  upper_analytic_steps T hT (hasProx_of_finiteDimensional hL hh) hf hh hL hR hmin hradius

/-- Exact initial distance, with no division by that distance. -/
theorem upper_analytic_exact_radius_finiteDimensional [FiniteDimensional ℝ E]
    (T : ℕ) (hT : 0 < T) {L : ℝ≥0} {f h : E → ℝ} {g : E → E} {xStar x0 : E}
    (hf : IsSmoothConvexAnalytic L f g) (hh : ConvexOn ℝ Set.univ h) (hL : 0 < (L : ℝ))
    (hmin : ∀ y, f xStar + h xStar ≤ f y + h y) :
    f (finiteDimensionalIterate L h hL hh g x0 T) +
      h (finiteDimensionalIterate L h hL hh g x0 T) - (f xStar + h xStar) ≤
        (L : ℝ)*‖x0-xStar‖^2/(4*(T : ℝ)) :=
  upper_analytic_steps_finiteDimensional T hT hf hh hL (norm_nonneg _) hmin (le_refl _)

/-- The constructed trajectory remains at any composite minimizer, including
nonzero component gradients which cancel. This covers every time index. -/
theorem iterate_at_minimizer {L : ℝ≥0} {f h : E → ℝ} {g : E → E} {xStar : E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hh : ConvexOn ℝ Set.univ h) (hL : 0 < (L : ℝ))
    (hmin : ∀ y, f xStar + h xStar ≤ f y + h y) (k : ℕ) :
    iterate hp g xStar k = xStar :=
  ProximalGradientScaling.stationary_run_of_minimizer hf hh hL hmin
    (iterate_isSmoothProxRun hp g xStar k) rfl k (le_refl _)

/-- The old linear witness is the canonical trajectory on its proved prefix.
It is not asserted to continue linearly beyond n+1. -/
theorem iterate_witness (n : ℕ) {L : ℝ≥0} {R : ℝ}
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) (k : ℕ) (hk : k ≤ n+1) :
    finiteDimensionalIterate L (ProximalGradientWitnessScaling.nonsmoothFunction n L R)
      hL (ProximalGradientWitnessScaling.nonsmooth_convex n L hR)
      (ProximalGradientWitnessScaling.smoothGradient L) R k =
        ProximalGradientWitnessScaling.witnessPoint n R k := by
  exact (run_eq_iterate (hasProx_of_finiteDimensional hL
      (ProximalGradientWitnessScaling.nonsmooth_convex n L hR)) hL
    (ProximalGradientWitnessScaling.nonsmooth_convex n L hR)
    (ProximalGradientWitnessScaling.actual_run n hL hR)
    (ProximalGradientWitnessScaling.witnessPoint_zero n R) k hk).symm

/-- Actual attainability by selected trajectories. No free trajectory or finite
Gram datum is quantified. The existence proof is internal to each instance. -/
def oneDimensionalValues (n : ℕ) (L : ℝ≥0) (R : ℝ) : Set ℝ :=
  {r | ∃ (f h g : ℝ → ℝ) (xStar x0 : ℝ) (hp : HasProx L h),
    IsSmoothConvexAnalytic L f g ∧ ConvexOn ℝ Set.univ h ∧
    (∀ y, f xStar + h xStar ≤ f y + h y) ∧ ‖x0-xStar‖^2 ≤ R^2 ∧
    f (iterate hp g x0 (n+1)) + h (iterate hp g x0 (n+1)) - (f xStar + h xStar) = r}

/-- Equality of full value sets, not just of their worst-case bounds. The reverse
direction proves existence in one dimension and identifies the whole prefix. -/
theorem oneDimensionalValues_eq_minimizerValues (n : ℕ) {L : ℝ≥0}
    (hL : 0 < (L : ℝ)) (R : ℝ) :
    oneDimensionalValues n L R = ProximalGradientScaling.oneDimensionalMinimizerValues n L R := by
  ext r
  constructor
  · rintro ⟨f, h, g, xStar, x0, hp, hf, hh, hmin, hr, hv⟩
    exact ⟨f, h, g, xStar, iterate hp g x0, hf, hh, hmin,
      iterate_isSmoothProxRun hp g x0 (n+1), hr, hv⟩
  · rintro ⟨f, h, g, xStar, x, hf, hh, hmin, hrun, hr, hv⟩
    let hp : HasProx L h := hasProx_of_finiteDimensional hL hh
    have heq := run_eq_iterate hp hL hh hrun rfl (n+1) (le_refl _)
    refine ⟨f, h, g, xStar, x 0, hp, hf, hh, hmin, hr, ?_⟩
    rw [← heq]
    exact hv

/-- The established actual lower is attained by the selected map as well. -/
theorem bound_mem (n : ℕ) {L : ℝ≥0} {R : ℝ} (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) :
    (L : ℝ)*R^2/(4*((n : ℝ)+1)) ∈ oneDimensionalValues n L R := by
  rw [oneDimensionalValues_eq_minimizerValues n hL R]
  exact ProximalGradientScaling.witness_mem_minimizerValues n hL hR

/-- Tightness for actual canonical iterates, including zero initial radius. -/
theorem tight_all (n : ℕ) {L : ℝ≥0} {R : ℝ} (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) :
    IsGreatest (oneDimensionalValues n L R) ((L : ℝ)*R^2/(4*((n : ℝ)+1))) := by
  rw [oneDimensionalValues_eq_minimizerValues n hL R]
  exact ProximalGradientScaling.minimizer_tight_all n hL hR

end LeanPEP.ActualFunction.ProximalGradientCanonical
