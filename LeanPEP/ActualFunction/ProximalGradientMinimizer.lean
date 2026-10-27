import LeanPEP.ActualFunction.ProximalGradientMinimizerCore
import LeanPEP.ActualFunction.CompositeOptimality
import LeanPEP.ActualFunction.ProximalGradientWitnessScaling

/-!
# The existing exact proximal-gradient rate at an ordinary minimizer

This file replaces the caller-supplied subgradient certificate with global
minimality of the composite objective. It invokes C5 optimality extraction,
then the unchanged C4 physical-run bridge and C3B all-horizon certificate.
The old stationarity-facing API remains intact.

The new actual value set is proved equal to the old actual value set, not
merely bounded by the same number. It does not quantify over Gram data or
accepted certificates. No prox existence theorem or extended-real h is added.
-/

noncomputable section
open scoped NNReal
namespace LeanPEP.ActualFunction.ProximalGradientScaling

open Proximal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exact rate from first-order models and global composite minimality. -/
theorem upper_firstOrder_of_minimizer {n : ℕ} {L : ℝ≥0} {R : ℝ}
    {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsSmoothConvexFirstOrder L f g) (hh : ConvexOn ℝ Set.univ h)
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar + h xStar ≤ f y + h y)
    (hrun : IsSmoothProxRun (n+1) L h g x) (hradius : ‖x 0-xStar‖^2 ≤ R^2) :
    f (x (n+1)) + h (x (n+1)) - (f xStar + h xStar) ≤
      (L : ℝ)*R^2/(4*((n : ℝ)+1)) :=
  upper_firstOrder hf hh hL hR (subgradient_of_composite_minimizer hf hh hmin) hrun hradius

/-- Analysis-facing rate without a caller-supplied stationarity certificate. -/
theorem upper_analytic_of_minimizer [CompleteSpace E] {n : ℕ} {L : ℝ≥0} {R : ℝ}
    {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsSmoothConvexAnalytic L f g) (hh : ConvexOn ℝ Set.univ h)
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar + h xStar ≤ f y + h y)
    (hrun : IsSmoothProxRun (n+1) L h g x) (hradius : ‖x 0-xStar‖^2 ≤ R^2) :
    f (x (n+1)) + h (x (n+1)) - (f xStar + h xStar) ≤
      (L : ℝ)*R^2/(4*((n : ℝ)+1)) :=
  upper_firstOrder_of_minimizer hf.toFirstOrder hh hL hR hmin hrun hradius

/-- Actual positive step count T, retaining step size 1/L. -/
theorem upper_analytic_steps_of_minimizer [CompleteSpace E] (T : ℕ) (hT : 0 < T)
    {L : ℝ≥0} {R : ℝ} {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsSmoothConvexAnalytic L f g) (hh : ConvexOn ℝ Set.univ h)
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar + h xStar ≤ f y + h y)
    (hrun : IsSmoothProxRun T L h g x) (hradius : ‖x 0-xStar‖^2 ≤ R^2) :
    f (x T) + h (x T) - (f xStar + h xStar) ≤ (L : ℝ)*R^2/(4*(T : ℝ)) :=
  upper_analytic_steps T hT hf hh hL hR
    (subgradient_of_composite_minimizer hf.toFirstOrder hh hmin) hrun hradius

/-- No separate radius parameter is necessary for an exact-distance bound. -/
theorem upper_analytic_exact_radius_of_minimizer [CompleteSpace E] {n : ℕ} {L : ℝ≥0}
    {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsSmoothConvexAnalytic L f g) (hh : ConvexOn ℝ Set.univ h)
    (hL : 0 < (L : ℝ)) (hmin : ∀ y, f xStar + h xStar ≤ f y + h y)
    (hrun : IsSmoothProxRun (n+1) L h g x) :
    f (x (n+1)) + h (x (n+1)) - (f xStar + h xStar) ≤
      (L : ℝ)*‖x 0-xStar‖^2/(4*((n : ℝ)+1)) :=
  upper_analytic_exact_radius hf hh hL
    (subgradient_of_composite_minimizer hf.toFirstOrder hh hmin) hrun

/-- Starting at a composite minimizer fixes any supplied finite run, even when
neither component is individually stationary. This includes the zero-radius case. -/
theorem stationary_run_of_minimizer {N : ℕ} {L : ℝ≥0}
    {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsSmoothConvexFirstOrder L f g) (hh : ConvexOn ℝ Set.univ h)
    (hL : 0 < (L : ℝ)) (hmin : ∀ y, f xStar + h xStar ≤ f y + h y)
    (hrun : IsSmoothProxRun N L h g x) (hx0 : x 0 = xStar) (k : ℕ) (hk : k ≤ N) :
    x k = xStar :=
  stationary_run hL (subgradient_of_composite_minimizer hf hh hmin) hrun hx0 k hk

/-- Natural actual-function value set: global minimum replaces explicit support.
As before, the compiler parameter n represents n+1 physical steps. -/
def oneDimensionalMinimizerValues (n : ℕ) (L : ℝ≥0) (R : ℝ) : Set ℝ :=
  {r | ∃ (f h g : ℝ → ℝ) (xStar : ℝ) (x : ℕ → ℝ),
    IsSmoothConvexAnalytic L f g ∧ ConvexOn ℝ Set.univ h ∧
    (∀ y, f xStar + h xStar ≤ f y + h y) ∧ IsSmoothProxRun (n+1) L h g x ∧
    ‖x 0-xStar‖^2 ≤ R^2 ∧ f (x (n+1)) + h (x (n+1)) - (f xStar + h xStar) = r}

/-- The whole value sets agree. This logical equivalence even allows L=0;
no convergence-rate claim at zero inverse step size is made. -/
theorem oneDimensionalMinimizerValues_eq_analyticValues (n : ℕ) (L : ℝ≥0) (R : ℝ) :
    oneDimensionalMinimizerValues n L R = oneDimensionalAnalyticValues n L R := by
  ext r
  constructor
  · rintro ⟨f, h, g, xStar, x, hf, hh, hmin, hp, hradius, hv⟩
    exact ⟨f, h, g, xStar, x, hf, hh,
      subgradient_of_composite_minimizer hf.toFirstOrder hh hmin, hp, hradius, hv⟩
  · rintro ⟨f, h, g, xStar, x, hf, hh, hs, hp, hradius, hv⟩
    exact ⟨f, h, g, xStar, x, hf, hh,
      composite_minimizer_of_subgradient hf.toFirstOrder hs, hp, hradius, hv⟩

/-- Membership uses the already verified explicit function and ordinary global
minimum directly, not a finite interpolation existence argument. -/
theorem witness_mem_minimizerValues (n : ℕ) {L : ℝ≥0} {R : ℝ}
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) :
    (L : ℝ)*R^2/(4*((n : ℝ)+1)) ∈ oneDimensionalMinimizerValues n L R := by
  exact ⟨ProximalGradientWitnessScaling.smoothFunction L,
    ProximalGradientWitnessScaling.nonsmoothFunction n L R,
    ProximalGradientWitnessScaling.smoothGradient L, 0,
    ProximalGradientWitnessScaling.witnessPoint n R,
    ProximalGradientWitnessScaling.smooth_analytic L,
    ProximalGradientWitnessScaling.nonsmooth_convex n L hR,
    ProximalGradientWitnessScaling.star_isGlobalMin n L hR,
    ProximalGradientWitnessScaling.actual_run n hL hR,
    ProximalGradientWitnessScaling.radius n R,
    ProximalGradientWitnessScaling.attains n L hR⟩

/-- Exact worst-case value stated using ordinary global minimizers. -/
theorem minimizer_tight_all (n : ℕ) {L : ℝ≥0} {R : ℝ}
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) :
    IsGreatest (oneDimensionalMinimizerValues n L R) ((L : ℝ)*R^2/(4*((n : ℝ)+1))) := by
  rw [oneDimensionalMinimizerValues_eq_analyticValues]
  exact ProximalGradientWitnessScaling.analytic_tight_all n hL hR

/-- Universal Hilbert upper plus one-dimensional exact attainment, without
assuming separate stationarity or a cross-universe supremum object. -/
theorem analytic_upper_and_oneDimensional_minimizer_tight [CompleteSpace E]
    (n : ℕ) {L : ℝ≥0} {R : ℝ} (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) :
    (∀ {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E},
      IsSmoothConvexAnalytic L f g → ConvexOn ℝ Set.univ h →
      (∀ y, f xStar + h xStar ≤ f y + h y) → IsSmoothProxRun (n+1) L h g x →
      ‖x 0-xStar‖^2 ≤ R^2 →
      f (x (n+1)) + h (x (n+1)) - (f xStar + h xStar) ≤
        (L : ℝ)*R^2/(4*((n : ℝ)+1))) ∧
    IsGreatest (oneDimensionalMinimizerValues n L R) ((L : ℝ)*R^2/(4*((n : ℝ)+1))) :=
  ⟨fun hf hh hmin hp hr => upper_analytic_of_minimizer hf hh hL hR hmin hp hr,
    minimizer_tight_all n hL hR⟩

end LeanPEP.ActualFunction.ProximalGradientScaling
