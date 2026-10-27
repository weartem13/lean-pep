import LeanPEP.ActualFunction.ProximalGradientHilbert

/-!
# Objective convergence from the unchanged exact finite-time rate

The C3B certificate and C4--C7 actual-function bridges already bound the
nonnegative objective gap at every positive iteration. This file passes to
the limit, including time zero by a tail argument. No compactness, finite
dimension, point convergence, new rate, or new certificate is used.
-/

noncomputable section
open Filter
open scoped NNReal Topology
namespace LeanPEP.ActualFunction

namespace ObjectiveConvergence

/-- An arbitrary time-zero value is allowed; only positive times are bounded.
This scalar lemma knows nothing about proximal-gradient or a certificate. -/
theorem gap_tendsto_zero_of_succ_bound {a : ℕ → ℝ} {C : ℝ}
    (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, a (k+1) ≤ C/((k : ℝ)+1)) :
    Tendsto a atTop (𝓝 0) := by
  have hmajor : Tendsto (fun k : ℕ => C/((k : ℝ)+1)) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => C) atTop (𝓝 C) := tendsto_const_nhds
    simpa only [mul_zero, mul_one_div] using
      hc.mul tendsto_one_div_add_atTop_nhds_zero_nat
  have hsucc : Tendsto (fun k => a (k+1)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmajor
      (fun k => ha (k+1)) hb
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hsucc ε hε
  refine ⟨N+1, ?_⟩
  intro k hk
  cases k with
  | zero => omega
  | succ k => exact hN k (by omega)

end ObjectiveConvergence

namespace ProximalGradientCanonical
open ProximalScaling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- One coherent supplied run on every finite horizon. This interface needs
neither finite dimension nor a global HasProx proof away from the orbit. -/
theorem run_objective_gap_tendsto_zero {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hf : IsSmoothConvexFirstOrder L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) (x : ℕ → E)
    (hrun : ∀ N, ProximalGradientScaling.IsSmoothProxRun N L h g x) :
    Tendsto (fun k => f (x k)+h (x k)-(f xStar+h xStar)) atTop (𝓝 0) := by
  apply ObjectiveConvergence.gap_tendsto_zero_of_succ_bound
    (C := (L : ℝ)*‖x 0-xStar‖^2/4)
  · intro k
    exact sub_nonneg.mpr (hmin _)
  · intro k
    have hb := ProximalGradientScaling.upper_firstOrder_of_minimizer
      hf hh hL (norm_nonneg _) hmin (hrun (k+1)) (le_refl (‖x 0-xStar‖^2))
    simpa only [div_div] using hb

/-- No point convergence or objective continuity is needed to pass from the
exact rate to convergence of the values. -/
theorem run_objective_tendsto {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hf : IsSmoothConvexFirstOrder L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) (x : ℕ → E)
    (hrun : ∀ N, ProximalGradientScaling.IsSmoothProxRun N L h g x) :
    Tendsto (fun k => f (x k)+h (x k)) atTop (𝓝 (f xStar+h xStar)) := by
  have ht : Tendsto (fun k =>
      (f (x k)+h (x k)-(f xStar+h xStar))+(f xStar+h xStar))
      atTop (𝓝 (0+(f xStar+h xStar))) :=
    (run_objective_gap_tendsto_zero hf hL hh hmin x hrun).add tendsto_const_nhds
  simpa only [sub_add_cancel, zero_add] using ht

/-- The full, unshifted objective gap of the original selected iteration. -/
theorem iterate_objective_gap_tendsto_zero {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E) :
    Tendsto (fun k => f (iterate hp g x0 k)+h (iterate hp g x0 k)-(f xStar+h xStar))
      atTop (𝓝 0) :=
  run_objective_gap_tendsto_zero hf hL hh hmin (iterate hp g x0)
    (iterate_isSmoothProxRun hp g x0)

theorem iterate_objective_tendsto {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E) :
    Tendsto (fun k => f (iterate hp g x0 k)+h (iterate hp g x0 k))
      atTop (𝓝 (f xStar+h xStar)) :=
  run_objective_tendsto hf hL hh hmin (iterate hp g x0) (iterate_isSmoothProxRun hp g x0)

/-- C7 supplies existence in a complete Hilbert space. Continuity of h remains
explicit; compactness and finite-dimensionality are absent. -/
theorem hilbertIterate_objective_gap_tendsto_zero [CompleteSpace E]
    {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hcont : Continuous h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E) :
    Tendsto (fun k => f (hilbertIterate L h hL hh hcont g x0 k)+
      h (hilbertIterate L h hL hh hcont g x0 k)-(f xStar+h xStar)) atTop (𝓝 0) :=
  iterate_objective_gap_tendsto_zero (hasProx_of_continuous hL hh hcont)
    hf.toFirstOrder hL hh hmin x0

theorem hilbertIterate_objective_tendsto [CompleteSpace E]
    {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hcont : Continuous h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E) :
    Tendsto (fun k => f (hilbertIterate L h hL hh hcont g x0 k)+
      h (hilbertIterate L h hL hh hcont g x0 k)) atTop (𝓝 (f xStar+h xStar)) :=
  iterate_objective_tendsto (hasProx_of_continuous hL hh hcont)
    hf.toFirstOrder hL hh hmin x0

/-- Finite-dimensional existence avoids a caller-supplied continuity proof. -/
theorem finiteDimensionalIterate_objective_tendsto [FiniteDimensional ℝ E]
    {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) (x0 : E) :
    Tendsto (fun k => f (finiteDimensionalIterate L h hL hh g x0 k)+
      h (finiteDimensionalIterate L h hL hh g x0 k)) atTop (𝓝 (f xStar+h xStar)) :=
  iterate_objective_tendsto (hasProx_of_finiteDimensional hL hh)
    hf.toFirstOrder hL hh hmin x0

end ProximalGradientCanonical
end LeanPEP.ActualFunction
