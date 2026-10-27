import LeanPEP.ActualFunction.WeakQuasiFejerConvergence
import LeanPEP.ActualFunction.ProximalGradientStability

/-!
# Summably inexact proximal-gradient trajectories

The reference step is C8's unchanged forwardBackwardStep, hence uses the
same C6 proxMap and the same physical 1/L gradient step. The supplied sequence
may have summable output errors, or simultaneous summable gradient-norm and
prox-output errors. Weak convergence is in mathlib's standard WeakSpace.
Finite-dimensional strong convergence has a separate compactness proof.
No noisy LR^2/(4T) bound, objective-gap error tolerance, weak continuity of
f+h, or equality with the unperturbed limit is asserted.
-/

noncomputable section
open Filter
open scoped NNReal Topology BigOperators
namespace LeanPEP.ActualFunction.ProximalGradientCanonical
open ProximalScaling HilbertWeakTopology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- C8's two-point estimate anchored at any fixed point, with the same 1/2
residual coefficient. This requires no separate minimizer assumption. -/
theorem forwardBackwardStep_fixed_energy {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) {p : E}
    (hpfix : forwardBackwardStep hp g p = p) (x : E) :
    ‖forwardBackwardStep hp g x-p‖^2 +
      (1/2 : ℝ)*‖forwardBackwardStep hp g x-x‖^2 ≤ ‖x-p‖^2 := by
  have he := forwardBackwardStep_energy hp hf hL hh x p
  rw [hpfix] at he
  have hv : (x-p)-(forwardBackwardStep hp g x-p) = -(forwardBackwardStep hp g x-x) := by
    abel
  rw [hv, norm_neg] at he
  exact he

/-- Distances need not decrease, but converge to finite real limits. -/
theorem inexact_distance_has_limit {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y)
    (u : ℕ → E) (eps : ℕ → ℝ) (hs : Summable eps)
    (herr : ∀ n, ‖u (n+1)-forwardBackwardStep hp g (u n)‖ ≤ eps n) :
    ∃ d : ℝ, Tendsto (fun n => ‖u n-xStar‖) atTop (𝓝 d) :=
  SummablePerturbation.distance_has_limit (forwardBackwardStep_norm_sub_le hp hf hL hh)
    hs herr (forwardBackwardStep_fixed_of_minimizer hp hf hL hh hmin)

theorem inexact_norm_sub_le_budget {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y)
    (u : ℕ → E) (eps : ℕ → ℝ) (hs : Summable eps)
    (herr : ∀ n, ‖u (n+1)-forwardBackwardStep hp g (u n)‖ ≤ eps n) (N : ℕ) :
    ‖u N-xStar‖ ≤ ‖u 0-xStar‖ + ∑' n, eps n :=
  SummablePerturbation.distance_le_budget (forwardBackwardStep_norm_sub_le hp hf hL hh)
    hs herr (forwardBackwardStep_fixed_of_minimizer hp hf hL hh hmin) N

/-- The exact step residual, evaluated on the inexact sequence, tends to zero. -/
theorem inexact_residual_tendsto_zero {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y)
    (u : ℕ → E) (eps : ℕ → ℝ) (hs : Summable eps)
    (herr : ∀ n, ‖u (n+1)-forwardBackwardStep hp g (u n)‖ ≤ eps n) :
    Tendsto (fun n => ‖forwardBackwardStep hp g (u n)-u n‖) atTop (𝓝 0) := by
  have hpfix := forwardBackwardStep_fixed_of_minimizer hp hf hL hh hmin
  exact SummablePerturbation.residual_tendsto_zero (by norm_num : (0 : ℝ) < 1/2)
    (forwardBackwardStep_norm_sub_le hp hf hL hh) hpfix
    (forwardBackwardStep_fixed_energy hp hf hL hh hpfix) hs herr

theorem inexact_step_norm_tendsto_zero {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y)
    (u : ℕ → E) (eps : ℕ → ℝ) (hs : Summable eps)
    (herr : ∀ n, ‖u (n+1)-forwardBackwardStep hp g (u n)‖ ≤ eps n) :
    Tendsto (fun n => ‖u (n+1)-u n‖) atTop (𝓝 0) :=
  SummablePerturbation.step_norm_tendsto_zero hs herr
    (inexact_residual_tendsto_zero hp hf hL hh hmin u eps hs herr)

/-- Summable output errors: full weak convergence of the supplied infinite
sequence to some composite minimizer, not necessarily the exact orbit limit. -/
theorem inexact_weak_tendsto [CompleteSpace E]
    {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y)
    (u : ℕ → E) (eps : ℕ → ℝ) (hs : Summable eps)
    (herr : ∀ n, ‖u (n+1)-forwardBackwardStep hp g (u n)‖ ≤ eps n) :
    ∃ z, (∀ y, f z+h z ≤ f y+h y) ∧
      Tendsto (fun n => toWeakSpace ℝ E (u n)) atTop (𝓝 (toWeakSpace ℝ E z)) := by
  obtain ⟨z, hz, ht⟩ := WeakQuasiFejerConvergence.inexact_weak_tendsto
    (by norm_num : (0 : ℝ) < 1/2) (forwardBackwardStep_norm_sub_le hp hf hL hh)
    (fun p hpfix => forwardBackwardStep_fixed_energy hp hf hL hh hpfix) xStar
    (forwardBackwardStep_fixed_of_minimizer hp hf hL hh hmin) hs herr
  exact ⟨z, (forwardBackwardStep_fixed_iff_minimizer hp hf hL hh z).mp hz, ht⟩

/-- Hilbert existence is discharged by C7. All errors concern the same map. -/
theorem inexact_weak_tendsto_hilbert [CompleteSpace E]
    {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hcont : Continuous h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y)
    (u : ℕ → E) (eps : ℕ → ℝ) (hs : Summable eps)
    (herr : ∀ n, ‖u (n+1)-forwardBackwardStep (hasProx_of_continuous hL hh hcont) g (u n)‖ ≤ eps n) :
    ∃ z, (∀ y, f z+h z ≤ f y+h y) ∧
      Tendsto (fun n => toWeakSpace ℝ E (u n)) atTop (𝓝 (toWeakSpace ℝ E z)) :=
  inexact_weak_tendsto (hasProx_of_continuous hL hh hcont) hf.toFirstOrder hL hh
    hmin u eps hs herr

/-- Finite-dimensional strong convergence has its own compact-orbit proof. -/
theorem inexact_tendsto_finiteDimensional [FiniteDimensional ℝ E]
    {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y)
    (u : ℕ → E) (eps : ℕ → ℝ) (hs : Summable eps)
    (herr : ∀ n, ‖u (n+1)-forwardBackwardStep hp g (u n)‖ ≤ eps n) :
    ∃ z, (∀ y, f z+h z ≤ f y+h y) ∧ Tendsto u atTop (𝓝 z) := by
  obtain ⟨z, hz, ht⟩ := WeakQuasiFejerConvergence.inexact_strong_tendsto_finiteDimensional
    (by norm_num : (0 : ℝ) < 1/2) (forwardBackwardStep_norm_sub_le hp hf hL hh)
    (fun p hpfix => forwardBackwardStep_fixed_energy hp hf hL hh hpfix) xStar
    (forwardBackwardStep_fixed_of_minimizer hp hf hL hh hmin) hs herr
  exact ⟨z, (forwardBackwardStep_fixed_iff_minimizer hp hf hL hh z).mp hz, ht⟩

/-- Analysis-facing finite-dimensional result without a HasProx premise. -/
theorem inexact_tendsto_finiteDimensional_analytic [FiniteDimensional ℝ E]
    {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y)
    (u : ℕ → E) (eps : ℕ → ℝ) (hs : Summable eps)
    (herr : ∀ n, ‖u (n+1)-forwardBackwardStep (hasProx_of_finiteDimensional hL hh) g (u n)‖ ≤ eps n) :
    ∃ z, (∀ y, f z+h z ≤ f y+h y) ∧ Tendsto u atTop (𝓝 z) :=
  inexact_tendsto_finiteDimensional (hasProx_of_finiteDimensional hL hh) hf.toFirstOrder
    hL hh hmin u eps hs herr

/-- A separate uniqueness premise identifies the weak limit as the reference. -/
theorem inexact_weak_tendsto_of_unique [CompleteSpace E]
    {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y)
    (hunique : ∀ z, (∀ y, f z+h z ≤ f y+h y) → z = xStar)
    (u : ℕ → E) (eps : ℕ → ℝ) (hs : Summable eps)
    (herr : ∀ n, ‖u (n+1)-forwardBackwardStep hp g (u n)‖ ≤ eps n) :
    Tendsto (fun n => toWeakSpace ℝ E (u n)) atTop (𝓝 (toWeakSpace ℝ E xStar)) := by
  obtain ⟨z, hz, ht⟩ := inexact_weak_tendsto hp hf hL hh hmin u eps hs herr
  rw [hunique z hz] at ht
  exact ht

/-- Prox error is an OUTPUT-NORM error, not a subproblem objective tolerance.
The physical gradient error always carries the factor 1/L. -/
theorem oracle_prox_error_bound {L : ℝ≥0} {h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h)
    (x e y : E) {delta : ℝ}
    (hprox : ‖y-proxMap hp (x-(L : ℝ)⁻¹ • (g x+e))‖ ≤ delta) :
    ‖y-forwardBackwardStep hp g x‖ ≤ delta + (L : ℝ)⁻¹*‖e‖ := by
  have ht := dist_triangle y (proxMap hp (x-(L : ℝ)⁻¹ • (g x+e)))
    (forwardBackwardStep hp g x)
  simp only [dist_eq_norm] at ht
  exact ht.trans (add_le_add hprox (forwardBackwardStep_oracle_error hp hL hh g x e))

/-- Simultaneous summable gradient-norm and prox-output errors. -/
theorem inexact_oracle_prox_weak_tendsto [CompleteSpace E]
    {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y)
    (u e : ℕ → E) (delta : ℕ → ℝ)
    (he : Summable (fun n => ‖e n‖)) (hd : Summable delta)
    (hprox : ∀ n, ‖u (n+1)-proxMap hp (u n-(L : ℝ)⁻¹ • (g (u n)+e n))‖ ≤ delta n) :
    ∃ z, (∀ y, f z+h z ≤ f y+h y) ∧
      Tendsto (fun n => toWeakSpace ℝ E (u n)) atTop (𝓝 (toWeakSpace ℝ E z)) :=
  inexact_weak_tendsto hp hf hL hh hmin u (fun n => delta n+(L : ℝ)⁻¹*‖e n‖)
    (hd.add (he.mul_left (L : ℝ)⁻¹))
    (fun n => oracle_prox_error_bound hp hL hh (u n) (e n) (u (n+1)) (hprox n))

theorem inexact_oracle_prox_weak_tendsto_hilbert [CompleteSpace E]
    {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hcont : Continuous h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y)
    (u e : ℕ → E) (delta : ℕ → ℝ)
    (he : Summable (fun n => ‖e n‖)) (hd : Summable delta)
    (hprox : ∀ n, ‖u (n+1)-proxMap (hasProx_of_continuous hL hh hcont)
      (u n-(L : ℝ)⁻¹ • (g (u n)+e n))‖ ≤ delta n) :
    ∃ z, (∀ y, f z+h z ≤ f y+h y) ∧
      Tendsto (fun n => toWeakSpace ℝ E (u n)) atTop (𝓝 (toWeakSpace ℝ E z)) :=
  inexact_oracle_prox_weak_tendsto (hasProx_of_continuous hL hh hcont)
    hf.toFirstOrder hL hh hmin u e delta he hd hprox

/-- Exact prox solves with summable additive gradient errors are included. -/
theorem inexact_gradient_weak_tendsto [CompleteSpace E]
    {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y)
    (u e : ℕ → E) (he : Summable (fun n => ‖e n‖))
    (hstep : ∀ n, u (n+1) = proxMap hp (u n-(L : ℝ)⁻¹ • (g (u n)+e n))) :
    ∃ z, (∀ y, f z+h z ≤ f y+h y) ∧
      Tendsto (fun n => toWeakSpace ℝ E (u n)) atTop (𝓝 (toWeakSpace ℝ E z)) := by
  apply inexact_weak_tendsto hp hf hL hh hmin u (fun n => (L : ℝ)⁻¹*‖e n‖)
    (he.mul_left (L : ℝ)⁻¹)
  intro n
  rw [hstep n]
  exact forwardBackwardStep_oracle_error hp hL hh g (u n) (e n)

end LeanPEP.ActualFunction.ProximalGradientCanonical
