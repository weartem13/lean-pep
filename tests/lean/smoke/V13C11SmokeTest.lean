import LeanPEP

open LeanPEP LeanPEP.ActualFunction
open ProximalScaling ProximalGradientCanonical Filter
open scoped NNReal Topology BigOperators

#check SummablePerturbation.errorTail
#check SummablePerturbation.partial_sum_le_total
#check SummablePerturbation.errorTail_nonneg
#check SummablePerturbation.errorTail_succ
#check SummablePerturbation.errorTail_tendsto_zero
#check SummablePerturbation.corrected_antitone
#check SummablePerturbation.exists_limit_of_summable_error
#check SummablePerturbation.le_initial_add_total
#check SummablePerturbation.distance_step
#check SummablePerturbation.distance_has_limit
#check SummablePerturbation.distance_le_budget
#check SummablePerturbation.residual_energy_bound
#check SummablePerturbation.residual_tendsto_zero
#check SummablePerturbation.step_norm_tendsto_zero
#check WeakQuasiFejerConvergence.inner_limits_eq_of_distance_limits
#check WeakQuasiFejerConvergence.clusters_eq_of_distance_limits
#check WeakQuasiFejerConvergence.exists_weak_tendsto_fixed_of_distance_limits
#check WeakQuasiFejerConvergence.inexact_weak_tendsto
#check WeakQuasiFejerConvergence.exists_strong_tendsto_fixed_of_compact
#check WeakQuasiFejerConvergence.inexact_strong_tendsto_finiteDimensional
#check ProximalGradientCanonical.forwardBackwardStep_fixed_energy
#check ProximalGradientCanonical.inexact_distance_has_limit
#check ProximalGradientCanonical.inexact_norm_sub_le_budget
#check ProximalGradientCanonical.inexact_residual_tendsto_zero
#check ProximalGradientCanonical.inexact_step_norm_tendsto_zero
#check ProximalGradientCanonical.inexact_weak_tendsto
#check ProximalGradientCanonical.inexact_weak_tendsto_hilbert
#check ProximalGradientCanonical.inexact_tendsto_finiteDimensional
#check ProximalGradientCanonical.inexact_tendsto_finiteDimensional_analytic
#check ProximalGradientCanonical.inexact_weak_tendsto_of_unique
#check ProximalGradientCanonical.oracle_prox_error_bound
#check ProximalGradientCanonical.inexact_oracle_prox_weak_tendsto
#check ProximalGradientCanonical.inexact_oracle_prox_weak_tendsto_hilbert
#check ProximalGradientCanonical.inexact_gradient_weak_tendsto

example {eps : ℕ → ℝ} (hs : Summable eps) :
    Tendsto (SummablePerturbation.errorTail eps) atTop (𝓝 0) :=
  SummablePerturbation.errorTail_tendsto_zero hs

example {a eps : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (he : ∀ n, 0 ≤ eps n)
    (hs : Summable eps) (hstep : ∀ n, a (n+1) ≤ a n+eps n) :
    ∃ d : ℝ, Tendsto a atTop (𝓝 d) :=
  SummablePerturbation.exists_limit_of_summable_error ha he hs hstep

section General
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- Neither completeness nor continuity is needed for this scalar norm limit.
example {L : ℝ≥0} {f h : E → ℝ} {g : E → E} {p : E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hm : ∀ y, f p+h p ≤ f y+h y)
    (u : ℕ → E) (eps : ℕ → ℝ) (hs : Summable eps)
    (he : ∀ n, ‖u (n+1)-forwardBackwardStep hp g (u n)‖ ≤ eps n) :
    Tendsto (fun n => ‖forwardBackwardStep hp g (u n)-u n‖) atTop (𝓝 0) :=
  inexact_residual_tendsto_zero hp hf hL hh hm u eps hs he

-- Errors in gradient and prox output are distinguished, including 1/L.
example {L : ℝ≥0} {h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h)
    (x e y : E) (delta : ℝ)
    (he : ‖y-proxMap hp (x-(L : ℝ)⁻¹ • (g x+e))‖ ≤ delta) :
    ‖y-forwardBackwardStep hp g x‖ ≤ delta+(L : ℝ)⁻¹*‖e‖ :=
  oracle_prox_error_bound hp hL hh x e y he
end General

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- No finite dimension, separability, norm compactness, or weak continuity of T.
example {T : E → E} {u : ℕ → E} {eps : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c) (hT : ∀ x y, ‖T x-T y‖ ≤ ‖x-y‖)
    (henergy : ∀ p, T p=p → ∀ x, ‖T x-p‖^2+c*‖T x-x‖^2 ≤ ‖x-p‖^2)
    (p : E) (hp : T p=p) (hs : Summable eps)
    (he : ∀ n, ‖u (n+1)-T (u n)‖ ≤ eps n) :
    ∃ z, T z=z ∧ Tendsto (fun n => toWeakSpace ℝ E (u n)) atTop (𝓝 (toWeakSpace ℝ E z)) :=
  WeakQuasiFejerConvergence.inexact_weak_tendsto hc hT henergy p hp hs he

example {L : ℝ≥0} {f h : E → ℝ} {g : E → E} {p : E}
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hc : Continuous h) (hm : ∀ y, f p+h p ≤ f y+h y)
    (u : ℕ → E) (eps : ℕ → ℝ) (hs : Summable eps)
    (he : ∀ n, ‖u (n+1)-forwardBackwardStep (hasProx_of_continuous hL hh hc) g (u n)‖ ≤ eps n) :
    ∃ z, (∀ y, f z+h z ≤ f y+h y) ∧
      Tendsto (fun n => toWeakSpace ℝ E (u n)) atTop (𝓝 (toWeakSpace ℝ E z)) :=
  inexact_weak_tendsto_hilbert hf hL hh hc hm u eps hs he

-- The same exact canonical recursion is recovered with zero error.
example {L : ℝ≥0} {f h : E → ℝ} {g : E → E} {p : E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hm : ∀ y, f p+h p ≤ f y+h y) (x0 : E) :
    ∃ z, (∀ y, f z+h z ≤ f y+h y) ∧
      Tendsto (fun n => toWeakSpace ℝ E (iterate hp g x0 n)) atTop (𝓝 (toWeakSpace ℝ E z)) := by
  apply inexact_weak_tendsto hp hf hL hh hm (iterate hp g x0) (fun _ => 0) (by simp)
  intro n
  rw [iterate_succ_eq_step]
  simp only [sub_self, norm_zero, le_refl]

example {L : ℝ≥0} {f h : E → ℝ} {g : E → E} {p : E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hm : ∀ y, f p+h p ≤ f y+h y)
    (u e : ℕ → E) (delta : ℕ → ℝ) (he : Summable (fun n => ‖e n‖)) (hd : Summable delta)
    (hprox : ∀ n, ‖u (n+1)-proxMap hp (u n-(L : ℝ)⁻¹ • (g (u n)+e n))‖ ≤ delta n) :
    ∃ z, (∀ y, f z+h z ≤ f y+h y) ∧
      Tendsto (fun n => toWeakSpace ℝ E (u n)) atTop (𝓝 (toWeakSpace ℝ E z)) :=
  inexact_oracle_prox_weak_tendsto hp hf hL hh hm u e delta he hd hprox

example {L : ℝ≥0} {f h : E → ℝ} {g : E → E} {p : E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hm : ∀ y, f p+h p ≤ f y+h y)
    (u e : ℕ → E) (he : Summable (fun n => ‖e n‖))
    (hstep : ∀ n, u (n+1)=proxMap hp (u n-(L : ℝ)⁻¹ • (g (u n)+e n))) :
    ∃ z, (∀ y, f z+h z ≤ f y+h y) ∧
      Tendsto (fun n => toWeakSpace ℝ E (u n)) atTop (𝓝 (toWeakSpace ℝ E z)) :=
  inexact_gradient_weak_tendsto hp hf hL hh hm u e he hstep
end Hilbert

section FiniteDimensional
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- Continuity of h and HasProx are not exposed in the finite-dimensional wrapper.
example {L : ℝ≥0} {f h : E → ℝ} {g : E → E} {p : E}
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hm : ∀ y, f p+h p ≤ f y+h y)
    (u : ℕ → E) (eps : ℕ → ℝ) (hs : Summable eps)
    (he : ∀ n, ‖u (n+1)-forwardBackwardStep (hasProx_of_finiteDimensional hL hh) g (u n)‖ ≤ eps n) :
    ∃ z, (∀ y, f z+h z ≤ f y+h y) ∧ Tendsto u atTop (𝓝 z) :=
  inexact_tendsto_finiteDimensional_analytic hf hL hh hm u eps hs he
end FiniteDimensional

-- These are still EXACT-run PEP values, not inexact objective bounds.
example : IsGreatest (oneDimensionalHilbertValues 7 3 2) (3/8 : ℝ) := by
  have ht := hilbert_tight_all 7 (L := 3) (R := 2) (by norm_num) (by norm_num)
  norm_num at ht ⊢
  exact ht

example (n : ℕ) {L : ℝ≥0} (hL : 0 < (L : ℝ)) :
    IsGreatest (oneDimensionalHilbertValues n L 0) 0 := by
  simpa using hilbert_tight_all n hL (le_refl (0 : ℝ))

#print axioms SummablePerturbation.exists_limit_of_summable_error
#print axioms SummablePerturbation.residual_tendsto_zero
#print axioms WeakQuasiFejerConvergence.inner_limits_eq_of_distance_limits
#print axioms WeakQuasiFejerConvergence.inexact_weak_tendsto
#print axioms WeakQuasiFejerConvergence.inexact_strong_tendsto_finiteDimensional
#print axioms ProximalGradientCanonical.inexact_weak_tendsto_hilbert
#print axioms ProximalGradientCanonical.inexact_tendsto_finiteDimensional_analytic
#print axioms ProximalGradientCanonical.inexact_oracle_prox_weak_tendsto_hilbert
