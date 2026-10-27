import LeanPEP.ActualFunction.ProximalHilbertExistence
import LeanPEP.ActualFunction.ProximalGradientCanonical

/-!
# The existing canonical proximal-gradient iteration on a Hilbert space

C7 discharges C6's `HasProx` premise on a complete real inner product space
when h is continuous and convex. It reuses `proxMap` and `iterate` verbatim.
Continuity is explicit; no finite-dimensionality assumption is smuggled into
the Hilbert interface. The old finite-dimensional interface remains available
without an explicit continuity premise.

All rates use the original C6/C5/C4 certificate chain. The one-dimensional
continuous-function value set equals C6's value set, since whole-space convex
functions on the real line are continuous. No new numerical rate, new solver,
or extended-real function semantics is introduced.
-/

noncomputable section
open scoped NNReal
namespace LeanPEP.ActualFunction

namespace ProximalScaling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Compact-free existence supplies the old total-solvability proposition. -/
theorem hasProx_of_continuous [CompleteSpace E] {L : ℝ≥0} {h : E → ℝ}
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) (hcont : Continuous h) :
    HasProx L h := fun v => exists_isProxPoint_hilbert hL hh hcont v

end ProximalScaling

namespace ProximalGradientCanonical
open ProximalScaling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The very same C6 recursive definition with its solvability proof supplied
by the compact-free existence theorem. This is still a noncomputable map. -/
def hilbertIterate [CompleteSpace E] (L : ℝ≥0) (h : E → ℝ)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) (hcont : Continuous h)
    (g : E → E) (x0 : E) : ℕ → E :=
  iterate (hasProx_of_continuous hL hh hcont) g x0

@[simp] theorem hilbertIterate_zero [CompleteSpace E] (L : ℝ≥0) (h : E → ℝ)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) (hcont : Continuous h)
    (g : E → E) (x0 : E) : hilbertIterate L h hL hh hcont g x0 0 = x0 := rfl

theorem hilbertIterate_succ [CompleteSpace E] (L : ℝ≥0) (h : E → ℝ)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) (hcont : Continuous h)
    (g : E → E) (x0 : E) (k : ℕ) :
    hilbertIterate L h hL hh hcont g x0 (k+1) =
      proxMap (hasProx_of_continuous hL hh hcont)
        (hilbertIterate L h hL hh hcont g x0 k -
          (L : ℝ)⁻¹ • g (hilbertIterate L h hL hh hcont g x0 k)) := rfl

theorem hilbertIterate_isSmoothProxRun [CompleteSpace E] (L : ℝ≥0) (h : E → ℝ)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) (hcont : Continuous h)
    (g : E → E) (x0 : E) (N : ℕ) :
    ProximalGradientScaling.IsSmoothProxRun N L h g (hilbertIterate L h hL hh hcont g x0) :=
  iterate_isSmoothProxRun (hasProx_of_continuous hL hh hcont) g x0 N

/-- One infinite sequence, not a separate choice for each horizon. -/
theorem exists_all_horizons_hilbert [CompleteSpace E] {L : ℝ≥0} {h : E → ℝ}
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) (hcont : Continuous h)
    (g : E → E) (x0 : E) :
    ∃ x : ℕ → E, x 0 = x0 ∧ ∀ N, ProximalGradientScaling.IsSmoothProxRun N L h g x :=
  exists_all_horizons (hasProx_of_continuous hL hh hcont) g x0

/-- Every supplied physical run agrees with the selected Hilbert iterate on
its actual prefix. No smoothness assumption on g is used for this equality. -/
theorem run_eq_hilbertIterate [CompleteSpace E] {L : ℝ≥0} {h : E → ℝ}
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) (hcont : Continuous h)
    {g : E → E} {x0 : E} {N : ℕ} {x : ℕ → E}
    (hrun : ProximalGradientScaling.IsSmoothProxRun N L h g x) (hx0 : x 0 = x0)
    (k : ℕ) (hk : k ≤ N) : x k = hilbertIterate L h hL hh hcont g x0 k :=
  run_eq_iterate (hasProx_of_continuous hL hh hcont) hL hh hrun hx0 k hk

/-- The finite-dimensional and Hilbert constructions give the same sequence;
this equality uses the old run uniqueness theorem, not a new prox semantics. -/
theorem hilbertIterate_eq_finiteDimensional [FiniteDimensional ℝ E]
    (L : ℝ≥0) (h : E → ℝ) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hcont : Continuous h) (g : E → E) (x0 : E) :
    hilbertIterate L h hL hh hcont g x0 = finiteDimensionalIterate L h hL hh g x0 := by
  funext k
  exact run_eq_iterate (hasProx_of_finiteDimensional hL hh) hL hh
    (hilbertIterate_isSmoothProxRun L h hL hh hcont g x0 k) rfl k (le_refl _)

/-- Generic certificate boundary retains all three old guards. -/
theorem certificate_upper_hilbert [CompleteSpace E] {n : ℕ}
    (c : GramPEP.UpperCertQ (Profiles.ProximalGradient.modelQ n))
    (hc : GramPEP.checkUpperCertQ c = true) (hempty : c.interpTerms = [])
    (hobj : c.objective = Profiles.ProximalGradient.objectiveQ n)
    {L : ℝ≥0} {R : ℝ} {f h : E → ℝ} {g : E → E} {xStar x0 : E}
    (hf : IsSmoothConvexFirstOrder L f g) (hh : ConvexOn ℝ Set.univ h)
    (hcont : Continuous h) (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) (hradius : ‖x0-xStar‖^2 ≤ R^2) :
    f (hilbertIterate L h hL hh hcont g x0 (n+1)) +
      h (hilbertIterate L h hL hh hcont g x0 (n+1)) - (f xStar+h xStar) ≤
        (L : ℝ)*R^2*(c.bound : ℝ) :=
  certificate_upper c hc hempty hobj (hasProx_of_continuous hL hh hcont)
    hf hh hL hR hmin hradius

theorem upper_firstOrder_hilbert [CompleteSpace E] {n : ℕ} {L : ℝ≥0} {R : ℝ}
    {f h : E → ℝ} {g : E → E} {xStar x0 : E}
    (hf : IsSmoothConvexFirstOrder L f g) (hh : ConvexOn ℝ Set.univ h)
    (hcont : Continuous h) (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) (hradius : ‖x0-xStar‖^2 ≤ R^2) :
    f (hilbertIterate L h hL hh hcont g x0 (n+1)) +
      h (hilbertIterate L h hL hh hcont g x0 (n+1)) - (f xStar+h xStar) ≤
        (L : ℝ)*R^2/(4*((n : ℝ)+1)) :=
  upper_firstOrder (hasProx_of_continuous hL hh hcont) hf hh hL hR hmin hradius

/-- No supplied HasProx proof, run, supporting vector or Gram data. Continuity
of h replaces finite-dimensionality in the automatic existence layer. -/
theorem upper_analytic_steps_hilbert [CompleteSpace E] (T : ℕ) (hT : 0 < T)
    {L : ℝ≥0} {R : ℝ} {f h : E → ℝ} {g : E → E} {xStar x0 : E}
    (hf : IsSmoothConvexAnalytic L f g) (hh : ConvexOn ℝ Set.univ h)
    (hcont : Continuous h) (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) (hradius : ‖x0-xStar‖^2 ≤ R^2) :
    f (hilbertIterate L h hL hh hcont g x0 T) +
      h (hilbertIterate L h hL hh hcont g x0 T) - (f xStar+h xStar) ≤
        (L : ℝ)*R^2/(4*(T : ℝ)) :=
  upper_analytic_steps T hT (hasProx_of_continuous hL hh hcont)
    hf hh hL hR hmin hradius

theorem upper_analytic_exact_radius_hilbert [CompleteSpace E] (T : ℕ) (hT : 0 < T)
    {L : ℝ≥0} {f h : E → ℝ} {g : E → E} {xStar x0 : E}
    (hf : IsSmoothConvexAnalytic L f g) (hh : ConvexOn ℝ Set.univ h)
    (hcont : Continuous h) (hL : 0 < (L : ℝ))
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) :
    f (hilbertIterate L h hL hh hcont g x0 T) +
      h (hilbertIterate L h hL hh hcont g x0 T) - (f xStar+h xStar) ≤
        (L : ℝ)*‖x0-xStar‖^2/(4*(T : ℝ)) :=
  upper_analytic_steps_hilbert T hT hf hh hcont hL (norm_nonneg _) hmin (le_refl _)

theorem hilbertIterate_at_minimizer [CompleteSpace E] {L : ℝ≥0}
    {f h : E → ℝ} {g : E → E} {xStar : E}
    (hf : IsSmoothConvexFirstOrder L f g) (hh : ConvexOn ℝ Set.univ h)
    (hcont : Continuous h) (hL : 0 < (L : ℝ))
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) (k : ℕ) :
    hilbertIterate L h hL hh hcont g xStar k = xStar :=
  iterate_at_minimizer (hasProx_of_continuous hL hh hcont) hf hh hL hmin k

/-- Continuity of the existing witness; its function and trajectory are not
changed to fit the new interface. -/
theorem witness_nonsmooth_continuous (n : ℕ) (L : ℝ≥0) (R : ℝ) :
    Continuous (ProximalGradientWitnessScaling.nonsmoothFunction n L R) := by
  unfold ProximalGradientWitnessScaling.nonsmoothFunction
  fun_prop

theorem hilbertIterate_witness (n : ℕ) {L : ℝ≥0} {R : ℝ}
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) (k : ℕ) (hk : k ≤ n+1) :
    hilbertIterate L (ProximalGradientWitnessScaling.nonsmoothFunction n L R)
      hL (ProximalGradientWitnessScaling.nonsmooth_convex n L hR)
      (witness_nonsmooth_continuous n L R)
      (ProximalGradientWitnessScaling.smoothGradient L) R k =
        ProximalGradientWitnessScaling.witnessPoint n R k := by
  rw [hilbertIterate_eq_finiteDimensional]
  exact iterate_witness n hL hR k hk

/-- Actual one-dimensional values with continuity and positive L stated
explicitly and with no existential HasProx proof or freely supplied sequence. -/
def oneDimensionalHilbertValues (n : ℕ) (L : ℝ≥0) (R : ℝ) : Set ℝ :=
  {r | ∃ (f h g : ℝ → ℝ) (xStar x0 : ℝ) (hL : 0 < (L : ℝ))
    (hh : ConvexOn ℝ Set.univ h) (hcont : Continuous h),
    IsSmoothConvexAnalytic L f g ∧ (∀ y, f xStar+h xStar ≤ f y+h y) ∧
    ‖x0-xStar‖^2 ≤ R^2 ∧
    f (hilbertIterate L h hL hh hcont g x0 (n+1)) +
      h (hilbertIterate L h hL hh hcont g x0 (n+1)) - (f xStar+h xStar) = r}

/-- Equality of full value sets. In one dimension continuity follows from
whole-space convexity; it is not silently dropped in arbitrary Hilbert spaces. -/
theorem oneDimensionalHilbertValues_eq_canonicalValues (n : ℕ) {L : ℝ≥0}
    (hL : 0 < (L : ℝ)) (R : ℝ) : oneDimensionalHilbertValues n L R = oneDimensionalValues n L R := by
  ext r
  constructor
  · rintro ⟨f, h, g, xStar, x0, hLp, hh, hcont, hf, hmin, hr, hv⟩
    exact ⟨f, h, g, xStar, x0, hasProx_of_continuous hLp hh hcont, hf, hh, hmin, hr, hv⟩
  · rintro ⟨f, h, g, xStar, x0, hp, hf, hh, hmin, hr, hv⟩
    have hcont : Continuous h := continuousOn_univ.mp (hh.continuousOn isOpen_univ)
    have heq := run_eq_iterate hp hL hh
      (hilbertIterate_isSmoothProxRun L h hL hh hcont g x0 (n+1)) rfl (n+1) (le_refl _)
    refine ⟨f, h, g, xStar, x0, hL, hh, hcont, hf, hmin, hr, ?_⟩
    rw [heq]
    exact hv

theorem hilbert_bound_mem (n : ℕ) {L : ℝ≥0} {R : ℝ}
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) :
    (L : ℝ)*R^2/(4*((n : ℝ)+1)) ∈ oneDimensionalHilbertValues n L R := by
  rw [oneDimensionalHilbertValues_eq_canonicalValues n hL R]
  exact bound_mem n hL hR

theorem hilbert_tight_all (n : ℕ) {L : ℝ≥0} {R : ℝ}
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) :
    IsGreatest (oneDimensionalHilbertValues n L R) ((L : ℝ)*R^2/(4*((n : ℝ)+1))) := by
  rw [oneDimensionalHilbertValues_eq_canonicalValues n hL R]
  exact tight_all n hL hR

end ProximalGradientCanonical
end LeanPEP.ActualFunction
