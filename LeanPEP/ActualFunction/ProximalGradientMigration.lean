import LeanPEP.ActualFunction.ProximalGradient
import LeanPEP.Profiles.ProximalGradientMigration
import LeanPEP.ActualFunction.ProximalGradientOneStepWitness

/-! # One-step compatibility of the general actual-run interface

This file exercises the NEW all-horizon actual-data bridge with the OLD
accepted C1 certificate. It also proves equality of the one-step actual
value sets, so the new run interface neither weakens nor strengthens the
already verified normalized one-step problem.
-/

noncomputable section
namespace LeanPEP.ActualFunction.ProximalGradient

open Proximal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem isProxRun_one_iff (h : E → ℝ) (g : E → E) (x : ℕ → E) :
    IsProxRun 1 h g x ↔ IsUnitProxPoint h (x 0 - g (x 0)) (x 1) := by
  constructor
  · intro hr
    exact hr 0 (by omega)
  · intro hp k hk
    have heq : k = 0 := by omega
    subst k
    exact hp

/-- Uses the migrated exact certificate via the new arbitrary-horizon bridge,
not a direct invocation of the old one-step actual upper theorem. -/
theorem oneStep_upper_analytic [CompleteSpace E]
    {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsOneSmoothConvexAnalytic f g) (hh : ConvexOn ℝ Set.univ h)
    (hs : SubgradientAt h (-g xStar) xStar) (hrun : IsProxRun 1 h g x)
    (hradius : ‖x 0 - xStar‖ ^ 2 ≤ 1) :
    (f (x 1) + h (x 1)) - (f xStar + h xStar) ≤ (1 : ℝ) / 4 := by
  rcases LeanPEP.Profiles.ProximalGradient.oneStep_exact_certificate with
    ⟨c, hb, ho, he, hc⟩
  have hbound := certificate_upper_analytic c hc he ho hf hh hs hrun hradius
  calc
    (f (x 1) + h (x 1)) - (f xStar + h xStar) ≤ (c.bound : ℝ) := hbound
    _ = (1 : ℝ) / 4 := by norm_num [hb]

/-- Actual functions and actual runs; no finite feasibility appears here. -/
def oneDimensionalAnalyticValues (n : ℕ) : Set ℝ :=
  {r | ∃ (f h g : ℝ → ℝ) (xStar : ℝ) (x : ℕ → ℝ),
    IsOneSmoothConvexAnalytic f g ∧ ConvexOn ℝ Set.univ h ∧
      SubgradientAt h (-g xStar) xStar ∧ IsProxRun (n + 1) h g x ∧
      ‖x 0 - xStar‖ ^ 2 ≤ 1 ∧
      (f (x (n + 1)) + h (x (n + 1))) - (f xStar + h xStar) = r}

/-- Exact equality of new run-based and old point-based actual problems. -/
theorem oneDimensionalAnalyticValues_zero :
    oneDimensionalAnalyticValues 0 =
      ProximalGradientOneStepWitness.oneDimensionalAnalyticValues := by
  ext r
  constructor
  · rintro ⟨f, h, g, xStar, x, hf, hh, hs, hp, hR, hv⟩
    exact ⟨f, h, g, xStar, x 0, x 1, hf, hh, hs,
      (isProxRun_one_iff h g x).mp hp, hR, hv⟩
  · rintro ⟨f, h, g, xStar, x0, x1, hf, hh, hs, hp, hR, hv⟩
    let x : ℕ → ℝ := fun k => if k = 0 then x0 else x1
    refine ⟨f, h, g, xStar, x, hf, hh, hs, ?_, ?_, ?_⟩
    · apply (isProxRun_one_iff h g x).mpr
      simpa [x] using hp
    · simpa [x] using hR
    · simpa [x] using hv

/-- Transport only at ONE step; this is not an all-horizon rate theorem. -/
theorem oneStep_analytic_tight :
    IsGreatest (oneDimensionalAnalyticValues 0) ((1 : ℝ) / 4) := by
  rw [oneDimensionalAnalyticValues_zero]
  exact ProximalGradientOneStepWitness.oneDimensional_analytic_tight

end LeanPEP.ActualFunction.ProximalGradient
