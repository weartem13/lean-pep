import LeanPEP.ActualFunction.ProximalGradientOneStep

/-!
# Actual nonsmooth lower witness for one-step proximal gradient

`f(x) = x`, `g(x) = 1`, `h(x) = max(x,0)/2 - x`.
The composite objective is `max(x,0)/2`. Its minimizer is `x_star = 0`.
Neither component is separately stationary there: `g_star = 1`, `s_star = -1`.
The unit forward point from `x_0 = 1` is zero, and its actual h-prox is `1/2`.
The gap equals `1/4`, matching the compiler-generated Gram certificate.

This is an explicit actual-function proof, not a completeness lift of a finite
primal. It is limited to the normalized one-step problem.
-/

noncomputable section
namespace LeanPEP.ActualFunction.ProximalGradientOneStepWitness

open Proximal

def smoothFunction (x : ℝ) : ℝ := x
def smoothGradient (_ : ℝ) : ℝ := 1
def nonsmoothFunction (x : ℝ) : ℝ := max x 0 / 2 - x

theorem smooth_analytic : IsOneSmoothConvexAnalytic smoothFunction smoothGradient := by
  constructor
  · intro x
    change HasGradientAt (fun z : ℝ => z) (1 : ℝ) x
    exact (hasDerivAt_id x).hasGradientAt'
  · refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    simp [smoothFunction]
  · intro x y
    simp [smoothGradient]

/-- The nonsmooth component is convex although it need not be bounded below. -/
theorem nonsmooth_convex : ConvexOn ℝ Set.univ nonsmoothFunction := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hleft : a * x + b * y ≤ a * max x 0 + b * max y 0 :=
    add_le_add (mul_le_mul_of_nonneg_left (le_max_left x 0) ha)
      (mul_le_mul_of_nonneg_left (le_max_left y 0) hb)
  have hright : 0 ≤ a * max x 0 + b * max y 0 :=
    add_nonneg (mul_nonneg ha (le_max_right x 0))
      (mul_nonneg hb (le_max_right y 0))
  have hmax := max_le hleft hright
  simp only [nonsmoothFunction, smul_eq_mul]
  nlinarith

theorem star_subgradient : SubgradientAt nonsmoothFunction (-1 : ℝ) 0 := by
  intro y
  norm_num [nonsmoothFunction, RCLike.inner_apply] <;>
    linarith [le_max_right y (0 : ℝ)]

theorem final_subgradient : SubgradientAt nonsmoothFunction (-(1/2) : ℝ) (1/2) := by
  intro y
  norm_num [nonsmoothFunction, RCLike.inner_apply] <;>
    linarith [le_max_left y (0 : ℝ)]

/-- This witness deliberately rejects separate-stationarity modelling. -/
theorem smooth_gradient_at_star_ne_zero : smoothGradient 0 ≠ 0 := by
  norm_num [smoothGradient]

theorem star_isGlobalMin (y : ℝ) :
    smoothFunction 0 + nonsmoothFunction 0 ≤
      smoothFunction y + nonsmoothFunction y := by
  norm_num [smoothFunction, nonsmoothFunction] <;>
    linarith [le_max_right y (0 : ℝ)]

/-- The output is an actual minimizer of the proximal subproblem. -/
theorem actual_prox : IsUnitProxPoint nonsmoothFunction (1 - smoothGradient 1) (1/2) := by
  apply isUnitProxPoint_of_subgradient
  simpa [smoothGradient] using final_subgradient

theorem attains :
    (smoothFunction (1/2) + nonsmoothFunction (1/2)) -
      (smoothFunction 0 + nonsmoothFunction 0) = (1 : ℝ) / 4 := by
  norm_num [smoothFunction, nonsmoothFunction]

/-- Actual functions, actual prox minimality, and a composite stationarity
certificate. No finite Gram or checker premise appears in this set. -/
def oneDimensionalAnalyticValues : Set ℝ :=
  {r | ∃ (f h g : ℝ → ℝ) (xStar x0 x1 : ℝ),
    IsOneSmoothConvexAnalytic f g ∧ ConvexOn ℝ Set.univ h ∧
      SubgradientAt h (-g xStar) xStar ∧
      IsUnitProxPoint h (x0 - g x0) x1 ∧
      ‖x0 - xStar‖ ^ 2 ≤ 1 ∧
      (f x1 + h x1) - (f xStar + h xStar) = r}

theorem bound_mem : (1 : ℝ) / 4 ∈ oneDimensionalAnalyticValues := by
  refine ⟨smoothFunction, nonsmoothFunction, smoothGradient, 0, 1, 1/2,
    smooth_analytic, nonsmooth_convex, ?_, actual_prox, ?_, attains⟩
  · simpa [smoothGradient] using star_subgradient
  · norm_num

theorem oneDimensional_analytic_tight :
    IsGreatest oneDimensionalAnalyticValues ((1 : ℝ) / 4) := by
  constructor
  · exact bound_mem
  · intro r hr
    rcases hr with ⟨f, h, g, xStar, x0, x1, hf, hh, hs, hp, hR, hv⟩
    rw [← hv]
    exact ProximalGradientOneStep.upper_analytic hf hh hs hp hR

/-- Arbitrary real Hilbert-space upper bound and a one-dimensional actual
maximum, without introducing a universe-polymorphic supremum object. -/
theorem analytic_upper_and_oneDimensional_tight
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    (∀ {f h : E → ℝ} {g : E → E} {xStar x0 x1 : E},
      IsOneSmoothConvexAnalytic f g → ConvexOn ℝ Set.univ h →
      SubgradientAt h (-g xStar) xStar →
      IsUnitProxPoint h (x0 - g x0) x1 →
      ‖x0 - xStar‖ ^ 2 ≤ 1 →
      (f x1 + h x1) - (f xStar + h xStar) ≤ (1 : ℝ) / 4) ∧
      IsGreatest oneDimensionalAnalyticValues ((1 : ℝ) / 4) := by
  exact ⟨fun hf hh hs hp hR => ProximalGradientOneStep.upper_analytic hf hh hs hp hR,
    oneDimensional_analytic_tight⟩

end LeanPEP.ActualFunction.ProximalGradientOneStepWitness
