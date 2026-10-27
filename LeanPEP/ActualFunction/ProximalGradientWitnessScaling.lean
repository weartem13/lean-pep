import LeanPEP.ActualFunction.ProximalGradientScaling

/-!
# Actual all-horizon attainment of LR^2/(4T)

T=n+1. The physical witness is f(x)=L*x, g(x)=L,
h(x)=L*(a*max(x,0)-x), a=R/(2T), and x_k=R*(1-k/(2T)).
The affine tilt is deliberate: g(0)=L is nonzero whenever L>0, including
R=0. Composite stationarity is cancellation, not separate stationarity.
The point sequence is proved to be a physical prox run only for k<T.
No claim of a linear run beyond the finite prefix or prox-existence theorem
is made. Tightness is in the actual-function value set, not inferred from
finite interpolation feasibility.
-/

noncomputable section
open scoped NNReal
namespace LeanPEP.ActualFunction.ProximalGradientWitnessScaling

open Proximal ProximalScaling ProximalGradientScaling

/-- Reuse the old lower-witness slope, now multiplied by the physical radius. -/
def slope (n : ℕ) (R : ℝ) : ℝ := R * ProximalGradientWitness.slope n

def smoothFunction (L : ℝ≥0) (z : ℝ) : ℝ := (L : ℝ)*z
def smoothGradient (L : ℝ≥0) (_ : ℝ) : ℝ := (L : ℝ)
def nonsmoothFunction (n : ℕ) (L : ℝ≥0) (R z : ℝ) : ℝ :=
  (L : ℝ) * (slope n R * max z 0 - z)

def witnessPoint (n : ℕ) (R : ℝ) (k : ℕ) : ℝ := R * ProximalGradientWitness.witnessPoint n k

theorem slope_nonneg (n : ℕ) {R : ℝ} (hR : 0 ≤ R) : 0 ≤ slope n R :=
  mul_nonneg hR (le_of_lt (ProximalGradientWitness.slope_pos n))

/-- Affine f has a constant actual gradient, with Lipschitz constant at most L. -/
theorem smooth_analytic (L : ℝ≥0) :
    IsSmoothConvexAnalytic L (smoothFunction L) (smoothGradient L) := by
  constructor
  · intro z
    change HasGradientAt (fun y : ℝ => (L : ℝ)*y) (L : ℝ) z
    exact (hasDerivAt_const_mul (x := z) (L : ℝ)).hasGradientAt'
  · refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    change (L : ℝ)*(a*x+b*y) ≤ a*((L : ℝ)*x)+b*((L : ℝ)*y)
    nlinarith
  · intro x y
    simp [smoothGradient]

theorem nonsmooth_convex (n : ℕ) (L : ℝ≥0) {R : ℝ} (hR : 0 ≤ R) :
    ConvexOn ℝ Set.univ (nonsmoothFunction n L R) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hleft : a*x+b*y ≤ a*max x 0+b*max y 0 :=
    add_le_add (mul_le_mul_of_nonneg_left (le_max_left x 0) ha)
      (mul_le_mul_of_nonneg_left (le_max_left y 0) hb)
  have hright : 0 ≤ a*max x 0+b*max y 0 :=
    add_nonneg (mul_nonneg ha (le_max_right x 0)) (mul_nonneg hb (le_max_right y 0))
  have hmax := mul_le_mul_of_nonneg_left (max_le hleft hright)
    (mul_nonneg L.property (slope_nonneg n hR))
  simp only [nonsmoothFunction, smul_eq_mul]
  calc
    (L : ℝ) * (slope n R * max (a*x+b*y) 0 - (a*x+b*y)) =
        (L : ℝ)*slope n R*max (a*x+b*y) 0 - (L : ℝ)*(a*x+b*y) := by ring
    _ ≤ (L : ℝ)*slope n R*(a*max x 0+b*max y 0) - (L : ℝ)*(a*x+b*y) :=
      sub_le_sub hmax (le_refl _)
    _ = a*((L : ℝ)*(slope n R*max x 0-x)) +
        b*((L : ℝ)*(slope n R*max y 0-y)) := by ring

@[simp] theorem smoothFunction_zero (L : ℝ≥0) : smoothFunction L 0 = 0 := by
  simp [smoothFunction]

@[simp] theorem nonsmoothFunction_zero (n : ℕ) (L : ℝ≥0) (R : ℝ) :
    nonsmoothFunction n L R 0 = 0 := by simp [nonsmoothFunction]

theorem composite_value (n : ℕ) (L : ℝ≥0) (R z : ℝ) :
    smoothFunction L z + nonsmoothFunction n L R z = (L : ℝ)*slope n R*max z 0 := by
  unfold smoothFunction nonsmoothFunction
  ring

theorem star_subgradient (n : ℕ) (L : ℝ≥0) {R : ℝ} (hR : 0 ≤ R) :
    SubgradientAt (nonsmoothFunction n L R) (-smoothGradient L 0) 0 := by
  intro y
  have hm := mul_nonneg (mul_nonneg L.property (slope_nonneg n hR)) (le_max_right y 0)
  norm_num [nonsmoothFunction, smoothGradient, RCLike.inner_apply]
  calc
    -(y * (L : ℝ)) = 0 - (L : ℝ)*y := by ring
    _ ≤ (L : ℝ)*slope n R*max y 0 - (L : ℝ)*y :=
      sub_le_sub hm (le_refl _)
    _ = (L : ℝ)*(slope n R*max y 0-y) := by ring

theorem subgradient_at_nonneg (n : ℕ) (L : ℝ≥0) {R z : ℝ} (hR : 0 ≤ R) (hz : 0 ≤ z) :
    SubgradientAt (nonsmoothFunction n L R) ((L : ℝ)*(slope n R-1)) z := by
  intro y
  have hm := mul_le_mul_of_nonneg_left (le_max_left y 0)
    (mul_nonneg L.property (slope_nonneg n hR))
  norm_num [nonsmoothFunction, max_eq_left hz, RCLike.inner_apply]
  calc
    (L : ℝ)*(slope n R*z-z) + (y-z)*((L : ℝ)*(slope n R-1)) =
        (L : ℝ)*slope n R*y - (L : ℝ)*y := by ring
    _ ≤ (L : ℝ)*slope n R*max y 0 - (L : ℝ)*y :=
      sub_le_sub hm (le_refl _)
    _ = (L : ℝ)*(slope n R*max y 0-y) := by ring

theorem star_isGlobalMin (n : ℕ) (L : ℝ≥0) {R : ℝ} (hR : 0 ≤ R) (y : ℝ) :
    smoothFunction L 0 + nonsmoothFunction n L R 0 ≤
      smoothFunction L y + nonsmoothFunction n L R y := by
  rw [composite_value, composite_value]
  simp only [max_self, mul_zero]
  exact mul_nonneg (mul_nonneg L.property (slope_nonneg n hR)) (le_max_right y 0)

theorem smooth_gradient_at_star_ne_zero {L : ℝ≥0} (hL : 0 < (L : ℝ)) :
    smoothGradient L 0 ≠ 0 := ne_of_gt hL

@[simp] theorem witnessPoint_zero (n : ℕ) (R : ℝ) : witnessPoint n R 0 = R := by
  simp [witnessPoint]

theorem witnessPoint_succ (n k : ℕ) (R : ℝ) :
    witnessPoint n R (k+1) = witnessPoint n R k - slope n R := by
  rw [witnessPoint, ProximalGradientWitness.witnessPoint_succ]
  change R*(ProximalGradientWitness.witnessPoint n k-ProximalGradientWitness.slope n) = _
  simp only [witnessPoint, slope]
  ring

theorem witnessPoint_final (n : ℕ) (R : ℝ) : witnessPoint n R (n+1) = R/2 := by
  rw [witnessPoint, ProximalGradientWitness.witnessPoint_final]
  ring

theorem witnessPoint_nonneg (n k : ℕ) {R : ℝ} (hR : 0 ≤ R) (hk : k ≤ n+1) :
    0 ≤ witnessPoint n R k :=
  mul_nonneg hR (ProximalGradientWitness.witnessPoint_nonneg n k hk)

/-- Ordinary physical prox steps, established by explicit residual support. -/
theorem actual_run (n : ℕ) {L : ℝ≥0} {R : ℝ} (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) :
    IsSmoothProxRun (n+1) L (nonsmoothFunction n L R) (smoothGradient L) (witnessPoint n R) := by
  intro k hk
  apply isProxPoint_of_subgradient
  have hres : (L : ℝ) • (witnessPoint n R k -
      (L : ℝ)⁻¹ • smoothGradient L (witnessPoint n R k) - witnessPoint n R (k+1)) =
        (L : ℝ)*(slope n R-1) := by
    rw [witnessPoint_succ]
    simp only [smoothGradient, smul_eq_mul, inv_mul_cancel₀ (ne_of_gt hL)]
    ring
  rw [hres]
  exact subgradient_at_nonneg n L hR (witnessPoint_nonneg n (k+1) hR (by omega))

/-- Explicit equality for every positive step count, also at radius zero. -/
theorem attains (n : ℕ) (L : ℝ≥0) {R : ℝ} (hR : 0 ≤ R) :
    (smoothFunction L (witnessPoint n R (n+1)) +
      nonsmoothFunction n L R (witnessPoint n R (n+1))) -
      (smoothFunction L 0 + nonsmoothFunction n L R 0) =
        (L : ℝ)*R^2/(4*((n : ℝ)+1)) := by
  rw [witnessPoint_final, composite_value, composite_value]
  have hhalf : 0 ≤ R/2 := by positivity
  rw [max_eq_left hhalf]
  simp only [max_self, mul_zero, sub_zero, slope, ProximalGradientWitness.slope]
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  field_simp [hn] <;> ring

theorem radius (n : ℕ) (R : ℝ) : ‖witnessPoint n R 0 - (0 : ℝ)‖^2 ≤ R^2 := by
  simpa only [witnessPoint_zero, sub_zero, Real.norm_eq_abs, sq_abs] using (le_refl (R^2))

@[simp] theorem zeroRadius_point (n k : ℕ) : witnessPoint n 0 k = 0 := by
  simp [witnessPoint]

/-- L=R=1 recovers the existing lower witness, including its affine split. -/
theorem unit_witness (n : ℕ) :
    smoothFunction 1 = ProximalGradientWitness.smoothFunction ∧
    smoothGradient 1 = ProximalGradientWitness.smoothGradient ∧
    nonsmoothFunction n 1 1 = ProximalGradientWitness.nonsmoothFunction n ∧
    witnessPoint n 1 = ProximalGradientWitness.witnessPoint n := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext z
  · simp [smoothFunction, ProximalGradientWitness.smoothFunction,
      ProximalGradientOneStepWitness.smoothFunction]
  · simp [smoothGradient, ProximalGradientWitness.smoothGradient,
      ProximalGradientOneStepWitness.smoothGradient]
  · simp [nonsmoothFunction, slope, ProximalGradientWitness.nonsmoothFunction]
  · simp [witnessPoint]

theorem bound_mem (n : ℕ) {L : ℝ≥0} {R : ℝ} (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) :
    (L : ℝ)*R^2/(4*((n : ℝ)+1)) ∈ oneDimensionalAnalyticValues n L R := by
  exact ⟨smoothFunction L, nonsmoothFunction n L R, smoothGradient L, 0, witnessPoint n R,
    smooth_analytic L, nonsmooth_convex n L hR, star_subgradient n L hR,
    actual_run n hL hR, radius n R, attains n L hR⟩

/-- Actual-function maximum, using the unchanged all-horizon upper certificate. -/
theorem analytic_tight_all (n : ℕ) {L : ℝ≥0} {R : ℝ} (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) :
    IsGreatest (oneDimensionalAnalyticValues n L R) ((L : ℝ)*R^2/(4*((n : ℝ)+1))) := by
  constructor
  · exact bound_mem n hL hR
  · intro r hr
    rcases hr with ⟨f, h, g, xStar, x, hf, hh, hs, hp, hradius, hv⟩
    rw [← hv]
    exact upper_analytic hf hh hL hR hs hp hradius

/-- Universal Hilbert upper with one-dimensional attainment; no
universe-polymorphic supremum is introduced. -/
theorem analytic_upper_and_oneDimensional_tight
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (n : ℕ) {L : ℝ≥0} {R : ℝ} (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) :
    (∀ {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E},
      IsSmoothConvexAnalytic L f g → ConvexOn ℝ Set.univ h →
      SubgradientAt h (-g xStar) xStar → IsSmoothProxRun (n+1) L h g x →
      ‖x 0-xStar‖^2 ≤ R^2 →
      f (x (n+1)) + h (x (n+1)) - (f xStar+h xStar) ≤
        (L : ℝ)*R^2/(4*((n : ℝ)+1))) ∧
    IsGreatest (oneDimensionalAnalyticValues n L R) ((L : ℝ)*R^2/(4*((n : ℝ)+1))) := by
  exact ⟨fun hf hh hs hp hr => upper_analytic hf hh hL hR hs hp hr,
    analytic_tight_all n hL hR⟩

end LeanPEP.ActualFunction.ProximalGradientWitnessScaling
