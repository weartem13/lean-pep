import LeanPEP.ActualFunction.ProximalGradientMigration
import LeanPEP.Profiles.ProximalGradientCertificate

/-!
# An explicit actual lower witness at every positive proximal-gradient horizon

T = n+1, a = 1/(2T). Reuse C1's f(x)=x, g(x)=1, and take
h(x)=a*max(x,0)-x. The composite objective is a*max(x,0).
The finite trajectory x_k=1-k*a, 0<=k<=T, consists of actual unit prox
steps, with residual a-1 at each new point and star subgradient -1.
It ends at x_T=1/2 with gap 1/(4T).

This is an actual LOWER theorem for every T. It does not assume or prove
acceptance of the parametric upper certificate. No interpolation completeness
or prox-existence axiom is used. No run claim is made beyond this prefix.
-/

noncomputable section
namespace LeanPEP.ActualFunction.ProximalGradientWitness

open Proximal
open LeanPEP.Profiles.ProximalGradientCertificate (boundQ boundQ_cast)

abbrev smoothFunction : ℝ → ℝ := ProximalGradientOneStepWitness.smoothFunction
abbrev smoothGradient : ℝ → ℝ := ProximalGradientOneStepWitness.smoothGradient

def slope (n : ℕ) : ℝ := 1 / (2 * ((n : ℝ) + 1))
def nonsmoothFunction (n : ℕ) (x : ℝ) : ℝ := slope n * max x 0 - x

def witnessPoint (n k : ℕ) : ℝ := 1 - (k : ℝ) * slope n

theorem slope_pos (n : ℕ) : 0 < slope n := by
  unfold slope
  positivity

theorem horizon_mul_slope (n : ℕ) : ((n : ℝ) + 1) * slope n = 1/2 := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  unfold slope
  field_simp [hn] <;> ring

theorem smooth_analytic : IsOneSmoothConvexAnalytic smoothFunction smoothGradient :=
  ProximalGradientOneStepWitness.smooth_analytic

theorem nonsmooth_convex (n : ℕ) : ConvexOn ℝ Set.univ (nonsmoothFunction n) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hleft : a * x + b * y ≤ a * max x 0 + b * max y 0 :=
    add_le_add (mul_le_mul_of_nonneg_left (le_max_left x 0) ha)
      (mul_le_mul_of_nonneg_left (le_max_left y 0) hb)
  have hright : 0 ≤ a * max x 0 + b * max y 0 :=
    add_nonneg (mul_nonneg ha (le_max_right x 0))
      (mul_nonneg hb (le_max_right y 0))
  have hmax := mul_le_mul_of_nonneg_left (max_le hleft hright) (le_of_lt (slope_pos n))
  simp only [nonsmoothFunction, smul_eq_mul]
  nlinarith

theorem star_subgradient (n : ℕ) :
    SubgradientAt (nonsmoothFunction n) (-smoothGradient 0) 0 := by
  intro y
  have hm := mul_nonneg (le_of_lt (slope_pos n)) (le_max_right y (0 : ℝ))
  norm_num [nonsmoothFunction, smoothGradient,
    ProximalGradientOneStepWitness.smoothGradient, RCLike.inner_apply] <;> nlinarith

/-- Each nonnegative point has the required affine-branch subgradient. -/
theorem subgradient_at_nonneg (n : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    SubgradientAt (nonsmoothFunction n) (slope n - 1) z := by
  intro y
  have hm := mul_le_mul_of_nonneg_left (le_max_left y (0 : ℝ)) (le_of_lt (slope_pos n))
  norm_num [nonsmoothFunction, max_eq_left hz, RCLike.inner_apply] <;> nlinarith

theorem composite_value (n : ℕ) (z : ℝ) :
    smoothFunction z + nonsmoothFunction n z = slope n * max z 0 := by
  unfold nonsmoothFunction
  change z + (slope n * max z 0 - z) = _
  ring

theorem star_isGlobalMin (n : ℕ) (z : ℝ) :
    smoothFunction 0 + nonsmoothFunction n 0 ≤ smoothFunction z + nonsmoothFunction n z := by
  rw [composite_value, composite_value]
  norm_num only [max_self, mul_zero]
  exact mul_nonneg (le_of_lt (slope_pos n)) (le_max_right z 0)

/-- The components are not separately stationary at the composite minimizer. -/
theorem smooth_gradient_at_star_ne_zero : smoothGradient 0 ≠ 0 :=
  ProximalGradientOneStepWitness.smooth_gradient_at_star_ne_zero

@[simp] theorem witnessPoint_zero (n : ℕ) : witnessPoint n 0 = 1 := by
  simp [witnessPoint]

theorem witnessPoint_succ (n k : ℕ) :
    witnessPoint n (k + 1) = witnessPoint n k - slope n := by
  simp only [witnessPoint, Nat.cast_add, Nat.cast_one]
  ring

theorem witnessPoint_final (n : ℕ) : witnessPoint n (n + 1) = 1/2 := by
  simp only [witnessPoint, Nat.cast_add, Nat.cast_one, horizon_mul_slope]
  norm_num

theorem witnessPoint_nonneg (n k : ℕ) (hk : k ≤ n + 1) : 0 ≤ witnessPoint n k := by
  have hkR : (k : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hk
  have hmul := mul_le_mul_of_nonneg_right hkR (le_of_lt (slope_pos n))
  rw [horizon_mul_slope] at hmul
  unfold witnessPoint
  linarith

theorem residual_value (n k : ℕ) :
    ProximalGradient.residual smoothGradient (witnessPoint n) k = slope n - 1 := by
  unfold ProximalGradient.residual
  rw [witnessPoint_succ]
  change witnessPoint n k - 1 - (witnessPoint n k - slope n) = _
  ring

/-- Prox minimality is derived from a proved residual subgradient, not assumed. -/
theorem actual_run (n : ℕ) :
    ProximalGradient.IsProxRun (n + 1) (nonsmoothFunction n) smoothGradient (witnessPoint n) := by
  intro k hk
  apply isUnitProxPoint_of_subgradient
  have hr := residual_value n k
  unfold ProximalGradient.residual at hr
  rw [hr]
  exact subgradient_at_nonneg n (witnessPoint_nonneg n (k + 1) (by omega))

theorem attains (n : ℕ) :
    (smoothFunction (witnessPoint n (n + 1)) + nonsmoothFunction n (witnessPoint n (n + 1))) -
      (smoothFunction 0 + nonsmoothFunction n 0) = (boundQ n : ℝ) := by
  rw [witnessPoint_final, composite_value, composite_value, boundQ_cast]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  norm_num [slope] <;> field_simp [hn] <;> ring

theorem radius (n : ℕ) : ‖witnessPoint n 0 - (0 : ℝ)‖ ^ 2 ≤ 1 := by
  norm_num [witnessPoint_zero]

/-- Membership alone is the correct all-horizon actual LOWER conclusion. -/
theorem bound_mem_analyticValues (n : ℕ) :
    (boundQ n : ℝ) ∈ ProximalGradient.oneDimensionalAnalyticValues n := by
  exact ⟨smoothFunction, nonsmoothFunction n, smoothGradient, 0, witnessPoint n,
    smooth_analytic, nonsmooth_convex n, star_subgradient n,
    actual_run n, radius n, attains n⟩

/-- The all-horizon lower witness also realizes the original compiled finite
model. This direction needs no interpolation completeness theorem. -/
theorem bound_mem_finiteValues (n : ℕ) :
    (boundQ n : ℝ) ∈ LeanPEP.Profiles.ProximalGradient.finiteValues n := by
  let s := ProximalGradient.residual smoothGradient (witnessPoint n)
  let d := ProximalGradient.actualData n smoothFunction (nonsmoothFunction n)
    smoothGradient 0 (witnessPoint n) s
  refine ⟨d, ?_, ?_, ?_⟩
  · exact FiniteGram.gramOfVectors_posSemidef _
  · exact ProximalGradient.actualData_constraints smooth_analytic.toFirstOrder
      (star_subgradient n) ((actual_run n).toResidualRun (nonsmooth_convex n)) (radius n)
  · change (LeanPEP.Profiles.ProximalGradient.objectiveQ n).evalR
      (ProximalGradient.actualData n smoothFunction (nonsmoothFunction n)
        smoothGradient 0 (witnessPoint n) s) = _
    rw [ProximalGradient.objective_eval]
    exact attains n

/-- Every genuine universal upper bound on the actual value set must dominate
this value. No existence of an upper bound is silently assumed. -/
theorem bound_le_any_upper (n : ℕ) (b : ℝ)
    (hb : ∀ r ∈ ProximalGradient.oneDimensionalAnalyticValues n, r ≤ b) :
    (boundQ n : ℝ) ≤ b := hb _ (bound_mem_analyticValues n)

end LeanPEP.ActualFunction.ProximalGradientWitness
