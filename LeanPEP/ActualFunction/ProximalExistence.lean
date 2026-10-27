import LeanPEP.ActualFunction.CompositeOptimality
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact

/-!
# Finite-dimensional existence for the existing real-valued prox predicate

No proximal operator or existence axiom is postulated. Convexity on the whole
finite-dimensional real space gives continuity. A compact unit ball supplies
an upper bound; convexity along the opposite unit direction gives a global
linear-growth lower bound. The positive quadratic penalty then confines a
minimizer to a compact ball. Uniqueness is the already proved C5 theorem.

Finite-dimensionality is explicit. This file does not assert that every
real-valued convex function on an infinite-dimensional Hilbert space has a
proximal minimizer, and it does not introduce extended-real functions.
-/

noncomputable section
open scoped NNReal
namespace LeanPEP.ActualFunction.ProximalScaling

open Metric Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A whole-space finite-dimensional convex function admits a radial affine
lower bound around every input. No supporting vector is assumed or chosen. -/
theorem exists_norm_lower_bound [FiniteDimensional ℝ E]
    {h : E → ℝ} (hh : ConvexOn ℝ Set.univ h) (v : E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, h v - C * ‖x-v‖ ≤ h x := by
  classical
  have hcont : Continuous h := continuousOn_univ.mp (hh.continuousOn isOpen_univ)
  have hv : v ∈ closedBall v (1 : ℝ) := by simp
  obtain ⟨z, hz, hmax⟩ := (isCompact_closedBall v (1 : ℝ)).exists_isMaxOn
    ⟨v, hv⟩ hcont.continuousOn
  refine ⟨h z - h v, sub_nonneg.mpr (hmax hv), ?_⟩
  intro x
  by_cases hx : x = v
  · simp only [hx, sub_self, norm_zero, mul_zero, sub_zero, le_refl]
  let r : ℝ := ‖x-v‖
  have hr : 0 < r := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  have hr1 : 0 < r+1 := by linarith only [hr]
  let y : E := v - r⁻¹ • (x-v)
  have hy : y ∈ closedBall v (1 : ℝ) := by
    apply mem_closedBall_iff_norm.mpr
    have hyv : y-v = -(r⁻¹ • (x-v)) := by dsimp [y]; abel
    rw [hyv, norm_neg, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
    change r⁻¹ * r ≤ 1
    rw [inv_mul_cancel₀ (ne_of_gt hr)]
  have hab : (1 : ℝ)/(r+1) + r/(r+1) = 1 := by
    field_simp [ne_of_gt hr1] <;> ring
  have hmul : r/(r+1) * r⁻¹ = 1/(r+1) := by
    field_simp [ne_of_gt hr, ne_of_gt hr1] <;> ring
  have hcombo : (1/(r+1)) • x + (r/(r+1)) • y = v := by
    dsimp only [y]
    rw [smul_sub, smul_smul, hmul, smul_sub]
    calc
      _ = (1/(r+1) + r/(r+1)) • v := by rw [add_smul]; abel
      _ = v := by rw [hab, one_smul]
  have hconv := hh.2 (mem_univ x) (mem_univ y)
    (by positivity : (0 : ℝ) ≤ 1/(r+1))
    (by positivity : (0 : ℝ) ≤ r/(r+1)) hab
  rw [hcombo] at hconv
  simp only [smul_eq_mul] at hconv
  have hupper : h v ≤ (1/(r+1))*h x + (r/(r+1))*h z :=
    hconv.trans (add_le_add (le_refl _)
      (mul_le_mul_of_nonneg_left (hmax hy) (by positivity)))
  have hclear := mul_le_mul_of_nonneg_left hupper (le_of_lt hr1)
  have hcancel : (r+1)*((1/(r+1))*h x + (r/(r+1))*h z) = h x+r*h z := by
    field_simp [ne_of_gt hr1] <;> ring
  rw [hcancel] at hclear
  change h v - (h z-h v)*r ≤ h x
  calc
    h v - (h z-h v)*r = (r+1)*h v-r*h z := by ring
    _ ≤ h x := (sub_le_iff_le_add).mpr hclear

/-- Every positive-parameter prox subproblem of a real-valued convex function
on a finite-dimensional real inner product space attains its minimum. -/
theorem exists_isProxPoint [FiniteDimensional ℝ E] {L : ℝ≥0} {h : E → ℝ}
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) (v : E) :
    ∃ x, IsProxPoint L h v x := by
  classical
  have hcont : Continuous h := continuousOn_univ.mp (hh.continuousOn isOpen_univ)
  obtain ⟨C, hC, hlower⟩ := exists_norm_lower_bound hh v
  let Q : E → ℝ := fun x => h x + ((L : ℝ)/2)*‖x-v‖^2
  let r : ℝ := 2*C/(L : ℝ)+1
  have hr : 0 < r := by dsimp [r]; positivity
  have hQ : Continuous Q := by
    dsimp only [Q]
    exact hcont.add (continuous_const.mul ((continuous_id.sub continuous_const).norm.pow 2))
  have hv : v ∈ closedBall v r := by simp [hr.le]
  obtain ⟨z, hz, hmin⟩ := (isCompact_closedBall v r).exists_isMinOn ⟨v, hv⟩ hQ.continuousOn
  refine ⟨z, (isProxPoint_iff_norm L h v z).mpr ?_⟩
  intro y
  change Q z ≤ Q y
  by_cases hy : y ∈ closedBall v r
  · exact hmin hy
  have hfar : r < ‖y-v‖ := lt_of_not_ge (fun hle => hy (mem_closedBall_iff_norm.mpr hle))
  have hfrac : 2*C/(L : ℝ) ≤ ‖y-v‖ := by
    dsimp only [r] at hfar
    linarith only [hfar]
  have hproduct : 2*C ≤ ‖y-v‖*(L : ℝ) := (div_le_iff₀ hL).mp hfrac
  have hcoeff : 0 ≤ ((L : ℝ)/2)*‖y-v‖-C := by nlinarith only [hproduct]
  have hquad := mul_nonneg hcoeff (norm_nonneg (y-v))
  have hout : h v ≤ Q y := by
    dsimp only [Q]
    have hl := hlower y
    nlinarith only [hl, hquad]
  have hzv : Q z ≤ h v := by
    have hcompare : Q z ≤ Q v := hmin hv
    simpa only [Q, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
      add_zero] using hcompare
  exact hzv.trans hout

/-- Existence and uniqueness for the same C4 predicate, not a new minimization
semantics. Positivity is essential; no conclusion at L=0 is claimed. -/
theorem existsUnique_isProxPoint [FiniteDimensional ℝ E] {L : ℝ≥0} {h : E → ℝ}
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) (v : E) :
    ∃! x, IsProxPoint L h v x := by
  obtain ⟨x, hx⟩ := exists_isProxPoint hL hh v
  exact ⟨x, hx, fun y hy => isProxPoint_unique hL hh hx hy⟩

end LeanPEP.ActualFunction.ProximalScaling
