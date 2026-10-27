import LeanPEP.HardInstances.NesterovChain.Matrix

/-!
# The explicit Nesterov chain function

For the chain matrix `A` in dimension `n + 1`, define

`f(x) = (L / 8) xᵀ A x - (L / 4) x₀`.

Rather than relying on an opaque calculus step, this file proves an exact
first-order expansion.  The remainder is `(L / 8)` times the chain energy.
For `L ≥ 0`, the lower and upper quadratic models therefore establish the
convexity and `L`-smoothness semantics needed by later PEP bridges.
-/

namespace LeanPEP
namespace HardInstances
namespace NesterovChain

open scoped BigOperators Matrix
open Matrix

/-- The Nesterov chain quadratic function. -/
noncomputable def function (n : ℕ) (L : ℝ) (x : Vector n) : ℝ :=
  (L / 8) * energy x - (L / 4) * x 0

/-- The explicit gradient field `(L / 4) (A x - e₀)`. -/
noncomputable def gradient (n : ℕ) (L : ℝ) (x : Vector n) : Vector n :=
  (L / 4) • ((chainMatrix n) *ᵥ x - firstBasis n)

/-- The constant Hessian matrix `(L / 4) A`. -/
noncomputable def hessian (n : ℕ) (L : ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  (L / 4) • chainMatrix n

/-- Pairing the explicit gradient with a displacement gives the polarized
chain energy minus the first-coordinate linear term. -/
theorem gradient_dot {n : ℕ} (L : ℝ) (x d : Vector n) :
    gradient n L x ⬝ᵥ d
      = (L / 4) * energyInner x d - (L / 4) * d 0 := by
  unfold gradient
  simp only [smul_dotProduct, sub_dotProduct, smul_eq_mul]
  rw [dotProduct_comm ((chainMatrix n) *ᵥ x) d]
  change (L / 4) * (bilinearForm (chainMatrix n) d x - firstBasis n ⬝ᵥ d) = _
  rw [bilinearForm_chainMatrix, firstBasis_dot, energyInner_comm]
  ring

/-- Exact first-order expansion at an additive displacement. -/
theorem function_add_expansion {n : ℕ} (L : ℝ) (x d : Vector n) :
    function n L (x + d)
      = function n L x
        + gradient n L x ⬝ᵥ d
        + (L / 8) * energy d := by
  unfold function
  rw [energy_add, gradient_dot]
  simp only [Pi.add_apply]
  ring

/-- Exact first-order expansion between two arbitrary points. -/
theorem function_sub_expansion {n : ℕ} (L : ℝ) (x y : Vector n) :
    function n L y
      = function n L x
        + gradient n L x ⬝ᵥ (y - x)
        + (L / 8) * energy (y - x) := by
  have h := function_add_expansion (n := n) L x (y - x)
  convert h using 1 <;> abel

/-- First-order convexity inequality. -/
theorem convex_firstOrder {n : ℕ} {L : ℝ} (hL : 0 ≤ L)
    (x y : Vector n) :
    function n L x + gradient n L x ⬝ᵥ (y - x)
      ≤ function n L y := by
  have hrem : 0 ≤ (L / 8) * energy (y - x) := by
    exact mul_nonneg (by positivity) (energy_nonneg (y - x))
  calc
    function n L x + gradient n L x ⬝ᵥ (y - x)
        ≤ function n L x + gradient n L x ⬝ᵥ (y - x)
            + (L / 8) * energy (y - x) :=
      le_add_of_nonneg_right hrem
    _ = function n L y := (function_sub_expansion (n := n) L x y).symm

/-- The exact `L`-smooth upper quadratic model. -/
theorem smooth_upperModel {n : ℕ} {L : ℝ} (hL : 0 ≤ L)
    (x y : Vector n) :
    function n L y
      ≤ function n L x
        + gradient n L x ⬝ᵥ (y - x)
        + (L / 2) * normSq (y - x) := by
  have hscale :
      (L / 8) * energy (y - x)
        ≤ (L / 2) * normSq (y - x) := by
    calc
      (L / 8) * energy (y - x)
          ≤ (L / 8) * (4 * normSq (y - x)) :=
        mul_le_mul_of_nonneg_left
          (energy_le_four_normSq (y - x)) (by positivity)
      _ = (L / 2) * normSq (y - x) := by ring
  calc
    function n L y
        = function n L x + gradient n L x ⬝ᵥ (y - x)
            + (L / 8) * energy (y - x) :=
      function_sub_expansion (n := n) L x y
    _ ≤ function n L x + gradient n L x ⬝ᵥ (y - x)
          + (L / 2) * normSq (y - x) :=
      add_le_add_right hscale
        (function n L x + gradient n L x ⬝ᵥ (y - x))

/-- The gradient increment is exactly the Hessian applied to the point
increment.  This is the constant-Hessian semantics of the quadratic. -/
theorem gradient_sub_eq_hessian_mulVec {n : ℕ} (L : ℝ) (x y : Vector n) :
    gradient n L y - gradient n L x
      = (hessian n L) *ᵥ (y - x) := by
  funext i
  simp [gradient, hessian, Matrix.smul_mulVec, Matrix.mulVec_sub] <;> ring

/-- The Hessian quadratic form is `(L / 4)` times the chain energy. -/
theorem quadraticForm_hessian {n : ℕ} (L : ℝ) (x : Vector n) :
    quadraticForm (hessian n L) x = (L / 4) * energy x := by
  unfold hessian quadraticForm bilinearForm
  rw [Matrix.smul_mulVec, dotProduct_smul]
  simp only [smul_eq_mul]
  change (L / 4) * bilinearForm (chainMatrix n) x x = _
  rw [bilinearForm_chainMatrix, ← energy_eq_energyInner]

/-- For `L ≥ 0`, the Hessian is positive semidefinite. -/
theorem hessian_posSemidef (n : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    (hessian n L).PosSemidef := by
  unfold hessian
  exact (chainMatrix_posSemidef n).smul (by positivity)

/-- The constant Hessian obeys `0 ≤ H ≤ L I` in quadratic form. -/
theorem quadraticForm_hessian_le {n : ℕ} {L : ℝ} (hL : 0 ≤ L)
    (x : Vector n) :
    quadraticForm (hessian n L) x ≤ L * normSq x := by
  rw [quadraticForm_hessian]
  have hscale :
      (L / 4) * energy x ≤ (L / 4) * (4 * normSq x) := by
    exact mul_le_mul_of_nonneg_left (energy_le_four_normSq x) (by positivity)
  nlinarith

end NesterovChain
end HardInstances
end LeanPEP
