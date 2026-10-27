import LeanPEP.HardInstances.NesterovChain.Minimizer
import Mathlib.Data.Fin.VecNotation

/-!
# Exact small gradient-descent trajectories on the Nesterov chain

This file specializes the explicit Nesterov-chain function to the normalized
smoothness parameter `L = 1`.  A standard gradient-descent step therefore has
step size `1 / L = 1` and is exactly

`x⁺ = x - gradient n 1 x`.

Two finite trajectories are checked exactly:

* one step in ambient dimension `3` (branch parameter `n = 2`); and
* two steps in ambient dimension `5` (branch parameter `n = 4`).

The coordinate calculations use the already verified real-function semantics.
They do not identify the Hessian structure matrix with a PEP Gram matrix and
they do not yet construct a finite-PEP witness.
-/

namespace LeanPEP
namespace HardInstances
namespace NesterovChain

open scoped BigOperators Matrix
open Matrix

/-- One standard gradient-descent step for the normalized chain with `L = 1`. -/
noncomputable def unitGDStep {n : ℕ} (x : Vector n) : Vector n :=
  x - gradient n 1 x

/-- A finite path follows normalized, unit-step gradient descent. -/
def IsUnitGDPath {n steps : ℕ} (path : Fin (steps + 1) → Vector n) : Prop :=
  ∀ k : Fin steps, path k.succ = unitGDStep (path k.castSucc)

/-- The dimensionless performance ratio used to compare the explicit `L = 1`
trajectory with the normalized finite-PEP constants. -/
noncomputable def unitNormalizedPerformance {n : ℕ}
    (x0 xk : Vector n) : ℝ :=
  (function n 1 xk - function n 1 (minimizer n)) /
    normSq (x0 - minimizer n)

/-- At the zero vector, the normalized gradient is exactly `-(1 / 4) e₀`. -/
theorem gradient_zero (n : ℕ) :
    gradient n 1 (0 : Vector n) = -(((1 : ℝ) / 4) • firstBasis n) := by
  simp [gradient]

/-! ## One step in ambient dimension 3 -/

/-- Initial point for the dimension-3 regression. -/
noncomputable def dim3X0 : Vector 2 :=
  ![0, 0, 0]

@[simp] theorem dim3X0_apply (i : Fin 3) :
    dim3X0 i = 0 := by
  fin_cases i <;> rfl

@[simp] theorem dim3X0_eq_zero :
    dim3X0 = (0 : Vector 2) := by
  funext i
  simp

/-- Exact gradient at the dimension-3 initial point. -/
noncomputable def dim3G0 : Vector 2 :=
  ![-((1 : ℝ) / 4), 0, 0]

/-- Exact point after one standard gradient-descent step. -/
noncomputable def dim3X1 : Vector 2 :=
  ![((1 : ℝ) / 4), 0, 0]

@[simp] theorem dim3X1_apply (i : Fin 3) :
    dim3X1 i = if i = 0 then (1 : ℝ) / 4 else 0 := by
  fin_cases i <;> norm_num [dim3X1]

/-- The complete one-step dimension-3 path. -/
noncomputable def dim3Path : Fin 2 → Vector 2 :=
  ![dim3X0, dim3X1]

/-- Exact initial gradient in dimension 3. -/
theorem dim3_gradient_start :
    gradient 2 1 dim3X0 = dim3G0 := by
  rw [dim3X0_eq_zero, gradient_zero]
  funext i
  fin_cases i <;>
    norm_num [dim3G0, firstBasis, Pi.single_apply]

/-- The displayed dimension-3 point is exactly the first GD iterate. -/
theorem dim3_step_zero :
    unitGDStep dim3X0 = dim3X1 := by
  unfold unitGDStep
  rw [dim3_gradient_start]
  funext i
  fin_cases i <;> norm_num [dim3X0, dim3G0, dim3X1]

/-- The two displayed points satisfy the GD recurrence. -/
theorem dim3Path_isUnitGD :
    IsUnitGDPath dim3Path := by
  intro k
  fin_cases k
  simpa [dim3Path] using dim3_step_zero.symm

/-- Exact initial function value in dimension 3. -/
theorem dim3_function_start :
    function 2 1 dim3X0 = 0 := by
  unfold function energy
  rw [Fin.sum_univ_two]
  norm_num [edgeDiff, Fin.last]

/-- Exact function value after one step in dimension 3. -/
theorem dim3_function_after_one :
    function 2 1 dim3X1 = -((3 : ℝ) / 64) := by
  unfold function energy
  rw [Fin.sum_univ_two]
  norm_num [edgeDiff, Fin.last, Fin.ext_iff]

/-- Exact optimal value for the dimension-3 chain. -/
theorem dim3_function_minimum :
    function 2 1 (minimizer 2) = -((3 : ℝ) / 32) := by
  rw [function_minimizer_value]
  norm_num

/-- Exact final objective gap after one step. -/
theorem dim3_gap_after_one :
    function 2 1 dim3X1 - function 2 1 (minimizer 2)
      = (3 : ℝ) / 64 := by
  rw [dim3_function_after_one, dim3_function_minimum]
  norm_num

/-- Exact squared initial distance to the minimizer in dimension 3. -/
theorem dim3_initialDistanceSq :
    normSq (dim3X0 - minimizer 2) = (7 : ℝ) / 8 := by
  unfold normSq
  rw [Fin.sum_univ_three]
  norm_num [minimizer]

/-- The normalized one-step performance is exactly `3 / 56`. -/
theorem dim3_unitNormalizedPerformance :
    unitNormalizedPerformance dim3X0 dim3X1 = (3 : ℝ) / 56 := by
  unfold unitNormalizedPerformance
  rw [dim3_gap_after_one, dim3_initialDistanceSq]
  norm_num

/-! ## Two steps in ambient dimension 5 -/

/-- Initial point for the dimension-5 regression. -/
noncomputable def dim5X0 : Vector 4 :=
  ![0, 0, 0, 0, 0]

@[simp] theorem dim5X0_apply (i : Fin 5) :
    dim5X0 i = 0 := by
  fin_cases i <;> rfl

@[simp] theorem dim5X0_eq_zero :
    dim5X0 = (0 : Vector 4) := by
  funext i
  simp

/-- Exact initial gradient in dimension 5. -/
noncomputable def dim5G0 : Vector 4 :=
  ![-((1 : ℝ) / 4), 0, 0, 0, 0]

/-- Exact point after one standard gradient-descent step in dimension 5. -/
noncomputable def dim5X1 : Vector 4 :=
  ![((1 : ℝ) / 4), 0, 0, 0, 0]

@[simp] theorem dim5X1_apply (i : Fin 5) :
    dim5X1 i = if i = 0 then (1 : ℝ) / 4 else 0 := by
  fin_cases i <;> norm_num [dim5X1]

/-- Exact gradient at the first dimension-5 iterate. -/
noncomputable def dim5G1 : Vector 4 :=
  ![-((1 : ℝ) / 8), -((1 : ℝ) / 16), 0, 0, 0]

/-- Exact point after two standard gradient-descent steps in dimension 5. -/
noncomputable def dim5X2 : Vector 4 :=
  ![((3 : ℝ) / 8), ((1 : ℝ) / 16), 0, 0, 0]

@[simp] theorem dim5X2_apply (i : Fin 5) :
    dim5X2 i =
      if i = 0 then (3 : ℝ) / 8
      else if i = 1 then (1 : ℝ) / 16
      else 0 := by
  fin_cases i <;> norm_num [dim5X2]

/-- The complete two-step dimension-5 path. -/
noncomputable def dim5Path : Fin 3 → Vector 4 :=
  ![dim5X0, dim5X1, dim5X2]

/-- Exact initial gradient in dimension 5. -/
theorem dim5_gradient_start :
    gradient 4 1 dim5X0 = dim5G0 := by
  rw [dim5X0_eq_zero, gradient_zero]
  funext i
  fin_cases i <;>
    norm_num [dim5G0, firstBasis, Pi.single_apply]

/-- Polarization against the first dimension-5 iterate has a two-coordinate form. -/
theorem energyInner_dim5X1 (z : Vector 4) :
    energyInner dim5X1 z =
      ((1 : ℝ) / 2) * z 0 - ((1 : ℝ) / 4) * z 1 := by
  unfold energyInner
  rw [Fin.sum_univ_four]
  simp [edgeDiff, Fin.last]
  ring

/-- Exact gradient at the first dimension-5 iterate. -/
theorem dim5_gradient_after_one :
    gradient 4 1 dim5X1 = dim5G1 := by
  classical
  funext i
  have h := gradient_dot (n := 4) 1 dim5X1 (Pi.single i 1)
  rw [energyInner_dim5X1] at h
  fin_cases i <;>
    norm_num [dim5G1, Pi.single_apply] at h ⊢ <;>
    exact h

/-- The displayed first dimension-5 point is exactly the first GD iterate. -/
theorem dim5_step_zero :
    unitGDStep dim5X0 = dim5X1 := by
  unfold unitGDStep
  rw [dim5_gradient_start]
  funext i
  fin_cases i <;> norm_num [dim5X0, dim5G0, dim5X1]

/-- The displayed second dimension-5 point is exactly the second GD iterate. -/
theorem dim5_step_one :
    unitGDStep dim5X1 = dim5X2 := by
  unfold unitGDStep
  rw [dim5_gradient_after_one]
  funext i
  fin_cases i <;> norm_num [dim5X1, dim5G1, dim5X2]

/-- The three displayed points satisfy both GD recurrence equations. -/
theorem dim5Path_isUnitGD :
    IsUnitGDPath dim5Path := by
  intro k
  fin_cases k
  · simpa [dim5Path] using dim5_step_zero.symm
  · simpa [dim5Path] using dim5_step_one.symm

/-- Exact initial function value in dimension 5. -/
theorem dim5_function_start :
    function 4 1 dim5X0 = 0 := by
  unfold function energy
  rw [Fin.sum_univ_four]
  norm_num [edgeDiff, Fin.last]

/-- Exact function value after one step in dimension 5. -/
theorem dim5_function_after_one :
    function 4 1 dim5X1 = -((3 : ℝ) / 64) := by
  unfold function energy
  rw [Fin.sum_univ_four]
  norm_num [edgeDiff, Fin.last, Fin.ext_iff]

/-- Exact function value after two steps in dimension 5. -/
theorem dim5_function_after_two :
    function 4 1 dim5X2 = -((65 : ℝ) / 1024) := by
  unfold function energy
  rw [Fin.sum_univ_four]
  norm_num [edgeDiff, Fin.last, Fin.ext_iff]

/-- Exact optimal value for the dimension-5 chain. -/
theorem dim5_function_minimum :
    function 4 1 (minimizer 4) = -((5 : ℝ) / 48) := by
  rw [function_minimizer_value]
  norm_num

/-- Exact final objective gap after two steps. -/
theorem dim5_gap_after_two :
    function 4 1 dim5X2 - function 4 1 (minimizer 4)
      = (125 : ℝ) / 3072 := by
  rw [dim5_function_after_two, dim5_function_minimum]
  norm_num

/-- Exact squared initial distance to the minimizer in dimension 5. -/
theorem dim5_initialDistanceSq :
    normSq (dim5X0 - minimizer 4) = (55 : ℝ) / 36 := by
  unfold normSq
  rw [Fin.sum_univ_five]
  norm_num [minimizer]

/-- The normalized two-step performance is exactly `75 / 2816`. -/
theorem dim5_unitNormalizedPerformance :
    unitNormalizedPerformance dim5X0 dim5X2 = (75 : ℝ) / 2816 := by
  unfold unitNormalizedPerformance
  rw [dim5_gap_after_two, dim5_initialDistanceSq]
  norm_num

end NesterovChain
end HardInstances
end LeanPEP
