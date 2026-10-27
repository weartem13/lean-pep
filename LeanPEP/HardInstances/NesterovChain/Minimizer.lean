import LeanPEP.HardInstances.NesterovChain.Function

/-!
# Minimizer and optimal value of the Nesterov chain

The file uses Lean's zero-based `Fin` indexing.  In dimension `n + 1`, the
coordinate formula is

`x★ i = 1 - (i.val + 1) / (n + 2)`.

This is the zero-based form of the usual one-based expression
`1 - i / (dimension + 1)`.
-/

namespace LeanPEP
namespace HardInstances
namespace NesterovChain

open scoped BigOperators Matrix
open Matrix

/-- The reciprocal affine step appearing in the minimizer. -/
noncomputable def minimizerStep (n : ℕ) : ℝ :=
  1 / (((n + 2 : ℕ) : ℝ))

/-- The explicit minimizer in dimension `n + 1`, using zero-based indices. -/
noncomputable def minimizer (n : ℕ) : Vector n :=
  fun i => 1 - (((i.val + 1 : ℕ) : ℝ) / (((n + 2 : ℕ) : ℝ)))

@[simp] theorem minimizer_zero (n : ℕ) :
    minimizer n 0 = 1 - minimizerStep n := by
  simp [minimizer, minimizerStep]

@[simp] theorem minimizer_last (n : ℕ) :
    minimizer n (Fin.last n) = minimizerStep n := by
  have hd : (((n + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
  unfold minimizer minimizerStep
  simp only [Fin.val_last]
  push_cast
  field_simp [hd] <;> ring

@[simp] theorem edgeDiff_minimizer {n : ℕ} (i : Fin n) :
    edgeDiff (minimizer n) i = minimizerStep n := by
  have hd : (((n + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
  unfold edgeDiff minimizer minimizerStep
  simp only [Fin.val_castSucc, Fin.val_succ]
  push_cast
  field_simp [hd] <;> ring

/-- Polarization against the minimizer selects the first coordinate.  This is
the scalar form of `A x★ = e₀`. -/
theorem energyInner_minimizer {n : ℕ} (z : Vector n) :
    energyInner (minimizer n) z = z 0 := by
  simp only [energyInner, minimizer_zero, edgeDiff_minimizer, minimizer_last]
  rw [← Finset.mul_sum, sum_edgeDiff]
  ring


/-- The stationary matrix equation tested with the minimizer in the right
argument. -/
theorem chainMatrix_minimizer_bilinear_left {n : ℕ} (z : Vector n) :
    bilinearForm (chainMatrix n) z (minimizer n) = z 0 := by
  rw [bilinearForm_chainMatrix, energyInner_comm, energyInner_minimizer]

/-- Exact vector form of `A x★ = e₀`. -/
theorem chainMatrix_mulVec_minimizer (n : ℕ) :
    (chainMatrix n) *ᵥ minimizer n = firstBasis n := by
  classical
  funext i
  calc
    ((chainMatrix n) *ᵥ minimizer n) i
        = bilinearForm (chainMatrix n) (Pi.single i 1) (minimizer n) := by
          simp [bilinearForm]
    _ = (Pi.single i 1 : Vector n) 0 :=
      chainMatrix_minimizer_bilinear_left (n := n) (Pi.single i 1)
    _ = firstBasis n i := by
      by_cases hi : i = 0
      · subst i
        simp [firstBasis]
      · have h0i : (0 : Fin (n + 1)) ≠ i := Ne.symm hi
        simp [firstBasis, hi, h0i]

/-- The minimizer's chain energy is its first coordinate. -/
theorem energy_minimizer (n : ℕ) :
    energy (minimizer n) = 1 - minimizerStep n := by
  rw [energy_eq_energyInner, energyInner_minimizer, minimizer_zero]

/-- The explicit gradient vanishes at the minimizer. -/
theorem gradient_minimizer_dot {n : ℕ} (L : ℝ) (z : Vector n) :
    gradient n L (minimizer n) ⬝ᵥ z = 0 := by
  rw [gradient_dot, energyInner_minimizer]
  ring

/-- Vector form of the stationarity equation. -/
theorem gradient_minimizer (n : ℕ) (L : ℝ) :
    gradient n L (minimizer n) = 0 := by
  unfold gradient
  rw [chainMatrix_mulVec_minimizer]
  simp

/-- Completing the square around the minimizer. -/
theorem function_eq_minimum_add_energy {n : ℕ} (L : ℝ) (x : Vector n) :
    function n L x
      = function n L (minimizer n)
        + (L / 8) * energy (x - minimizer n) := by
  simpa [gradient_minimizer] using
    function_sub_expansion (n := n) L (minimizer n) x

/-- The minimizer is globally optimal when `L ≥ 0`. -/
theorem minimizer_isGlobalMin {n : ℕ} {L : ℝ} (hL : 0 ≤ L)
    (x : Vector n) :
    function n L (minimizer n) ≤ function n L x := by
  have hrem : 0 ≤ (L / 8) * energy (x - minimizer n) := by
    exact mul_nonneg (by positivity) (energy_nonneg (x - minimizer n))
  calc
    function n L (minimizer n)
        ≤ function n L (minimizer n)
            + (L / 8) * energy (x - minimizer n) :=
      le_add_of_nonneg_right hrem
    _ = function n L x :=
      (function_eq_minimum_add_energy (n := n) L x).symm

/-- Exact optimal value in dimension `n + 1`. -/
theorem function_minimizer_value (n : ℕ) (L : ℝ) :
    function n L (minimizer n)
      = -(L / 8) * (1 - 1 / (((n + 2 : ℕ) : ℝ))) := by
  rw [function, energy_minimizer, minimizer_zero]
  unfold minimizerStep
  ring

/-- The stationary matrix equation, expressed through all bilinear tests. -/
theorem chainMatrix_minimizer_bilinear {n : ℕ} (z : Vector n) :
    bilinearForm (chainMatrix n) (minimizer n) z = z 0 := by
  rw [bilinearForm_chainMatrix, energyInner_minimizer]

end NesterovChain
end HardInstances
end LeanPEP
