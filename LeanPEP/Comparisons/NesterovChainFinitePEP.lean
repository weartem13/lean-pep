import LeanPEP.HardInstances.NesterovChain.SmallTrajectory
import LeanPEP.Toy.OneStep.ExactValue
import LeanPEP.Toy.TwoStep.ExactValue

/-!
# Comparing small Nesterov-chain trajectories with exact finite-PEP constants

The explicit Nesterov-chain trajectories and the one-dimensional finite PEP are
separate formal objects.  This file makes only an exact scalar comparison of
their normalized performance values.  It does not claim a general-dimensional
PEP conversion or an interpolation theorem.
-/

namespace LeanPEP
namespace Comparisons

open HardInstances.NesterovChain

/-- The classic dimension-3 one-step chain value is strictly below the exact
one-step finite-PEP constant `1 / 6`. -/
theorem nesterovDim3_oneStep_lt_finitePEP :
    unitNormalizedPerformance dim3X0 dim3X1 < (1 : ℝ) / 6 := by
  rw [dim3_unitNormalizedPerformance]
  norm_num

/-- The comparison packaged together with the already proved exact finite-PEP
value theorem. -/
theorem nesterovDim3_oneStep_comparison :
    IsGreatest Toy.OneStep.pepValues ((1 : ℝ) / 6) ∧
      unitNormalizedPerformance dim3X0 dim3X1 = (3 : ℝ) / 56 ∧
      unitNormalizedPerformance dim3X0 dim3X1 < (1 : ℝ) / 6 := by
  exact ⟨Toy.OneStep.oneStep_exact_value,
    ⟨dim3_unitNormalizedPerformance,
      nesterovDim3_oneStep_lt_finitePEP⟩⟩

/-- The classic dimension-5 two-step chain value is strictly below the exact
two-step finite-PEP constant `1 / 10`. -/
theorem nesterovDim5_twoStep_lt_finitePEP :
    unitNormalizedPerformance dim5X0 dim5X2 < (1 : ℝ) / 10 := by
  rw [dim5_unitNormalizedPerformance]
  norm_num

/-- The two-step comparison packaged with the exact finite-PEP value theorem. -/
theorem nesterovDim5_twoStep_comparison :
    IsGreatest Toy.TwoStep.pepValues ((1 : ℝ) / 10) ∧
      unitNormalizedPerformance dim5X0 dim5X2 = (75 : ℝ) / 2816 ∧
      unitNormalizedPerformance dim5X0 dim5X2 < (1 : ℝ) / 10 := by
  exact ⟨Toy.TwoStep.twoStep_exact_value,
    ⟨dim5_unitNormalizedPerformance,
      nesterovDim5_twoStep_lt_finitePEP⟩⟩

end Comparisons
end LeanPEP
