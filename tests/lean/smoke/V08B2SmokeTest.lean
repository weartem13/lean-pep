import LeanPEP

open LeanPEP.HardInstances.NesterovChain
open LeanPEP.Comparisons

#check unitGDStep
#check IsUnitGDPath
#check unitNormalizedPerformance
#check dim3_gradient_start
#check dim3_step_zero
#check dim3Path_isUnitGD
#check dim3_gap_after_one
#check dim3_initialDistanceSq
#check dim3_unitNormalizedPerformance
#check dim5_gradient_start
#check dim5_gradient_after_one
#check dim5_step_zero
#check dim5_step_one
#check dim5Path_isUnitGD
#check dim5_gap_after_two
#check dim5_initialDistanceSq
#check dim5_unitNormalizedPerformance
#check nesterovDim3_oneStep_comparison
#check nesterovDim5_twoStep_comparison

example : dim3X1 = ![((1 : ℝ) / 4), 0, 0] := rfl

example : dim5X2 =
    ![((3 : ℝ) / 8), ((1 : ℝ) / 16), 0, 0, 0] := rfl

example : unitNormalizedPerformance dim3X0 dim3X1 = (3 : ℝ) / 56 :=
  dim3_unitNormalizedPerformance

example : unitNormalizedPerformance dim3X0 dim3X1 < (1 : ℝ) / 6 :=
  nesterovDim3_oneStep_lt_finitePEP

example : unitNormalizedPerformance dim5X0 dim5X2 = (75 : ℝ) / 2816 :=
  dim5_unitNormalizedPerformance

example : unitNormalizedPerformance dim5X0 dim5X2 < (1 : ℝ) / 10 :=
  nesterovDim5_twoStep_lt_finitePEP
