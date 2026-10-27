import LeanPEP

open LeanPEP.HardInstances.NesterovChain

#check quadraticForm_chainMatrix
#check chainMatrix_posSemidef
#check quadraticForm_chainMatrix_le
#check function_add_expansion
#check function_sub_expansion
#check convex_firstOrder
#check smooth_upperModel
#check gradient_sub_eq_hessian_mulVec
#check hessian_posSemidef
#check quadraticForm_hessian_le
#check chainMatrix_mulVec_minimizer
#check gradient_minimizer
#check minimizer_isGlobalMin
#check function_minimizer_value

/-- The classic three-dimensional chain uses branch parameter `n = 2`. -/
example : minimizer 2 (0 : Fin 3) = (3 : ℝ) / 4 := by
  norm_num [minimizer]

example : minimizer 2 (Fin.last 2) = (1 : ℝ) / 4 := by
  norm_num [minimizer]

example : energy (minimizer 2) = (3 : ℝ) / 4 := by
  rw [energy_minimizer]
  norm_num [minimizerStep]

example : quadraticForm (chainMatrix 2) (minimizer 2) = (3 : ℝ) / 4 := by
  rw [quadraticForm_chainMatrix, energy_minimizer]
  norm_num [minimizerStep]

example : function 2 1 (minimizer 2) = -(3 : ℝ) / 32 := by
  rw [function_minimizer_value]
  norm_num
