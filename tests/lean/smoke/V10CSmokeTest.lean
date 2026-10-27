import LeanPEP

open LeanPEP
open LeanPEP.GramPEP
open LeanPEP.Bridges.NesterovChainGram

#check standardGram
#check standardGram_posSemidef
#check standardFactorCertQ
#check castDataQ
#check interpolationSlack_castDataQ
#check interpolationFeasibleQ_toReal

#check dim3PSDCertQ_check
#check dim3InterpolationFeasibleQ
#check dim3CoreFeasibleQ
#check dim3CoreFeasibleR
#check dim3TrajectoryQ
#check dim3NormalizedPerformanceQ
#check dim3DataR_eq_actual

#check dim5PSDCertQ_check
#check dim5InterpolationFeasibleQ
#check dim5CoreFeasibleQ
#check dim5CoreFeasibleR
#check dim5TrajectoryStep0Q
#check dim5TrajectoryStep1Q
#check dim5NormalizedPerformanceQ
#check dim5DataR_eq_actual

#eval checkPSDFactorQ dim3DataQ.gram dim3PSDCertQ
#eval checkPSDFactorQ dim5DataQ.gram dim5PSDCertQ

example : CoreFeasible dim3DataQ := by
  exact dim3CoreFeasibleQ

example : CoreFeasible dim5DataQ := by
  exact dim5CoreFeasibleQ

example :
    (dim3DataQ.value (.iter 1) - dim3DataQ.value .star) /
        gramNormSq dim3DataQ.gram
          (dim3DataQ.position (.iter 0) - dim3DataQ.position .star) =
      (3 : ℚ) / 56 := by
  exact dim3NormalizedPerformanceQ

example :
    (dim5DataQ.value (.iter 2) - dim5DataQ.value .star) /
        gramNormSq dim5DataQ.gram
          (dim5DataQ.position (.iter 0) - dim5DataQ.position .star) =
      (75 : ℚ) / 2816 := by
  exact dim5NormalizedPerformanceQ
