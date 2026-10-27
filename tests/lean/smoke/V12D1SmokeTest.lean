import LeanPEP.ActualFunction.HuberWitness

open LeanPEP
open LeanPEP.ActualFunction
open LeanPEP.ActualFunction.HuberWitness

#check huberFunction
#check huberGradient
#check lowerModel
#check upperModel
#check firstOrder
#check threshold
#check threshold_eq_gdCenterQ_cast
#check witnessFunction
#check witnessGradient
#check witnessPoint
#check witness_firstOrder
#check witness_zero_isGlobalMin

example :
    IsOneSmoothConvexFirstOrder
      (witnessFunction 4) (witnessGradient 4) :=
  witness_firstOrder 4

example : witnessGradient 4 0 = 0 :=
  witnessGradient_zero 4

example : witnessFunction 4 0 ≤ witnessFunction 4 2 :=
  witness_zero_isGlobalMin 4 2

example : witnessPoint 4 1 = 1 - threshold 4 := by
  simp
