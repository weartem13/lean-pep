import LeanPEP.ActualFunction.HuberWitnessTrajectory

open LeanPEP
open LeanPEP.ActualFunction
open LeanPEP.ActualFunction.HuberWitness
open LeanPEP.ActualFunction.ParametricGDActual
open LeanPEP.Toy.FiniteGD.ParametricUpper

#check threshold_den_mul
#check threshold_le_witnessPoint
#check witnessGradient_witnessPoint
#check witnessFunction_witnessPoint
#check witnessPoint_unitGD_step
#check unitGDIterate_eq_witnessPoint
#check unitGDIterate_final
#check witnessPoint_final_eq_midpoint
#check witnessFunction_final_eq_half_threshold
#check half_threshold_eq_gdBoundQ_cast
#check gdBoundQ_cast_eq_closed
#check witnessFunction_final_eq_bound
#check witness_unitGD_attains_bound
#check witness_unitGD_attains_closed_form
#check normalized_lower_witness

example :
    unitGDIterate (witnessGradient 4) 1 4 =
      witnessPoint 4 4 :=
  unitGDIterate_final 4

example :
    witnessFunction 4
        (unitGDIterate (witnessGradient 4) 1 4) -
      witnessFunction 4 0 =
        (gdBoundQ 4 : ℝ) :=
  witness_unitGD_attains_bound 4

example :
    witnessFunction 4
        (unitGDIterate (witnessGradient 4) 1 4) -
      witnessFunction 4 0 = (1 : ℝ) / 18 := by
  simpa using witness_unitGD_attains_closed_form 4

example :
    IsOneSmoothConvexFirstOrder
        (witnessFunction 4) (witnessGradient 4) ∧
      witnessGradient 4 0 = 0 ∧
      (∀ x : ℝ, witnessFunction 4 0 ≤ witnessFunction 4 x) ∧
      ‖(1 : ℝ) - 0‖ ^ 2 ≤ 1 ∧
      witnessFunction 4
          (unitGDIterate (witnessGradient 4) 1 4) -
        witnessFunction 4 0 =
          (gdBoundQ 4 : ℝ) :=
  normalized_lower_witness 4
