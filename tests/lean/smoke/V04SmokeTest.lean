import LeanPEP

namespace LeanPEP.Toy

#eval FiniteGD.checkFeasibleQ TwoStep.exactWitnessQ
#eval FiniteGD.auditPrimalQ TwoStep.exactWitnessQ
#eval FiniteGD.auditPrimalQ TwoStep.badCandidateQ

example : (FiniteGD.pointPairs 2).length = 16 := by
  exact TwoStep.twoStep_pointPair_count

example : FiniteGD.checkFeasibleQ TwoStep.exactWitnessQ = true := by
  exact TwoStep.exactWitnessQ_check

example : FiniteGD.Feasible TwoStep.exactWitness := by
  exact TwoStep.exactWitness_feasible

example (d : TwoStep.TwoStepData) (h : FiniteGD.Feasible d) :
    d.value 2 ≤ (1 : ℝ) / 10 := by
  exact TwoStep.twoStep_upper d h

example : IsGreatest TwoStep.pepValues ((1 : ℝ) / 10) := by
  exact TwoStep.twoStep_exact_value

example :
    FiniteGD.checkFeasibleQ
      (FiniteGD.fromOneStepQ OneStep.exactWitnessQ) = true := by
  exact FiniteGD.oneStep_exactWitness_generic_check

example :
    FiniteGD.checkFeasibleQ
      (FiniteGD.fromOneStepQ OneStep.pseudoCertQ) = false := by
  exact FiniteGD.oneStep_pseudoCert_generic_check

end LeanPEP.Toy
