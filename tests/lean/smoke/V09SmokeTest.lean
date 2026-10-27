import LeanPEP

open LeanPEP.Toy.ThreeStep

#check threeStep_pointPair_count
#check exactWitnessQ_check
#check exactWitness_feasible
#check exactWitness_value
#check threeStepUpperCertQ_check
#check threeStep_upper
#check threeStep_exact_value

#eval LeanPEP.Toy.FiniteGD.checkFeasibleQ exactWitnessQ
#eval LeanPEP.Toy.FiniteGD.checkUpperCertQ threeStepUpperCertQ
#eval LeanPEP.Toy.FiniteGD.auditUpperCertQ threeStepUpperCertQ

example : exactWitnessQ.value 3 = (1 : ℚ) / 14 := by
  exact exactWitnessQ_value

example : IsGreatest pepValues ((1 : ℝ) / 14) := by
  exact threeStep_exact_value
