import LeanPEP

open LeanPEP
open LeanPEP.GramPEP
open LeanPEP.GramPEP.FiniteGDRegression

#check VecExpr
#check Gram
#check gramInner
#check gramNormSq
#check IsGramPosSemidef
#check interpolationSlack
#check InterpolationFeasible
#check CoreFeasible
#check interpolationSlack_ofFiniteGD
#check interpolationFeasible_ofFiniteGD_iff
#check coreFeasible_ofFiniteGD_iff
#check oneStepWitness_coreFeasible
#check twoStepWitness_coreFeasible
#check threeStepWitness_coreFeasible
#check twoStepBadCandidate_notInterpolationFeasible

example : IsGramPosSemidef (unitGram (𝕜 := ℚ)) := by
  exact unitGram_posSemidef

example :
    gramInner (unitGram (𝕜 := ℚ))
      (scalarExpr (2 : ℚ)) (scalarExpr (3 : ℚ)) = 6 := by
  rw [gramInner_unitGram]
  norm_num [scalarExpr]

example : CoreFeasible (ofFiniteGD oneStepWitnessQ) := by
  exact oneStepWitness_coreFeasible

example : CoreFeasible
    (ofFiniteGD LeanPEP.Toy.ThreeStep.exactWitnessQ) := by
  exact threeStepWitness_coreFeasible

example : ¬ InterpolationFeasible
    (ofFiniteGD LeanPEP.Toy.TwoStep.badCandidateQ) := by
  exact twoStepBadCandidate_notInterpolationFeasible
