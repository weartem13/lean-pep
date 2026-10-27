import LeanPEP.Profiles

open LeanPEP
open LeanPEP.Toy.FiniteGD
open LeanPEP.GramPEP

#check LeanPEP.Profiles.GramCompilation.pointAtIndex
#check LeanPEP.Profiles.GramCompilation.pointIndex
#check LeanPEP.Profiles.GramCompilation.pointAtIndex_pointIndex
#check LeanPEP.Profiles.GramCompilation.pointIndex_pointAtIndex
#check LeanPEP.Profiles.GramCompilation.pointIndex_injective
#check LeanPEP.Profiles.GramCompilation.pointIndex_surjective
#check LeanPEP.Profiles.GramCompilation.initialBasisIndex
#check LeanPEP.Profiles.GramCompilation.gradientBasisIndex
#check LeanPEP.Profiles.GramCompilation.affineVecQ
#check LeanPEP.Profiles.GramCompilation.affineVecQ_initial
#check LeanPEP.Profiles.GramCompilation.affineVecQ_gradient
#check LeanPEP.Profiles.GramCompilation.NormalizationProfileQ
#check LeanPEP.Profiles.GramCompilation.unitRadiusNormalizationQ
#check LeanPEP.Profiles.GramCompilation.initialRadiusExprQ
#check LeanPEP.Profiles.GramCompilation.ObjectiveProfileQ
#check LeanPEP.Profiles.GramCompilation.finalGapObjectiveProfileQ
#check LeanPEP.Profiles.GramCompilation.PEPProfileQ
#check LeanPEP.Profiles.GramCompilation.compileModelQ
#check LeanPEP.Profiles.GramCompilation.compileObjectiveQ
#check LeanPEP.Profiles.GramCompilation.compileModelQ_position_pointIndex
#check LeanPEP.Profiles.GramCompilation.compileModelQ_gradient_pointIndex
#check LeanPEP.Profiles.GramCompilation.compileModelQ_iter_initial_coordinate
#check LeanPEP.Profiles.GramCompilation.compileModelQ_iter_gradient_coordinate_of_le
#check LeanPEP.Profiles.GramCompilation.objectiveExprQ_evalR
#check LeanPEP.Profiles.GramCompilation.initialRadiusExprQ_evalR

#check LeanPEP.Profiles.GradientDescentGram.unitGDGramProfileQ
#check LeanPEP.Profiles.GradientDescentGram.unitGDModelQ
#check LeanPEP.Profiles.GradientDescentGram.unitGDObjectiveQ
#check LeanPEP.Profiles.GradientDescentGram.unitGDModelQ_position_pointIndex
#check LeanPEP.Profiles.GradientDescentGram.unitGDModelQ_gradient_pointIndex
#check LeanPEP.Profiles.GradientDescentGram.unitGDModelQ_iter_gradient_coordinate
#check LeanPEP.Profiles.GradientDescentGram.unitGDModelQ_iter_gradient_coordinate_of_le
#check LeanPEP.Profiles.GradientDescentGram.unitGDObjectiveQ_evalR
#check LeanPEP.Profiles.GradientDescentGram.unitGDModelQ_one_vectors
#check LeanPEP.Profiles.GradientDescentGram.unitGDModelQ_one_assumptions
#check LeanPEP.Profiles.GradientDescentGram.unitGDModelQ_one_eq
#check LeanPEP.Profiles.GradientDescentGram.unitGDObjectiveQ_one_eq
#check LeanPEP.Profiles.GradientDescentGram.unitGDInterpolationExprQ_one
#check LeanPEP.Profiles.GradientDescentGram.unitGD_oneStep_exact_certificate
#check LeanPEP.Profiles.GradientDescentGram.unitGD_oneStep_upper

example :
    LeanPEP.Profiles.GradientDescentGram.unitGDModelQ 1 =
      LeanPEP.GramPEP.UpperCertificateExamples.oneStepModelQ := by
  exact LeanPEP.Profiles.GradientDescentGram.unitGDModelQ_one_eq

example :
    LeanPEP.Profiles.GradientDescentGram.unitGDObjectiveQ 1 =
      LeanPEP.GramPEP.UpperCertificateExamples.oneStepObjectiveQ := by
  exact LeanPEP.Profiles.GradientDescentGram.unitGDObjectiveQ_one_eq

example :
    ∃ c : LeanPEP.GramPEP.UpperCertQ
        (LeanPEP.Profiles.GradientDescentGram.unitGDModelQ 1),
      c.bound = (1 : ℚ) / 6 ∧
      c.objective =
        LeanPEP.Profiles.GradientDescentGram.unitGDObjectiveQ 1 ∧
      LeanPEP.GramPEP.checkUpperCertQ c = true := by
  exact LeanPEP.Profiles.GradientDescentGram.unitGD_oneStep_exact_certificate
