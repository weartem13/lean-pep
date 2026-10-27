import LeanPEP.Profiles

open LeanPEP
open LeanPEP.Toy.FiniteGD
open LeanPEP.Toy.FiniteGD.ParametricUpper

#check LeanPEP.Profiles.FixedStepFirstOrder.ProfileQ
#check LeanPEP.Profiles.FixedStepFirstOrder.ProfileQ.causal
#check LeanPEP.Profiles.FixedStepFirstOrder.gradientCombinationAffineQ
#check LeanPEP.Profiles.FixedStepFirstOrder.iterateAffineQ
#check LeanPEP.Profiles.FixedStepFirstOrder.iterateAffineQ_gradCoeff_of_le
#check LeanPEP.Profiles.FixedStepFirstOrder.interpolationPolyQ
#check LeanPEP.Profiles.FixedStepFirstOrder.evalR_interpolationPolyQ
#check LeanPEP.Profiles.FixedStepFirstOrder.checkUpperCertQ_eq_true_iff
#check LeanPEP.Profiles.FixedStepFirstOrder.checkUpperCertQ_sound_real

#check LeanPEP.Profiles.GradientDescent.unitGDProfileQ
#check LeanPEP.Profiles.GradientDescent.unitStepCoeffQ_causal
#check LeanPEP.Profiles.GradientDescent.gradientCombinationAffineQ_unitGD
#check LeanPEP.Profiles.GradientDescent.iterateAffineQ_unitGD
#check LeanPEP.Profiles.GradientDescent.pointAffineQ_unitGD
#check LeanPEP.Profiles.GradientDescent.interpolationPolyQ_unitGD
#check LeanPEP.Profiles.GradientDescent.interpolationSlackR_unitGD
#check LeanPEP.Profiles.GradientDescent.feasibleR_unitGD_iff
#check LeanPEP.Profiles.GradientDescent.certificateRhsPolyQ_unitGD
#check LeanPEP.Profiles.GradientDescent.checkUpperCertQ_unitGD
#check LeanPEP.Profiles.GradientDescent.gdUpperCertQ_profile_check_all
#check LeanPEP.Profiles.GradientDescent.gd_profile_upper_all
#check LeanPEP.Profiles.GradientDescent.gd_profile_upper_all_of_legacy_feasible

example :
    LeanPEP.Profiles.FixedStepFirstOrder.checkUpperCertQ
      (LeanPEP.Profiles.GradientDescent.unitGDProfileQ 0)
      (gdUpperCertQ 0) = true := by
  exact LeanPEP.Profiles.GradientDescent.gdUpperCertQ_profile_check_all 0

example :
    LeanPEP.Profiles.FixedStepFirstOrder.checkUpperCertQ
      (LeanPEP.Profiles.GradientDescent.unitGDProfileQ 4)
      (gdUpperCertQ 4) = true := by
  exact LeanPEP.Profiles.GradientDescent.gdUpperCertQ_profile_check_all 4

example :
    LeanPEP.Profiles.FixedStepFirstOrder.checkUpperCertQ
      (LeanPEP.Profiles.GradientDescent.unitGDProfileQ 8)
      (gdUpperCertQ 8) = true := by
  exact LeanPEP.Profiles.GradientDescent.gdUpperCertQ_profile_check_all 8
