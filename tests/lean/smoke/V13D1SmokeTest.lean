import LeanPEP

open scoped NNReal
open LeanPEP LeanPEP.GramPEP
open LeanPEP.Imported
open LeanPEP.ActualFunction.PSDSynthesisApplications

#check checkPSDFactorQ
#check checkPSDFactorQ_sound
#check checkPSDFactorQ_sound_real
#check UpperCertQ.withDualFactor
#check UpperCertValidQ.withDualFactor
#check checkUpperCertQ_withDualFactor
#check not_isGramPosSemidef_of_negative
#check not_isGramPosSemidef_real_of_negative
#check not_isGramPosSemidef_of_asymmetry
#check PSDSynthesisRegression.gd_bundle_check
#check PSDSynthesisRegression.gd_attainment_real
#check pg_one_matrix_binding
#check pg_two_matrix_binding
#check pg_one_upper_check
#check pg_two_upper_check
#check upper_of_synthesized_dual
#check two_step_upper

example : IsGramPosSemidef (castGramQ PSDSynthesized.Empty.matrixQ) :=
  PSDSynthesized.Empty.psd_real
example : IsGramPosSemidef (castGramQ PSDSynthesized.Zero.matrixQ) :=
  PSDSynthesized.Zero.psd_real
example : IsGramPosSemidef (castGramQ PSDSynthesized.IrrationalCholesky.matrixQ) :=
  PSDSynthesized.IrrationalCholesky.psd_real
example : IsGramPosSemidef (castGramQ PSDSynthesized.SingularPermuted.matrixQ) :=
  PSDSynthesized.SingularPermuted.psd_real
example : ¬ IsGramPosSemidef (castGramQ PSDSynthesized.PositiveDiagonalIndefinite.matrixQ) :=
  PSDSynthesized.PositiveDiagonalIndefinite.not_psd_real
example : ¬ IsGramPosSemidef (castGramQ PSDSynthesized.LiftedZeroDiagonal.matrixQ) :=
  PSDSynthesized.LiftedZeroDiagonal.not_psd_real
example : ¬ IsGramPosSemidef (castGramQ PSDSynthesized.TinyNegative.matrixQ) :=
  PSDSynthesized.TinyNegative.not_psd_real
example : ¬ IsGramPosSemidef PSDSynthesized.Asymmetric.matrixQ :=
  PSDSynthesized.Asymmetric.not_psd_rational
example : PSDSynthesized.GDDual.factorQ.factors.length = 2 := by decide +kernel
example : PSDSynthesized.PGDualTwo.factorQ.factors.length = 5 := by decide +kernel
example : checkExactGramBundleQ PSDSynthesisRegression.wrongBoundBundleQ = false :=
  PSDSynthesisRegression.wrong_bound_bundle_rejected

example {p m : ℕ} {model : ModelQ p m} (c : UpperCertQ model) (d : PSDFactorCertQ m)
    (hc : checkUpperCertQ c = true) (hd : checkPSDFactorQ c.dualMatrix d = true) :
    checkUpperCertQ (c.withDualFactor d) = true :=
  checkUpperCertQ_withDualFactor c d hc hd

-- Retain a prior exact-run tightness regression; it is not an inexact rate.
example : IsGreatest
    (ActualFunction.ProximalGradientCanonical.oneDimensionalHilbertValues 7 (3 : ℝ≥0) 2)
    (3/8 : ℝ) := by
  convert ActualFunction.ProximalGradientCanonical.hilbert_tight_all 7
    (L := (3 : ℝ≥0)) (R := 2) (by norm_num) (by norm_num) using 1 <;> norm_num

#print axioms checkUpperCertQ_withDualFactor
#print axioms not_isGramPosSemidef_real_of_negative
#print axioms PSDSynthesized.IrrationalCholesky.psd_real
#print axioms PSDSynthesized.LiftedZeroDiagonal.not_psd_real
#print axioms PSDSynthesisRegression.gd_bundle_check
#print axioms PSDSynthesisRegression.gd_attainment_real
#print axioms pg_two_upper_check
#print axioms two_step_upper
