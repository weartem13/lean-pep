import LeanPEP

open scoped NNReal
open LeanPEP LeanPEP.GramPEP
open LeanPEP.GramPEP.RationalReconstructionAudit
open LeanPEP.Adapters.ProximalGradientReconstruction

#check checkPolicyQ_eq_true_iff
#check checkScalarQ_eq_true_iff
#check checkCoefficientsQ_eq_true_iff
#check coefficients_length
#check numericalCoefficientsQ
#check checkChangesQ_eq_true_iff
#check references_preserved
#check checkReconstructedQ_eq_true_iff
#check reconstructed_bound_check
#check reconstruction_within_policy
#check checked_certificate
#check Imported.CompositeCandidates.PGOne.raw_psd_passes
#check Imported.CompositeCandidates.PGOne.raw_rejected
#check Imported.CompositeCandidates.PGThree.raw_not_psd_real
#check Imported.CompositeCandidates.PGThree.reconstructed_check
#check Imported.CompositeCandidates.PGExact.raw_check
#check Imported.CompositeCandidates.strict_policy_rejected
#check Imported.CompositeCandidates.wrong_bound_within_policy
#check Imported.CompositeCandidates.wrong_bound_joint_rejected
#check Imported.CompositeCandidates.wrong_factors_rejected
#check Imported.CompositeCandidates.extra_zero_reference_rejected
#check Imported.CompositeCandidates.wrong_coverage_rejected
#check Imported.CompositeCandidates.raw_acceptance_not_inherited
#check ActualFunction.ProximalGradientReconstructionAudit.upper_firstOrder
#check ActualFunction.ProximalGradientReconstructionAudit.raw_upper_firstOrder
#check ActualFunction.ProximalGradientReconstructionAudit.three_step_upper

example : checkCoefficientsQ ⟨1, 0⟩ [] [] = true := by decide +kernel
example : checkCoefficientsQ ⟨1, 0⟩ [0] [] = false := by decide +kernel
example : checkScalarQ ⟨10, 1/10000⟩ (3333/10000) (1/3) = true := by decide +kernel
example : checkScalarQ ⟨2, 1⟩ (3333/10000) (1/3) = false := by decide +kernel
example : checkPolicyQ ⟨0, 0⟩ = false := by decide +kernel

example {p m : ℕ} {model : ModelQ p m} (policy : PolicyQ)
    (a b : UpperCertQ model) (h : checkChangesQ policy a b = true) :
    assumptionReferencesQ a = assumptionReferencesQ b :=
  (references_preserved policy a b h).1

example {n k : ℕ} (s : Adapters.ProximalGradientSparse.SourceQ n k)
    (policy : PolicyQ) (a b : UpperCertQ s.model)
    (h : checkReconstructedQ s policy a b = true) :
    Adapters.ProximalGradientSparse.checkBoundQ s b = true :=
  reconstructed_bound_check s policy a b h

example : checkRawQ Imported.CompositeCandidates.PGOne.sourceQ
    Imported.CompositeCandidates.PGOne.rawUpperQ = false :=
  Imported.CompositeCandidates.PGOne.raw_rejected

example : checkReconstructedQ Imported.CompositeCandidates.PGThree.sourceQ
    Imported.CompositeCandidates.PGThree.policyQ Imported.CompositeCandidates.PGThree.rawUpperQ
    Imported.CompositeCandidates.PGThree.reconstructedUpperQ = true :=
  Imported.CompositeCandidates.PGThree.reconstructed_check

example : ¬ IsGramPosSemidef (castGramQ Imported.CompositeCandidates.PGThree.rawUpperQ.dualMatrix) :=
  Imported.CompositeCandidates.PGThree.raw_not_psd_real

example : (Imported.CompositeCandidates.PGThree.reconstructedUpperQ.bound : ℝ) = 1/12 := by
  norm_num [Imported.CompositeCandidates.PGThree.reconstructedUpperQ]

example : IsGreatest
    (ActualFunction.ProximalGradientCanonical.oneDimensionalHilbertValues 7 (3 : ℝ≥0) 2) (3/8 : ℝ) := by
  convert ActualFunction.ProximalGradientCanonical.hilbert_tight_all 7
    (L := (3 : ℝ≥0)) (R := 2) (by norm_num) (by norm_num) using 1 <;> norm_num

example : IsGreatest
    (ActualFunction.ProximalGradientCanonical.oneDimensionalHilbertValues 7 (3 : ℝ≥0) 0) 0 := by
  convert ActualFunction.ProximalGradientCanonical.hilbert_tight_all 7
    (L := (3 : ℝ≥0)) (R := 0) (by norm_num) (by norm_num) using 1 <;> norm_num

#print axioms LeanPEP.GramPEP.RationalReconstructionAudit.checkCoefficientsQ_eq_true_iff
#print axioms LeanPEP.GramPEP.RationalReconstructionAudit.checkChangesQ_eq_true_iff
#print axioms LeanPEP.Adapters.ProximalGradientReconstruction.checked_certificate
#print axioms LeanPEP.Imported.CompositeCandidates.PGThree.raw_not_psd_real
#print axioms LeanPEP.Imported.CompositeCandidates.raw_acceptance_not_inherited
#print axioms LeanPEP.Imported.CompositeCandidates.wrong_bound_joint_rejected
#print axioms LeanPEP.Imported.CompositeCandidates.PGThree.reconstructed_check
#print axioms LeanPEP.ActualFunction.ProximalGradientReconstructionAudit.three_step_upper
