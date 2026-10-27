import LeanPEP

open scoped NNReal BigOperators
open LeanPEP LeanPEP.GramPEP LeanPEP.GramPEP.OriginCoordinates
open LeanPEP.Adapters.ProximalGradientCoordinates
open LeanPEP.Imported.CompositeCoordinates

#check restrict_liftVecQ
#check restrict_liftPositionQ
#check restrict_liftExprQ
#check restrict_liftSampleQ
#check liftVecQ_eq_center_combination
#check restrictVec_eq_section_combination
#check liftGramQ_eq_congruence
#check restrictGram_eq_congruence
#check center_section_entry
#check section_center_origin
#check restrict_factorGram
#check evalR_restrictExprQ
#check zeroOriginGramR_psd
#check checkRectQ_eq_true_iff
#check auditSourceQ
#check checkSourceQ_eq_true_iff
#check checkSourceQ_sound
#check centered_expectedSourceQ
#check expectedSource_check
#check checkSourceQ_eq_expected
#check centeredUpper_bound
#check checkBoundQ_eq_true_iff
#check checked_certificate
#check PGOne.bound_check
#check PGTwo.bound_check
#check PGThree.bound_check
#check hidden_origin_centered_passes
#check hidden_origin_native_rejected
#check wrong_native_dual_centered_passes
#check wrong_native_dual_joint_rejected
#check ActualFunction.ProximalGradientCoordinateAudit.finite_upper
#check ActualFunction.ProximalGradientCoordinateAudit.upper_firstOrder
#check ActualFunction.ProximalGradientCoordinateAudit.upper_analytic
#check ActualFunction.ProximalGradientCoordinateAudit.three_step_upper

example (n : ℕ) : checkSourceQ (expectedSourceQ n) = true := expectedSource_check n

example {p m : ℕ} (a : Fin m) (e : LinearExprQ p m) :
    restrictExprQ (liftExprQ a e) = e := restrict_liftExprQ a e
example {m : ℕ} (a : Fin m) (i j : Fin m) :
    (∑ k, centerMapQ a i k * sectionMapQ m k j) = if i = j then 1 else 0 :=
  center_section_entry a i j
example {p m : ℕ} (e : LinearExprQ p (m+1)) (d : DataR (Fin p) m) :
    (restrictExprQ e).evalR d = e.evalR (zeroOriginDataR d) := evalR_restrictExprQ e d
example {m : ℕ} (G : Gram m ℝ) (hG : IsGramPosSemidef G) :
    IsGramPosSemidef (zeroOriginGramR G) := zeroOriginGramR_psd G hG
example : checkBoundQ PGOne.sourceQ PGOne.upperQ = true := PGOne.bound_check
example : checkBoundQ PGTwo.sourceQ PGTwo.upperQ = true := PGTwo.bound_check
example : checkBoundQ PGThree.sourceQ PGThree.upperQ = true := PGThree.bound_check
example : Adapters.ProximalGradientSource.checkSourceQ (centeredSourceQ hiddenOriginQ) = true ∧
    checkSourceQ hiddenOriginQ = false := ⟨hidden_origin_centered_passes, hidden_origin_native_rejected⟩
example : Adapters.ProximalGradientSource.checkSourceQ (centeredSourceQ wrongPointOriginQ) = true ∧
    checkSourceQ wrongPointOriginQ = false := ⟨wrong_point_centered_passes, wrong_point_native_rejected⟩
example : checkSourceQ wrongCenterQ = false := wrong_center_rejected
example : checkSourceQ wrongSectionQ = false := wrong_section_rejected
example : checkUpperCertQ wrongNativeDualQ = false := wrong_native_dual_local_rejected
example : checkUpperCertQ implicitQ = true ∧ checkBoundQ PGOne.sourceQ implicitQ = false :=
  ⟨implicit_local_passes, implicit_joint_rejected⟩
example {n : ℕ} (s : SourceQ n) (hs : checkSourceQ s = true) : s = expectedSourceQ n :=
  checkSourceQ_sound s hs
example {n : ℕ} (s : SourceQ n) (c : UpperCertQ s.model) (hc : checkBoundQ s c = true) :
    ∃ d : UpperCertQ (Profiles.ProximalGradient.modelQ n), checkUpperCertQ d = true ∧
      d.interpTerms = [] ∧ d.objective = Profiles.ProximalGradient.objectiveQ n ∧ d.bound = c.bound :=
  checked_certificate s c hc
example : IsGreatest
    (ActualFunction.ProximalGradientScaling.oneDimensionalAnalyticValues 7 (3 : ℝ≥0) 2)
    (3/8 : ℝ) := by
  have h := ActualFunction.ProximalGradientWitnessScaling.analytic_tight_all 7
    (L := (3 : ℝ≥0)) (R := 2) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

#print axioms liftGramQ_eq_congruence
#print axioms evalR_restrictExprQ
#print axioms zeroOriginGramR_psd
#print axioms checkSourceQ_eq_expected
#print axioms checked_certificate
#print axioms hidden_origin_native_rejected
#print axioms PGThree.bound_check
#print axioms ActualFunction.ProximalGradientCoordinateAudit.three_step_upper
