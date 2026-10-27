import LeanPEP

open scoped NNReal
open LeanPEP LeanPEP.GramPEP
open LeanPEP.Adapters.ProximalGradientSource
open LeanPEP.Imported.CompositeSource

#check LeanPEP.Adapters.ExactFormulation.checkListQ_eq_true_iff
#check UpperCertQ.rebind
#check checkUpperCertQ_rebind
#check HeaderQ
#check SourceQ
#check expectedSource_model
#check checkSampleQ_eq_true_iff
#check auditSourceQ
#check checkSourceQ_eq_true_iff
#check source_model_eq
#check source_objective_eq
#check checkBoundQ_eq_true_iff
#check checked_certificate
#check PGOne.bound_check
#check PGTwo.bound_check
#check PGThree.bound_check
#check forged_local_certificate_accepted
#check forged_bound_rejected
#check ActualFunction.ProximalGradientSourceAudit.finite_upper
#check ActualFunction.ProximalGradientSourceAudit.upper_firstOrder
#check ActualFunction.ProximalGradientSourceAudit.upper_analytic
#check ActualFunction.ProximalGradientSourceAudit.three_step_upper

example (n : ℕ) : checkSourceQ (expectedSourceQ n) = true := expectedSource_check n
example (n : ℕ) : (expectedSourceQ n).model = Profiles.ProximalGradient.modelQ n :=
  expectedSource_model n
example : checkBoundQ PGOne.sourceQ PGOne.upperQ = true := PGOne.bound_check
example : checkBoundQ PGTwo.sourceQ PGTwo.upperQ = true := PGTwo.bound_check
example : checkBoundQ PGThree.sourceQ PGThree.upperQ = true := PGThree.bound_check
example : checkUpperCertQ forgedUpperQ = true ∧ checkBoundQ forgedSourceQ forgedUpperQ = false :=
  ⟨forged_local_certificate_accepted, forged_bound_rejected⟩
example : checkUpperCertQ wrongObjectiveQ = true ∧ checkBoundQ PGOne.sourceQ wrongObjectiveQ = false :=
  ⟨wrong_objective_local_accepted, wrong_objective_bound_rejected⟩
example : checkUpperCertQ implicitTermQ = true ∧ checkBoundQ PGOne.sourceQ implicitTermQ = false :=
  ⟨implicit_term_local_accepted, implicit_term_bound_rejected⟩
example : checkSourceQ missingConstraintQ = false := missing_constraint_rejected
example : checkSourceQ reversedSenseQ = false := reversed_sense_rejected
example : checkSourceQ swappedTagsQ = false := reordered_tags_rejected
example : (PGThree.upperQ.bound : ℝ) = 1/12 := by norm_num [PGThree.upperQ]

example {n : ℕ} (s : SourceQ n) (c : UpperCertQ s.model)
    (hc : checkBoundQ s c = true) :
    ∃ d : UpperCertQ (Profiles.ProximalGradient.modelQ n),
      checkUpperCertQ d = true ∧ d.interpTerms = [] ∧
      d.objective = Profiles.ProximalGradient.objectiveQ n ∧ d.bound = c.bound :=
  checked_certificate s c hc

example : IsGreatest
    (ActualFunction.ProximalGradientScaling.oneDimensionalAnalyticValues 7 (3 : ℝ≥0) 2)
    (3/8 : ℝ) := by
  have h := ActualFunction.ProximalGradientWitnessScaling.analytic_tight_all 7
    (L := (3 : ℝ≥0)) (R := 2) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

#print axioms LeanPEP.Adapters.ExactFormulation.checkListQ_eq_true_iff
#print axioms checkSourceQ_eq_true_iff
#print axioms checked_certificate
#print axioms PGThree.source_check
#print axioms PGThree.upper_check
#print axioms forged_bound_rejected
#print axioms ActualFunction.ProximalGradientSourceAudit.upper_firstOrder
#print axioms ActualFunction.ProximalGradientSourceAudit.three_step_upper
