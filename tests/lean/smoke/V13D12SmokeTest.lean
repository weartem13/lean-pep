import LeanPEP

open LeanPEP LeanPEP.GramPEP
open LeanPEP.GramPEP.UpperCoefficientSystem
open LeanPEP.GramPEP.UpperCoefficientBox
open scoped BigOperators NNReal

#check coefficient_ext_iff
#check coefficient_assumptions
#check compile_row
#check identity_iff_solution
#check accepted_iff
#check checkSystemQ_eq_true_iff
#check checked_no_identity
#check checked_no_accepted
#check feasible_iff
#check feasible_iff_accepted
#check checkBoxQ_eq_true_iff
#check checked_no_identity_in_budget
#check checked_no_accepted_in_budget
#check checkRawVectorQ_eq_true_iff
#check Imported.CompiledCompletion.One.system_binding
#check Imported.CompiledCompletion.Three.compiled_certificate_check
#check Imported.CompiledCompletion.Inconsistent.no_fixed_identity
#check Imported.CompiledCompletion.Budget.no_fixed_certificate_in_budget
#check Imported.CompiledCompletion.One.forged_local_obstruction_check
#check Imported.CompiledCompletion.One.forged_system_rejected
#check Imported.CompiledCompletion.Budget.changed_box_rejected

example {p m q : ℕ} {model : ModelQ p m} (f : FamilyQ model q) (x : Fin (q + 1) → ℚ)
    (hx : RationalLinearSystem.IsSolutionQ (compileQ f) x) :
    certificateRhsExprQ (instantiateQ f x) = upperTargetExprQ (x 0) f.objective :=
  (identity_iff_solution f x).mpr hx

example {p m q : ℕ} {model : ModelQ p m} (f : FamilyQ model q) (raw x : Fin (q + 1) → ℚ)
    (eta : ℚ) (hp : PSDFactorValidQ f.residual f.factors)
    (hx : RationalBoxSystem.FeasibleQ (compileBoxQ f raw eta) x) :
    checkUpperCertQ (instantiateQ f x) = true :=
  ((feasible_iff_accepted f raw x eta hp).mp hx).1

example : checkUpperCertQ (instantiateQ Imported.CompiledCompletion.emptyFamilyQ ![-2]) = true :=
  Imported.CompiledCompletion.negative_bound_accepted

example : ¬ ∃ x,
    checkUpperCertQ (instantiateQ Imported.CompiledCompletion.Inconsistent.familyQ x) = true :=
  Imported.CompiledCompletion.Inconsistent.no_fixed_certificate

example : checkSystemQ Imported.CompiledCompletion.One.familyQ
    Imported.CompiledCompletion.One.forgedSystemQ = false :=
  Imported.CompiledCompletion.One.forged_system_rejected

example : checkSystemQ Imported.CompiledCompletion.One.familyQ
    Imported.CompiledCompletion.One.wrongGramSystemQ = false :=
  Imported.CompiledCompletion.One.wrong_gram_axis_rejected

example : checkBoxQ Imported.CompiledCompletion.Budget.familyQ
    Imported.CompositeBoundedCompletion.Budget.rawVectorQ
    Imported.CompositeBoundedCompletion.Budget.policyQ.maxAbsError
    Imported.CompiledCompletion.Budget.changedBoxQ = false :=
  Imported.CompiledCompletion.Budget.changed_box_rejected

-- Preserve the existing actual-function interface; this release does not change rates.
#check ActualFunction.ProximalGradientBoundedCompletionAudit.three_step_upper

#print axioms coefficient_ext_iff
#print axioms identity_iff_solution
#print axioms accepted_iff
#print axioms checked_no_accepted
#print axioms checked_no_accepted_in_budget
#print axioms Imported.CompiledCompletion.Three.compiled_certificate_check
#print axioms Imported.CompiledCompletion.Inconsistent.no_fixed_certificate
#print axioms Imported.CompiledCompletion.Budget.no_fixed_certificate_in_budget
