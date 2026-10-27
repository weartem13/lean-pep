import LeanPEP.GramPEP.UpperCoefficientBox
import LeanPEP.Imported.CompositeBoundedCompletionRegression
import LeanPEP.Imported.CompositeCompletionRegression

/-! D12: no new numerical fixtures. Independently bind already committed D10/D11
systems to the Lean-defined original certificate family. Positive proofs keep the
old checker. Negative proofs now quantify over every bound/weight assignment for
the audited fixed targets, rather than just a detached numerical linear system. -/
namespace LeanPEP.Imported.CompiledCompletion
open LeanPEP.GramPEP
open LeanPEP.GramPEP.UpperCoefficientSystem
open LeanPEP.GramPEP.UpperCoefficientBox

namespace One
open LeanPEP.Imported.CompositeBoundedCompletion.PGOne

def familyQ := ofUpperQ reconstructedUpperQ

theorem system_binding : checkSystemQ familyQ coefficientSystemQ = true := by
  decide +kernel
theorem raw_binding : checkRawVectorQ reconstructedUpperQ rawUpperQ rawVectorQ = true := by
  decide +kernel
theorem box_binding : checkBoxQ familyQ rawVectorQ policyQ.maxAbsError boxQ = true := by
  decide +kernel
theorem fixed_psd_check : checkPSDFactorQ familyQ.residual familyQ.factors = true := by
  decide +kernel

theorem compiled_certificate_check : checkUpperCertQ (instantiateQ familyQ completionVectorQ) = true := by
  have hx := (RationalBoxSystem.checkFeasibleQ_eq_true_iff boxQ completionVectorQ).mp box_feasible_check
  have he := (checkBoxQ_eq_true_iff familyQ rawVectorQ policyQ.maxAbsError boxQ).mp box_binding
  rw [he] at hx
  exact ((feasible_iff_accepted familyQ rawVectorQ completionVectorQ policyQ.maxAbsError
    ((checkPSDFactorQ_eq_true_iff _ _).mp fixed_psd_check)).mp hx).1

/-- A perfectly checked obstruction to a MADE-UP system proves nothing about this family. -/
def forgedSystemQ : RationalLinearSystem.SystemQ 43 12 :=
  { matrix := fun _ _ => 0
    rhs := fun i => if i = 0 then 1 else 0 }
def forgedWitnessQ : Fin 43 → ℚ := fun i => if i = 0 then 1 else 0

theorem forged_local_obstruction_check :
    RationalLinearSystem.checkObstructionQ forgedSystemQ forgedWitnessQ = true := by
  decide +kernel
theorem forged_system_rejected : checkSystemQ familyQ forgedSystemQ = false := by
  decide +kernel

/-- An ordered (1,0) coefficient row is not interchangeable with (0,1). -/
def wrongGramSystemQ : RationalLinearSystem.SystemQ 43 12 :=
  { coefficientSystemQ with
    rhs := fun i => coefficientSystemQ.rhs i + if i = 13 then 1/10000 else 0 }
theorem wrong_gram_axis_rejected : checkSystemQ familyQ wrongGramSystemQ = false := by
  decide +kernel

def wrongRawVectorQ : Fin 12 → ℚ := fun j => rawVectorQ j + if j = 0 then 1/10000 else 0
theorem wrong_raw_vector_rejected :
    checkRawVectorQ reconstructedUpperQ rawUpperQ wrongRawVectorQ = false := by
  decide +kernel
end One

namespace Two
open LeanPEP.Imported.CompositeBoundedCompletion.PGTwo

def familyQ := ofUpperQ reconstructedUpperQ
theorem system_binding : checkSystemQ familyQ coefficientSystemQ = true := by
  decide +kernel
theorem raw_binding : checkRawVectorQ reconstructedUpperQ rawUpperQ rawVectorQ = true := by
  decide +kernel
theorem box_binding : checkBoxQ familyQ rawVectorQ policyQ.maxAbsError boxQ = true := by
  decide +kernel
end Two

namespace Three
open LeanPEP.Imported.CompositeBoundedCompletion.PGThree

def familyQ := ofUpperQ reconstructedUpperQ
theorem system_binding : checkSystemQ familyQ coefficientSystemQ = true := by
  decide +kernel
theorem raw_binding : checkRawVectorQ reconstructedUpperQ rawUpperQ rawVectorQ = true := by
  decide +kernel
theorem box_binding : checkBoxQ familyQ rawVectorQ policyQ.maxAbsError boxQ = true := by
  decide +kernel
theorem fixed_psd_check : checkPSDFactorQ familyQ.residual familyQ.factors = true := by
  decide +kernel
theorem compiled_certificate_check : checkUpperCertQ (instantiateQ familyQ completionVectorQ) = true := by
  have hx := (RationalBoxSystem.checkFeasibleQ_eq_true_iff boxQ completionVectorQ).mp box_feasible_check
  have he := (checkBoxQ_eq_true_iff familyQ rawVectorQ policyQ.maxAbsError boxQ).mp box_binding
  rw [he] at hx
  exact ((feasible_iff_accepted familyQ rawVectorQ completionVectorQ policyQ.maxAbsError
    ((checkPSDFactorQ_eq_true_iff _ _).mp fixed_psd_check)).mp hx).1
end Three

namespace Inconsistent
open LeanPEP.Imported.CompositeCompletion.Inconsistent

def familyQ := ofUpperQ reconstructedUpperQ
theorem system_binding : checkSystemQ familyQ coefficientSystemQ = true := by
  decide +kernel
/-- Now about the original fixed objective/residual/references, not a detached system. -/
theorem no_fixed_identity : ¬ ∃ x,
    certificateRhsExprQ (instantiateQ familyQ x) = upperTargetExprQ (x 0) familyQ.objective :=
  checked_no_identity familyQ coefficientSystemQ system_binding obstructionQ obstruction_check

theorem no_fixed_certificate : ¬ ∃ x, checkUpperCertQ (instantiateQ familyQ x) = true :=
  checked_no_accepted familyQ coefficientSystemQ system_binding obstructionQ obstruction_check
end Inconsistent

namespace Budget
open LeanPEP.Imported.CompositeBoundedCompletion.Budget

def familyQ := ofUpperQ reconstructedUpperQ
theorem system_binding : checkSystemQ familyQ coefficientSystemQ = true := by
  decide +kernel
theorem raw_binding : checkRawVectorQ reconstructedUpperQ rawUpperQ rawVectorQ = true := by
  decide +kernel
theorem box_binding : checkBoxQ familyQ rawVectorQ policyQ.maxAbsError boxQ = true := by
  decide +kernel

/-- No bound/multiplier vector in the original raw budget at these fixed targets.
No claim about a different residual, a different budget, or general PEP infeasibility. -/
theorem no_fixed_certificate_in_budget : ¬ ∃ x,
    checkUpperCertQ (instantiateQ familyQ x) = true ∧ WithinBudgetQ rawVectorQ x policyQ.maxAbsError :=
  checked_no_accepted_in_budget familyQ rawVectorQ policyQ.maxAbsError boxQ box_binding
    boxObstructionQ box_obstruction_check

theorem no_nonnegative_identity_in_budget : ¬ ∃ x,
    certificateRhsExprQ (instantiateQ familyQ x) = upperTargetExprQ (x 0) familyQ.objective ∧
    (∀ j : Fin 10, 0 ≤ x j.succ) ∧ WithinBudgetQ rawVectorQ x policyQ.maxAbsError :=
  checked_no_identity_in_budget familyQ rawVectorQ policyQ.maxAbsError boxQ box_binding
    boxObstructionQ box_obstruction_check

def changedBoxQ : RationalBoxSystem.BoxQ 43 11 :=
  { boxQ with lower := fun j => boxQ.lower j + if j = 0 then 1/10000 else 0 }
theorem changed_box_rejected : checkBoxQ familyQ rawVectorQ policyQ.maxAbsError changedBoxQ = false := by
  decide +kernel
end Budget

/-- Zero values, zero Gram dimensions, no references: the constant row remains. -/
def emptyModelQ : ModelQ 0 0 :=
  { position := fun i => Fin.elim0 i
    gradient := fun i => Fin.elim0 i
    assumptions := [] }
def emptyFamilyQ : FamilyQ emptyModelQ 0 :=
  { objective := LinearExprQ.const 0 0 (-2)
    residual := fun i => Fin.elim0 i
    factors := { factors := [] }
    references := fun i => Fin.elim0 i }
theorem empty_system_check : RationalLinearSystem.checkSolutionQ (compileQ emptyFamilyQ) ![-2] = true := by
  decide +kernel
theorem negative_bound_accepted : checkUpperCertQ (instantiateQ emptyFamilyQ ![-2]) = true := by
  decide +kernel

end LeanPEP.Imported.CompiledCompletion
