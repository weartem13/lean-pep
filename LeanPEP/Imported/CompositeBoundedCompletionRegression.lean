import LeanPEP.Imported.CompositeBoundedCompletion

/-! D11 simulations, not live solver output. Positive cases retain a permitted
zero self-pair and its negative seed multiplier, which affine equations cannot
remove. The new search changes that free variable, without clipping input data.
All final PEP certificates use the UNCHANGED D10 checker. -/
namespace LeanPEP.Imported.CompositeBoundedCompletion
open LeanPEP.GramPEP
open LeanPEP.Adapters.ProximalGradientCompletion

namespace PGOne
theorem completion_vector_check : List.ofFn completionVectorQ =
    completedUpperQ.bound :: completedUpperQ.assumptionTerms.map (fun t => t.weight) := by
  decide +kernel
theorem raw_vector_check : List.ofFn rawVectorQ =
    rawUpperQ.bound :: rawUpperQ.assumptionTerms.map (fun t => t.weight) := by
  decide +kernel
theorem box_bounds_check :
    boxQ.lower = RationalBoxSystem.policyLowerQ rawVectorQ policyQ.maxAbsError signMaskQ ∧
    boxQ.upper = RationalBoxSystem.policyUpperQ rawVectorQ policyQ.maxAbsError := by
  decide +kernel
theorem free_seed_linear_check :
    RationalLinearSystem.checkSolutionQ coefficientSystemQ freeSeedVectorQ = true := by
  decide +kernel
theorem free_seed_rejected :
    checkCompletedQ sourceQ traceQ policyQ rawUpperQ reconstructedUpperQ freeSeedUpperQ = false := by
  decide +kernel
theorem zero_row_retained : sourceQ.rows 10 = LinearExprQ.zero 6 6 := by
  apply checkLinearExprEqQ_sound (sourceQ.rows 10) (LinearExprQ.zero 6 6)
  decide +kernel
theorem negative_free_seed : freeSeedVectorQ 11 < 0 := by decide +kernel
theorem free_variable_repaired : completionVectorQ 11 = 0 := by decide +kernel
theorem box_feasible_check : RationalBoxSystem.checkFeasibleQ boxQ completionVectorQ = true := by
  decide +kernel
theorem fixed_targets_check : checkFixedTargetsQ reconstructedUpperQ completedUpperQ = true := by
  decide +kernel
theorem completed_check :
    checkCompletedQ sourceQ traceQ policyQ rawUpperQ reconstructedUpperQ completedUpperQ = true := by
  decide +kernel
end PGOne

namespace PGTwo
theorem completion_vector_check : List.ofFn completionVectorQ =
    completedUpperQ.bound :: completedUpperQ.assumptionTerms.map (fun t => t.weight) := by
  decide +kernel
theorem raw_vector_check : List.ofFn rawVectorQ =
    rawUpperQ.bound :: rawUpperQ.assumptionTerms.map (fun t => t.weight) := by
  decide +kernel
theorem box_bounds_check :
    boxQ.lower = RationalBoxSystem.policyLowerQ rawVectorQ policyQ.maxAbsError signMaskQ ∧
    boxQ.upper = RationalBoxSystem.policyUpperQ rawVectorQ policyQ.maxAbsError := by
  decide +kernel
theorem free_seed_rejected :
    checkCompletedQ sourceQ traceQ policyQ rawUpperQ reconstructedUpperQ freeSeedUpperQ = false := by
  decide +kernel
theorem box_feasible_check : RationalBoxSystem.checkFeasibleQ boxQ completionVectorQ = true := by
  decide +kernel
theorem completed_check :
    checkCompletedQ sourceQ traceQ policyQ rawUpperQ reconstructedUpperQ completedUpperQ = true := by
  decide +kernel
end PGTwo

namespace PGThree
theorem completion_vector_check : List.ofFn completionVectorQ =
    completedUpperQ.bound :: completedUpperQ.assumptionTerms.map (fun t => t.weight) := by
  decide +kernel
theorem raw_vector_check : List.ofFn rawVectorQ =
    rawUpperQ.bound :: rawUpperQ.assumptionTerms.map (fun t => t.weight) := by
  decide +kernel
theorem box_bounds_check :
    boxQ.lower = RationalBoxSystem.policyLowerQ rawVectorQ policyQ.maxAbsError signMaskQ ∧
    boxQ.upper = RationalBoxSystem.policyUpperQ rawVectorQ policyQ.maxAbsError := by
  decide +kernel
theorem free_seed_rejected :
    checkCompletedQ sourceQ traceQ policyQ rawUpperQ reconstructedUpperQ freeSeedUpperQ = false := by
  decide +kernel
theorem box_feasible_check : RationalBoxSystem.checkFeasibleQ boxQ completionVectorQ = true := by
  decide +kernel
theorem completed_check :
    checkCompletedQ sourceQ traceQ policyQ rawUpperQ reconstructedUpperQ completedUpperQ = true := by
  decide +kernel
end PGThree

namespace Budget
theorem raw_vector_check : List.ofFn rawVectorQ =
    rawUpperQ.bound :: rawUpperQ.assumptionTerms.map (fun t => t.weight) := by
  decide +kernel
theorem box_bounds_check :
    boxQ.lower = RationalBoxSystem.policyLowerQ rawVectorQ policyQ.maxAbsError signMaskQ ∧
    boxQ.upper = RationalBoxSystem.policyUpperQ rawVectorQ policyQ.maxAbsError := by
  decide +kernel
theorem affine_solution_check :
    RationalLinearSystem.checkSolutionQ coefficientSystemQ freeSeedVectorQ = true := by
  decide +kernel
theorem affine_certificate_valid : checkUpperCertQ freeSeedUpperQ = true := by
  decide +kernel
theorem free_seed_policy_rejected :
    checkCompletedQ sourceQ traceQ policyQ rawUpperQ reconstructedUpperQ freeSeedUpperQ = false := by
  decide +kernel
theorem box_obstruction_check : RationalBoxSystem.checkObstructionQ boxQ boxObstructionQ = true := by
  decide +kernel
theorem obstruction_margin : RationalBoxSystem.marginQ boxQ boxObstructionQ = -21/10000 := by
  decide +kernel
/-- Only the submitted system and box, not a different residual or error budget. -/
theorem no_box_solution : ¬ ∃ x, RationalBoxSystem.FeasibleQ boxQ x :=
  RationalBoxSystem.checked_obstruction boxQ boxObstructionQ box_obstruction_check
end Budget

/-- A genuinely coupled two-variable example: both entries must be repaired. -/
def coupledQ : RationalBoxSystem.BoxQ 1 2 :=
  { system := { matrix := ![![1, 1]], rhs := ![1] }
    lower := ![0, 0]
    upper := ![1, 1] }
theorem coupled_old_solution : RationalLinearSystem.checkSolutionQ coupledQ.system ![2,-1] = true := by
  decide +kernel
theorem coupled_old_not_feasible : RationalBoxSystem.checkFeasibleQ coupledQ ![2,-1] = false := by
  decide +kernel
theorem coupled_repaired : RationalBoxSystem.checkFeasibleQ coupledQ ![1,0] = true := by
  decide +kernel

def impossibleQ : RationalBoxSystem.BoxQ 1 2 :=
  { system := { matrix := ![![1, 1]], rhs := ![3] }
    lower := ![0, 0]
    upper := ![1, 1] }
def impossibleWitnessQ : RationalBoxSystem.ObstructionQ 1 2 :=
  { equality := ![-1]
    lower := ![0, 0]
    upper := ![1, 1] }
theorem impossible_check : RationalBoxSystem.checkObstructionQ impossibleQ impossibleWitnessQ = true := by
  decide +kernel
theorem impossible_no_solution : ¬ ∃ x, RationalBoxSystem.FeasibleQ impossibleQ x :=
  RationalBoxSystem.checked_obstruction impossibleQ impossibleWitnessQ impossible_check

/-- Being feasible in a rational box does NOT establish bounded denominator. -/
theorem feasible_third : RationalBoxSystem.checkFeasibleQ
    { system := { matrix := ![![3]], rhs := ![1] }
      lower := ![0]
      upper := ![1] } ![1/3] = true := by
  decide +kernel
theorem third_denominator_rejected : RationalReconstructionAudit.checkScalarQ
    { maxDenominator := 2, maxAbsError := 1 } 0 (1/3) = false := by
  decide +kernel

end LeanPEP.Imported.CompositeBoundedCompletion
