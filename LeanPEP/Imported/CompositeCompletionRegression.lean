import LeanPEP.Imported.CompositeCompletion

/-! D10 controlled simulated captures. Not PEPit solver runs. The D8 seed fails;
exact bound/weight completion keeps its objective, residual and factor payload.
All acceptance proofs call the original D9/D8 chain through the D10 guards. -/
namespace LeanPEP.Imported.CompositeCompletion
open LeanPEP.GramPEP
open LeanPEP.GramPEP.RationalLinearSystem
open LeanPEP.GramPEP.RationalReconstructionAudit
open LeanPEP.Adapters.ProximalGradientCompletion
open LeanPEP.Adapters.ProximalGradientCapture

namespace PGOne
theorem seed_rejected : checkCapturedQ sourceQ traceQ policyQ rawUpperQ reconstructedUpperQ = false := by
  decide +kernel
theorem linear_solution_check : checkSolutionQ coefficientSystemQ completionVectorQ = true := by
  decide +kernel
theorem fixed_targets_check : checkFixedTargetsQ reconstructedUpperQ completedUpperQ = true := by
  decide +kernel
theorem completed_check : checkCompletedQ sourceQ traceQ policyQ rawUpperQ reconstructedUpperQ completedUpperQ = true := by
  decide +kernel
end PGOne
namespace PGTwo
theorem seed_rejected : checkCapturedQ sourceQ traceQ policyQ rawUpperQ reconstructedUpperQ = false := by
  decide +kernel
theorem linear_solution_check : checkSolutionQ coefficientSystemQ completionVectorQ = true := by
  decide +kernel
theorem completed_check : checkCompletedQ sourceQ traceQ policyQ rawUpperQ reconstructedUpperQ completedUpperQ = true := by
  decide +kernel
end PGTwo
namespace PGThree
theorem seed_rejected : checkCapturedQ sourceQ traceQ policyQ rawUpperQ reconstructedUpperQ = false := by
  decide +kernel
theorem linear_solution_check : checkSolutionQ coefficientSystemQ completionVectorQ = true := by
  decide +kernel
theorem completed_check : checkCompletedQ sourceQ traceQ policyQ rawUpperQ reconstructedUpperQ completedUpperQ = true := by
  decide +kernel
end PGThree

namespace Inconsistent
/-- PSD is not sufficient for compatibility with the exact coefficient equations. -/
theorem seed_psd_check : checkPSDFactorQ reconstructedUpperQ.dualMatrix reconstructedUpperQ.dualFactor = true := by
  decide +kernel
theorem obstruction_check : checkObstructionQ coefficientSystemQ obstructionQ = true := by
  decide +kernel
/-- Only this supplied fixed-target linear system; not all possible residuals. -/
theorem no_linear_solution : ¬ ∃ x, IsSolutionQ coefficientSystemQ x :=
  checked_obstruction coefficientSystemQ obstructionQ obstruction_check
end Inconsistent

/-- A final certificate can pass old D9 yet violate a separately fixed seed target. -/
def changedSeedQ : UpperCertQ PGOne.sourceQ.model :=
  { PGOne.reconstructedUpperQ with
    dualMatrix := fun i j => PGOne.reconstructedUpperQ.dualMatrix i j +
      if i = 0 ∧ j = 0 then 1/10000 else 0 }
theorem changed_seed_within_policy : checkChangesQ PGOne.policyQ PGOne.rawUpperQ changedSeedQ = true := by
  decide +kernel
theorem completed_old_d9_passes : checkCapturedQ PGOne.sourceQ PGOne.traceQ PGOne.policyQ
    PGOne.rawUpperQ PGOne.completedUpperQ = true := by decide +kernel
theorem changed_seed_fixed_rejected : checkFixedTargetsQ changedSeedQ PGOne.completedUpperQ = false := by
  decide +kernel
theorem changed_seed_joint_rejected : checkCompletedQ PGOne.sourceQ PGOne.traceQ PGOne.policyQ
    PGOne.rawUpperQ changedSeedQ PGOne.completedUpperQ = false := by decide +kernel

end LeanPEP.Imported.CompositeCompletion
