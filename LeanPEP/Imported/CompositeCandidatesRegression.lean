import LeanPEP.Imported.CompositeCandidates
import LeanPEP.GramPEP.FactorReplacement

/-! D8 independent kernel checks on submitted numerical data. These examples
were created by decimal truncation for regression, NOT by live PEPit solves.
Raw failure never follows merely from a failed Python synthesis; it is checked.
-/
namespace LeanPEP.Imported.CompositeCandidates
open LeanPEP.GramPEP LeanPEP.GramPEP.RationalReconstructionAudit
open LeanPEP.Adapters.ProximalGradientReconstruction

namespace PGOne
theorem source_check : Adapters.ProximalGradientSparse.checkSourceQ sourceQ = true := by decide +kernel
theorem raw_psd_passes : checkPSDFactorQ rawUpperQ.dualMatrix rawUpperQ.dualFactor = true := by decide +kernel
theorem raw_rejected : checkRawQ sourceQ rawUpperQ = false := by decide +kernel
theorem changes_check : checkChangesQ policyQ rawUpperQ reconstructedUpperQ = true := by decide +kernel
theorem reconstructed_check : checkReconstructedQ sourceQ policyQ rawUpperQ reconstructedUpperQ = true := by decide +kernel
end PGOne

namespace PGTwo
theorem raw_psd_passes : checkPSDFactorQ rawUpperQ.dualMatrix rawUpperQ.dualFactor = true := by decide +kernel
theorem raw_rejected : checkRawQ sourceQ rawUpperQ = false := by decide +kernel
theorem changes_check : checkChangesQ policyQ rawUpperQ reconstructedUpperQ = true := by decide +kernel
theorem reconstructed_check : checkReconstructedQ sourceQ policyQ rawUpperQ reconstructedUpperQ = true := by decide +kernel
end PGTwo

namespace PGThree
theorem raw_negative_value : gramNormSq rawUpperQ.dualMatrix rawNegativeVecQ = -1/83333333325 := by decide +kernel
theorem raw_not_psd_real : ¬ IsGramPosSemidef (castGramQ rawUpperQ.dualMatrix) := by
  apply not_isGramPosSemidef_real_of_negative rawUpperQ.dualMatrix rawNegativeVecQ
  rw [raw_negative_value]
  norm_num
theorem raw_rejected : checkRawQ sourceQ rawUpperQ = false := by decide +kernel
theorem changes_check : checkChangesQ policyQ rawUpperQ reconstructedUpperQ = true := by decide +kernel
theorem reconstructed_check : checkReconstructedQ sourceQ policyQ rawUpperQ reconstructedUpperQ = true := by decide +kernel
end PGThree

namespace PGExact
theorem raw_check : checkRawQ sourceQ rawUpperQ = true := by decide +kernel
theorem reconstructed_check : checkReconstructedQ sourceQ policyQ rawUpperQ reconstructedUpperQ = true := by decide +kernel
end PGExact

/-- Valid reconstructed mathematics does not by itself satisfy a zero-change policy. -/
def strictPolicyQ : PolicyQ := { maxDenominator := 1000, maxAbsError := 0 }
theorem strict_policy_rejected :
    checkReconstructedQ PGOne.sourceQ strictPolicyQ PGOne.rawUpperQ PGOne.reconstructedUpperQ = false := by
  decide +kernel

/-- Exact budget compliance alone is not exact certificate feasibility. -/
def loosePolicyQ : PolicyQ :=
  { maxDenominator := 1000000000000, maxAbsError := 1/10000000000 }
def wrongBoundQ : UpperCertQ PGOne.sourceQ.model :=
  { PGOne.reconstructedUpperQ with bound := PGOne.reconstructedUpperQ.bound + 1/1000000000000 }
theorem wrong_bound_within_policy : checkChangesQ loosePolicyQ PGOne.rawUpperQ wrongBoundQ = true := by decide +kernel
theorem wrong_bound_joint_rejected : checkReconstructedQ PGOne.sourceQ loosePolicyQ PGOne.rawUpperQ wrongBoundQ = false := by decide +kernel

/-- Re-synthesized factors are not covered by coefficient proximity: checked separately. -/
def wrongFactorsQ : UpperCertQ PGOne.sourceQ.model :=
  { PGOne.reconstructedUpperQ with dualFactor := { factors := [] } }
theorem wrong_factors_within_policy : checkChangesQ PGOne.policyQ PGOne.rawUpperQ wrongFactorsQ = true := by decide +kernel
theorem wrong_factors_rejected : checkReconstructedQ PGOne.sourceQ PGOne.policyQ PGOne.rawUpperQ wrongFactorsQ = false := by decide +kernel

/-- Even inserting a zero-weight term violates the fixed reference-list contract. -/
def extraZeroQ : UpperCertQ PGOne.sourceQ.model :=
  { PGOne.reconstructedUpperQ with
    assumptionTerms := PGOne.reconstructedUpperQ.assumptionTerms ++
      [{ weight := 0, index := ⟨0, by decide +kernel⟩ }] }
theorem extra_zero_local_passes : checkUpperCertQ extraZeroQ = true := by decide +kernel
theorem extra_zero_reference_rejected : checkChangesQ PGOne.policyQ PGOne.rawUpperQ extraZeroQ = false := by decide +kernel

/-- The source is never reconstructed, even when all candidate numbers recover. -/
def wrongCoverageQ : Adapters.ProximalGradientSparse.SourceQ 0 10 :=
  { PGOne.sourceQ with
    coverage := { toFull := PGOne.sourceQ.coverage.toFull, fromFull := fun _ => none } }
theorem wrong_coverage_model_unchanged : wrongCoverageQ.model = PGOne.sourceQ.model := rfl
theorem wrong_coverage_rejected :
    checkReconstructedQ wrongCoverageQ PGOne.policyQ PGOne.rawUpperQ PGOne.reconstructedUpperQ = false := by
  decide +kernel

/-- One source, a small change, accepted reconstruction, REJECTED raw certificate. -/
theorem raw_acceptance_not_inherited :
    checkChangesQ PGOne.policyQ PGOne.rawUpperQ PGOne.reconstructedUpperQ = true ∧
    checkRawQ PGOne.sourceQ PGOne.rawUpperQ = false ∧
    checkReconstructedQ PGOne.sourceQ PGOne.policyQ PGOne.rawUpperQ PGOne.reconstructedUpperQ = true :=
  ⟨PGOne.changes_check, PGOne.raw_rejected, PGOne.reconstructed_check⟩

end LeanPEP.Imported.CompositeCandidates
