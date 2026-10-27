import LeanPEP.GramPEP.UpperCertificateAudit
import LeanPEP.GramPEP.UpperCertificateExamples

/-!
# Structured general-upper-certificate audit examples

The malformed certificates below are designed to isolate checker channels.
Whenever possible, a negative term is paired with a cancelling positive term,
so the exact affine identity remains unchanged and the report localizes the
sign error rather than manufacturing a second identity failure.
-/

namespace LeanPEP
namespace GramPEP
namespace UpperCertificateAuditExamples

open UpperCertificateExamples

/-- A correct structural certificate has an entirely clean audit. -/
theorem upperCertQ_audit :
    auditUpperCertQ upperCertQ =
      { accepted := true
        negativeInterpWeights := []
        negativeAssumptionWeights := []
        dualAudit :=
          { accepted := true
            asymmetries := []
            negativeWeights := []
            entryMismatches := [] }
        identityMismatches := [] } := by
  native_decide

/-- The genuine one-step `1/6` certificate also has a clean audit. -/
theorem oneStepUpperCertQ_audit :
    auditUpperCertQ oneStepUpperCertQ =
      { accepted := true
        negativeInterpWeights := []
        negativeAssumptionWeights := []
        dualAudit :=
          { accepted := true
            asymmetries := []
            negativeWeights := []
            entryMismatches := [] }
        identityMismatches := [] } := by
  native_decide

/-- Append a `-1,+1` cancelling pair on the same interpolation slack. -/
def cancellingNegativeInterpCertQ : UpperCertQ twoPointModelQ :=
  { upperCertQ with
    interpTerms := upperCertQ.interpTerms ++
      [ { weight := -1, i := 0, j := 1 }
      , { weight := 1, i := 0, j := 1 } ] }

/-- The exact identity remains valid; only the negative interpolation weight is
reported. -/
theorem cancellingNegativeInterpCertQ_audit :
    auditUpperCertQ cancellingNegativeInterpCertQ =
      { accepted := false
        negativeInterpWeights :=
          [{ index := 1, weight := -1, i := 0, j := 1 }]
        negativeAssumptionWeights := []
        dualAudit :=
          { accepted := true
            asymmetries := []
            negativeWeights := []
            entryMismatches := [] }
        identityMismatches := [] } := by
  native_decide

/-- Append a `-1,+1` cancelling pair on the sole formulation assumption. -/
def cancellingNegativeAssumptionCertQ : UpperCertQ twoPointModelQ :=
  { upperCertQ with
    assumptionTerms := upperCertQ.assumptionTerms ++
      [ { weight := -1, index := twoPointAssumption0 }
      , { weight := 1, index := twoPointAssumption0 } ] }

/-- The exact identity remains valid; only the negative assumption weight is
reported. -/
theorem cancellingNegativeAssumptionCertQ_audit :
    auditUpperCertQ cancellingNegativeAssumptionCertQ =
      { accepted := false
        negativeInterpWeights := []
        negativeAssumptionWeights :=
          [{ index := 1, assumptionIndex := 0, weight := -1 }]
        dualAudit :=
          { accepted := true
            asymmetries := []
            negativeWeights := []
            entryMismatches := [] }
        identityMismatches := [] } := by
  native_decide

/-- Append cancelling `-e₀e₀ᵀ,+e₀e₀ᵀ` factors while retaining the same dual
matrix. -/
def cancellingNegativeDualCertQ : UpperCertQ twoPointModelQ :=
  { upperCertQ with
    dualFactor :=
      { factors := upperCertQ.dualFactor.factors ++
          [ { weight := -1, vector := e0Q }
          , { weight := 1, vector := e0Q } ] } }

/-- The target/factorized matrix identity is exact; only the negative dual
factor weight is reported. -/
theorem cancellingNegativeDualCertQ_audit :
    auditUpperCertQ cancellingNegativeDualCertQ =
      { accepted := false
        negativeInterpWeights := []
        negativeAssumptionWeights := []
        dualAudit :=
          { accepted := false
            asymmetries := []
            negativeWeights := [{ index := 1, weight := -1 }]
            entryMismatches := [] }
        identityMismatches := [] } := by
  native_decide

/-- Preserve the target dual matrix but omit its factorization. -/
def missingDualFactorCertQ : UpperCertQ twoPointModelQ :=
  { upperCertQ with dualFactor := { factors := [] } }

/-- Missing the sole dual factor reports the exact `(1,1)` entry while the
upper identity itself remains unchanged. -/
theorem missingDualFactorCertQ_audit :
    auditUpperCertQ missingDualFactorCertQ =
      { accepted := false
        negativeInterpWeights := []
        negativeAssumptionWeights := []
        dualAudit :=
          { accepted := false
            asymmetries := []
            negativeWeights := []
            entryMismatches :=
              [{ i := 1, j := 1, expected := 1, actual := 0 }] }
        identityMismatches := [] } := by
  native_decide

/-- A wrong bound changes exactly the constant coefficient. -/
theorem wrongBoundCertQ_audit :
    auditUpperCertQ wrongBoundCertQ =
      { accepted := false
        negativeInterpWeights := []
        negativeAssumptionWeights := []
        dualAudit :=
          { accepted := true
            asymmetries := []
            negativeWeights := []
            entryMismatches := [] }
        identityMismatches :=
          [{ location := LinearCoeffLocationQ.const,
             expected := 2, actual := 1 }] } := by
  native_decide

/-- Combine all three isolated sign failures with the wrong bound. -/
def combinedFailureCertQ : UpperCertQ twoPointModelQ :=
  { upperCertQ with
    bound := 2
    interpTerms := upperCertQ.interpTerms ++
      [ { weight := -1, i := 0, j := 1 }
      , { weight := 1, i := 0, j := 1 } ]
    assumptionTerms := upperCertQ.assumptionTerms ++
      [ { weight := -1, index := twoPointAssumption0 }
      , { weight := 1, index := twoPointAssumption0 } ]
    dualFactor :=
      { factors := upperCertQ.dualFactor.factors ++
          [ { weight := -1, vector := e0Q }
          , { weight := 1, vector := e0Q } ] } }

/-- The complete report exposes all independent problems simultaneously rather
than stopping at the first failed check. -/
theorem combinedFailureCertQ_audit :
    auditUpperCertQ combinedFailureCertQ =
      { accepted := false
        negativeInterpWeights :=
          [{ index := 1, weight := -1, i := 0, j := 1 }]
        negativeAssumptionWeights :=
          [{ index := 1, assumptionIndex := 0, weight := -1 }]
        dualAudit :=
          { accepted := false
            asymmetries := []
            negativeWeights := [{ index := 1, weight := -1 }]
            entryMismatches := [] }
        identityMismatches :=
          [{ location := LinearCoeffLocationQ.const,
             expected := 2, actual := 1 }] } := by
  native_decide

end UpperCertificateAuditExamples
end GramPEP
end LeanPEP
