import LeanPEP.GramPEP.PSDFactorization
import LeanPEP.GramPEP.FiniteGD

/-!
# Exact PSD-factorization checker examples

These examples exercise acceptance, soundness, and structured rejection:

* the one-dimensional unit Gram matrix;
* a nontrivial positive-definite `2 × 2` rational matrix;
* a negative factor weight whose matrix identity is otherwise exact;
* an exact matrix-entry mismatch; and
* an asymmetric target matrix.
-/

namespace LeanPEP
namespace GramPEP
namespace PSDFactorizationExamples

/-- Exact certificate `[1] = 1 * [1][1]ᵀ`. -/
def unitFactorCertQ : PSDFactorCertQ 1 :=
  { factors :=
      [{ weight := 1
         vector := ![(1 : ℚ)] }] }

/-- The unit Gram certificate is accepted. -/
theorem unitFactorCertQ_check :
    checkPSDFactorQ (unitGram (𝕜 := ℚ)) unitFactorCertQ = true := by
  native_decide

/-- The accepted unit certificate proves the unit Gram matrix PSD. -/
theorem unitGram_psd_from_checker :
    IsGramPosSemidef (unitGram (𝕜 := ℚ)) :=
  checkPSDFactorQ_sound _ _ unitFactorCertQ_check

/-- A nontrivial exact rational `2 × 2` Gram matrix. -/
def twoByTwoGramQ : Gram 2 ℚ :=
  ![![(2 : ℚ), 1], ![1, 2]]

/-- Exact decomposition

`[[2,1],[1,2]] = [1,1][1,1]ᵀ + [1,0][1,0]ᵀ + [0,1][0,1]ᵀ`.
-/
def twoByTwoFactorCertQ : PSDFactorCertQ 2 :=
  { factors :=
      [{ weight := 1
         vector := ![(1 : ℚ), 1] },
       { weight := 1
         vector := ![(1 : ℚ), 0] },
       { weight := 1
         vector := ![(0 : ℚ), 1] }] }

/-- The nontrivial rational factorization is accepted. -/
theorem twoByTwoFactorCertQ_check :
    checkPSDFactorQ twoByTwoGramQ twoByTwoFactorCertQ = true := by
  native_decide

/-- Checker soundness proves the nontrivial matrix PSD. -/
theorem twoByTwoGramQ_posSemidef :
    IsGramPosSemidef twoByTwoGramQ :=
  checkPSDFactorQ_sound _ _ twoByTwoFactorCertQ_check

/-- A symmetric target exactly represented by a negative-weight factor. -/
def negativeUnitGramQ : Gram 1 ℚ :=
  ![![(-1 : ℚ)]]

/-- The matrix identity is exact, but the factor weight is invalid. -/
def negativeWeightCertQ : PSDFactorCertQ 1 :=
  { factors :=
      [{ weight := -1
         vector := ![(1 : ℚ)] }] }

/-- A negative weight is rejected even when the entry identity matches. -/
theorem negativeWeightCertQ_check :
    checkPSDFactorQ negativeUnitGramQ negativeWeightCertQ = false := by
  native_decide

/-- The audit reports the exact negative weight and no entry mismatch. -/
theorem negativeWeightCertQ_audit :
    auditPSDFactorQ negativeUnitGramQ negativeWeightCertQ =
      { accepted := false
        asymmetries := []
        negativeWeights := [{ index := 0, weight := -1 }]
        entryMismatches := [] } := by
  native_decide

/-- Empty factors cannot reconstruct the unit Gram matrix. -/
def missingFactorCertQ : PSDFactorCertQ 1 :=
  { factors := [] }

/-- The missing factor is rejected. -/
theorem missingFactorCertQ_check :
    checkPSDFactorQ (unitGram (𝕜 := ℚ)) missingFactorCertQ = false := by
  native_decide

/-- The audit localizes the exact matrix entry mismatch. -/
theorem missingFactorCertQ_audit :
    auditPSDFactorQ (unitGram (𝕜 := ℚ)) missingFactorCertQ =
      { accepted := false
        asymmetries := []
        negativeWeights := []
        entryMismatches :=
          [{ i := 0, j := 0, expected := 1, actual := 0 }] } := by
  native_decide

/-- A deliberately asymmetric target matrix. -/
def asymmetricGramQ : Gram 2 ℚ :=
  ![![(1 : ℚ), 1], ![0, 1]]

/-- Asymmetry is rejected before it could have PSD semantics. -/
theorem asymmetricGramQ_check :
    checkPSDFactorQ asymmetricGramQ { factors := [] } = false := by
  native_decide

/-- The audit reports both ordered manifestations of the asymmetric pair. -/
theorem asymmetricGramQ_asymmetries :
    (auditPSDFactorQ asymmetricGramQ { factors := [] }).asymmetries =
      [{ i := 0, j := 1, left := 1, right := 0 },
       { i := 1, j := 0, left := 0, right := 1 }] := by
  native_decide

end PSDFactorizationExamples
end GramPEP
end LeanPEP
