import LeanPEP

open LeanPEP
open LeanPEP.GramPEP
open LeanPEP.GramPEP.PSDFactorizationExamples

#check RankOneFactorQ
#check PSDFactorCertQ
#check weightedOuterQ
#check gramNormSq_zero_gram
#check factorGramQ
#check checkGramEqQ
#check checkGramSymmetricQ
#check checkFactorWeightsQ
#check PSDFactorValidQ
#check checkPSDFactorQ
#check checkPSDFactorQ_sound
#check GramAsymmetryQ
#check NegativeFactorWeightQ
#check GramEntryMismatchQ
#check PSDFactorAuditReportQ
#check auditPSDFactorQ
#check auditPSDFactorQ_sound
#check mem_gramAsymmetriesQ_sound
#check mem_negativeFactorWeightsQ_sound
#check mem_gramEntryMismatchesQ_sound
#check unitFactorCertQ_check
#check twoByTwoFactorCertQ_check
#check twoByTwoGramQ_posSemidef
#check negativeWeightCertQ_audit
#check missingFactorCertQ_audit
#check asymmetricGramQ_asymmetries

#eval checkPSDFactorQ (unitGram (𝕜 := ℚ)) unitFactorCertQ
#eval checkPSDFactorQ twoByTwoGramQ twoByTwoFactorCertQ
#eval auditPSDFactorQ negativeUnitGramQ negativeWeightCertQ
#eval auditPSDFactorQ (unitGram (𝕜 := ℚ)) missingFactorCertQ
#eval (auditPSDFactorQ asymmetricGramQ { factors := [] }).asymmetries

example : IsGramPosSemidef twoByTwoGramQ := by
  exact twoByTwoGramQ_posSemidef

example : checkPSDFactorQ negativeUnitGramQ negativeWeightCertQ = false := by
  exact negativeWeightCertQ_check

example :
    (auditPSDFactorQ (unitGram (𝕜 := ℚ)) missingFactorCertQ).entryMismatches =
      [{ i := 0, j := 0, expected := 1, actual := 0 }] := by
  native_decide
