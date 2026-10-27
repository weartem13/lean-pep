import LeanPEP

open LeanPEP

#check LeanPEP.Adapters.PEPitOneStep.SourceConstraintKindQ
#check LeanPEP.Adapters.PEPitOneStep.SourceConstraintSenseQ
#check LeanPEP.Adapters.PEPitOneStep.SourceConstraintQ
#check LeanPEP.Adapters.PEPitOneStep.SymbolicSourceQ
#check LeanPEP.Adapters.PEPitOneStep.SourceMatrixMismatchQ
#check LeanPEP.Adapters.PEPitOneStep.SourceConstraintHeaderMismatchQ
#check LeanPEP.Adapters.PEPitOneStep.SourceConstraintExprMismatchQ
#check LeanPEP.Adapters.PEPitOneStep.expectedPointDecompositionQ
#check LeanPEP.Adapters.PEPitOneStep.expectedGradientDecompositionQ
#check LeanPEP.Adapters.PEPitOneStep.expectedConstraintsQ
#check LeanPEP.Adapters.PEPitOneStep.expectedObjectiveQ
#check LeanPEP.Adapters.PEPitOneStep.expectedNativeToCenteredQ
#check LeanPEP.Adapters.PEPitOneStep.SourceValidQ
#check LeanPEP.Adapters.PEPitOneStep.checkSourceQ_eq_true_iff

#check LeanPEP.Imported.PEPitOneStepAdapter.sourceQ_check
#check LeanPEP.Imported.PEPitOneStepBadConstraintOrderAdapter.sourceQ_rejected
#check LeanPEP.Imported.PEPitOneStepBadSymbolicCoefficientAdapter.sourceQ_rejected
#check LeanPEP.Imported.PEPitOneStepBadSymbolicCoefficientAdapter.comparisonQ_rejected

/-- The supported source has no typed symbolic mismatch. -/
example :
    LeanPEP.Imported.PEPitOneStepAdapter.auditQ.matrixMismatches = [] ∧
      LeanPEP.Imported.PEPitOneStepAdapter.auditQ.constraintHeaderMismatches = [] ∧
      LeanPEP.Imported.PEPitOneStepAdapter.auditQ.constraintExprMismatches = [] ∧
      LeanPEP.Imported.PEPitOneStepAdapter.auditQ.objectiveMismatches = [] := by
  native_decide

/-- The coefficient-corruption fixture keeps every lightweight metadata field
canonical; rejection comes from the typed exact symbolic payload. -/
example :
    LeanPEP.Imported.PEPitOneStepBadSymbolicCoefficientAdapter.auditQ.mismatches = [] ∧
      LeanPEP.Imported.PEPitOneStepBadSymbolicCoefficientAdapter.auditQ.constraintExprMismatches ≠ [] := by
  native_decide

#eval LeanPEP.Imported.PEPitOneStepAdapter.auditQ
#eval LeanPEP.Imported.PEPitOneStepBadConstraintOrderAdapter.auditQ
#eval LeanPEP.Imported.PEPitOneStepBadSymbolicCoefficientAdapter.auditQ
