import LeanPEP

open LeanPEP
open LeanPEP.GramPEP

#check LeanPEP.Adapters.PEPitOneStep.SourceQ
#check LeanPEP.Adapters.PEPitOneStep.MismatchQ
#check LeanPEP.Adapters.PEPitOneStep.AuditReportQ
#check LeanPEP.Adapters.PEPitOneStep.AdapterAuditReportQ
#check LeanPEP.Adapters.PEPitOneStep.auditSourceQ
#check LeanPEP.Adapters.PEPitOneStep.checkSourceQ
#check LeanPEP.Adapters.PEPitOneStep.checkSourceQ_eq_true_iff
#check LeanPEP.Adapters.PEPitOneStep.auditAdapterOptionalQ

#check LeanPEP.Imported.PEPitOneStepAdapter.sourceQ_check
#check LeanPEP.Imported.PEPitOneStepAdapter.comparisonQ_accepted
#check LeanPEP.Imported.PEPitOneStepBadConstraintOrderAdapter.sourceQ_rejected
#check LeanPEP.Imported.PEPitOneStepBadConstraintOrderAdapter.comparisonQ_rejected
#check LeanPEP.Imported.PEPitOneStepApproxComparison.rawBundleQ_rejected
#check LeanPEP.Imported.PEPitOneStepApproxComparison.reconstructedBundleQ_check
#check LeanPEP.Imported.PEPitOneStepApproxReconstructed.bundleQ_sound_real

#eval LeanPEP.Imported.PEPitOneStepAdapter.auditQ
#eval LeanPEP.Imported.PEPitOneStepAdapter.comparisonQ
#eval LeanPEP.Imported.PEPitOneStepBadConstraintOrderAdapter.auditQ
#eval LeanPEP.Imported.PEPitOneStepBadConstraintOrderAdapter.comparisonQ
#eval LeanPEP.Imported.PEPitOneStepApproxComparison.comparisonQ
