import LeanPEP

open LeanPEP
open LeanPEP.GramPEP

#check ImportMetadataQ
#check ExactGramBundleQ
#check checkDataRealizesModelQ
#check checkInterpolationFeasibleQ
#check checkAssumptionsFeasibleQ
#check checkExactGramBundleQ
#check checkExactGramBundleQ_sound_real
#check ExactGramBundleAuditReportQ
#check auditExactGramBundleQ
#check auditExactGramBundleQ_sound_real
#check checkPSDFactorQ_sound_real

#check LeanPEP.Imported.GramOneStepExact.bundleQ_check
#check LeanPEP.Imported.GramOneStepExact.bundleQ_sound_real
#check LeanPEP.Imported.GramOneStepBadMetadata.bundleQ_rejected
#check LeanPEP.Imported.GramOneStepBadPrimal.bundleQ_rejected
#check LeanPEP.Imported.GramOneStepBadPrimalFactor.bundleQ_rejected
#check LeanPEP.Imported.GramOneStepBadUpper.bundleQ_rejected

#eval LeanPEP.Imported.GramOneStepExact.auditQ
#eval LeanPEP.Imported.GramOneStepBadMetadata.auditQ
#eval LeanPEP.Imported.GramOneStepBadPrimal.auditQ
#eval LeanPEP.Imported.GramOneStepBadPrimalFactor.auditQ
#eval LeanPEP.Imported.GramOneStepBadUpper.auditQ
