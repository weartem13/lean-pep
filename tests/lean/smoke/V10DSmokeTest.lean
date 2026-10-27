import LeanPEP

open LeanPEP
open LeanPEP.GramPEP
open LeanPEP.GramPEP.UpperCertificateExamples

#check LinearExprQ
#check ModelQ
#check RealizesModelQ
#check AssumptionsFeasibleR
#check UpperCertQ
#check checkLinearExprEqQ
#check checkUpperCertQ
#check checkUpperCertQ_sound_real
#check gramPairingR_nonneg_of_valid
#check upperCertQ_check
#check upper_bound
#check oneStepUpperCertQ_check
#check oneStep_upper

#eval checkUpperCertQ upperCertQ
#eval checkUpperCertQ oneStepUpperCertQ
#eval checkUpperCertQ negativeInterpCertQ
#eval checkUpperCertQ negativeAssumptionCertQ
#eval checkUpperCertQ negativeDualCertQ
#eval checkUpperCertQ wrongBoundCertQ

example : checkUpperCertQ upperCertQ = true := by
  exact upperCertQ_check

example : checkUpperCertQ oneStepUpperCertQ = true := by
  exact oneStepUpperCertQ_check
