import LeanPEP.ActualFunction.PGOneCapturedTightness
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace LeanPEP.Imported.C14PGOnePairRegression
open LeanPEP.GramPEP LeanPEP.Adapters
open LeanPEP.Imported.C14PGOneUpper

def wrongHorizon := { sourceQ with base := { sourceQ.base with snapshot :=
  { sourceQ.base.snapshot with metadata := { sourceQ.base.snapshot.metadata with steps := 2 } } } }
theorem wrong_horizon_rejected : ProximalGradientSparse.checkSourceQ wrongHorizon = false := by decide +kernel

def wrongCase := { sourceQ with base := { sourceQ.base with snapshot :=
  { sourceQ.base.snapshot with metadata := { sourceQ.base.snapshot.metadata with profileId := "gradient-descent-one-step" } } } }
theorem wrong_case_rejected : ProximalGradientSparse.checkSourceQ wrongCase = false := by decide +kernel

theorem wrong_objective_rejected : ProximalGradientSparse.checkSourceQ
    { sourceQ with objective := LinearExprQ.zero 6 6 } = false := by decide +kernel

theorem wrong_endpoint_rejected : checkUpperCertQ
    { structuredUpperQ with bound := (1/3 : ℚ) } = false := by decide +kernel

def badGram : PGOnePrimal.NativeQ :=
  { LeanPEP.Imported.C14PGOnePrimal.candidateQ with gram := fun i j =>
    if i = 0 ∧ j = 1 then LeanPEP.Imported.C14PGOnePrimal.candidateQ.gram i j + 1
    else LeanPEP.Imported.C14PGOnePrimal.candidateQ.gram i j }
theorem changed_gram_rejected : checkPSDFactorQ badGram.gram
    LeanPEP.Imported.C14PGOnePrimal.nativeFactorQ = false := by decide +kernel

def badValue : PGOnePrimal.NativeQ :=
  { LeanPEP.Imported.C14PGOnePrimal.candidateQ with values := fun i =>
    if i = 0 then LeanPEP.Imported.C14PGOnePrimal.candidateQ.values i + 1
    else LeanPEP.Imported.C14PGOnePrimal.candidateQ.values i }
theorem changed_value_rejected : PGOnePrimal.checkFinite
    sourceQ traceQ badValue LeanPEP.Imported.C14PGOnePrimal.nativeFactorQ
    LeanPEP.Imported.C14PGOnePrimal.centeredFactorQ = false := by decide +kernel

theorem changed_value_policy_rejected : PGOnePrimal.policy
    LeanPEP.Imported.C14PGOnePrimal.rawPrimalQ badValue = false := by decide +kernel
#print axioms wrong_horizon_rejected
#print axioms wrong_case_rejected
#print axioms wrong_objective_rejected
#print axioms wrong_endpoint_rejected
#print axioms changed_gram_rejected
#print axioms changed_value_rejected
#print axioms changed_value_policy_rejected
end LeanPEP.Imported.C14PGOnePairRegression
