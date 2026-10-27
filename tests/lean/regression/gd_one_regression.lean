import LeanPEP.ActualFunction.GDOneCapturedTightness
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace LeanPEP.Imported.C14GDOneRegression
open LeanPEP.GramPEP LeanPEP.GramPEP.UpperCertificateExamples
open LeanPEP.ActualFunction.GDOneCapture LeanPEP.Adapters
open LeanPEP.Imported.C14GDOneDual
open LeanPEP.Imported.C14GDOnePrimal (candidateQ nativeFactorQ rawPrimalQ)
theorem wrong_horizon : checkSourceQ {sourceQ with steps := 2} = false := by decide +kernel
theorem wrong_reference : checkSourceQ {sourceQ with gradient := fun _ _ => 0} = false := by decide +kernel
theorem wrong_objective : checkSourceQ {sourceQ with objective := LinearExprQ.zero 4 3} = false := by decide +kernel
theorem omitted_interpolation : checkSourceQ {sourceQ with rows := sourceQ.rows.take 7} = false := by decide +kernel
theorem wrong_bound : checkUpperCertQ {structuredUpperQ with bound := 1/7} = false := by decide +kernel
def badGram : GDOnePrimal.NativeQ := {candidateQ with gram := fun i j => if i=0 ∧ j=1 then candidateQ.gram i j+1/10000000 else candidateQ.gram i j}
theorem changed_gram : checkPSDFactorQ badGram.gram nativeFactorQ = false := by decide +kernel
theorem wrong_factor : checkPSDFactorQ candidateQ.gram {factors := []} = false := by decide +kernel
def badValue : GDOnePrimal.NativeQ := {candidateQ with values := fun i => if i=2 then candidateQ.values i+1/1000000 else candidateQ.values i}
theorem changed_value : GDOnePrimal.checkFinite badValue nativeFactorQ = false := by decide +kernel
theorem interpolation_required : checkInterpolationFeasibleQ (GDOnePrimal.canonicalData badValue) = false := by decide +kernel
def gaugeOutside : GDOnePrimal.NativeQ := {candidateQ with values := fun i => if i=3 then candidateQ.values i else candidateQ.values i+1/1000}
theorem gauge_feasible : GDOnePrimal.checkFinite gaugeOutside nativeFactorQ = true := by decide +kernel
theorem gauge_policy_rejected : GDOnePrimal.policy rawPrimalQ gaugeOutside = false := by decide +kernel
def oldRawObstruction : GDOnePrimal.NativeQ := { gram := ![![((4999999999952779 : ℚ) / 5000000000000000), ((16666610121368783 : ℚ) / 50000000000000000), ((8333305060601169 : ℚ) / 25000000000000000)], ![((16666610121368783 : ℚ) / 50000000000000000), ((1388879464704567 : ℚ) / 12500000000000000), ((5555517858719787 : ℚ) / 50000000000000000)], ![((8333305060601169 : ℚ) / 25000000000000000), ((5555517858719787 : ℚ) / 50000000000000000), ((11111035717618349 : ℚ) / 100000000000000000)]], values := ![((-118577028386799 : ℚ) / 800000000000000), ((6477786917724701 : ℚ) / 50000000000000000), ((18445381178166957 : ℚ) / 1000000000000000000), ((2083333333286579 : ℚ) / 12500000000000000)] }
theorem old_raw_optimal_face_rejected : GDOnePrimal.policy oldRawObstruction candidateQ = false := by decide +kernel
#print axioms wrong_horizon
#print axioms wrong_reference
#print axioms wrong_objective
#print axioms omitted_interpolation
#print axioms wrong_bound
#print axioms changed_gram
#print axioms wrong_factor
#print axioms changed_value
#print axioms interpolation_required
#print axioms gauge_feasible
#print axioms gauge_policy_rejected
#print axioms old_raw_optimal_face_rejected
end LeanPEP.Imported.C14GDOneRegression
