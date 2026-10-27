import LeanPEP.Imported.CompositeCapture

/-! D9 OFFLINE protocol regressions: every fixture is simulated from D7 exact
inputs, not an executed PEPit solve. These tests bind original scalar ordering
and numerical fields, then reuse the D8 checker. No producer authentication. -/
namespace LeanPEP.Imported.CompositeCapture
open LeanPEP.GramPEP LeanPEP.Adapters.ProximalGradientCapture

namespace PGOne
theorem trace_check : checkTraceQ sourceQ traceQ = true := by decide +kernel
theorem binding_check : checkRawBindingQ sourceQ traceQ rawUpperQ = true := by decide +kernel
theorem raw_check : checkCapturedRawQ sourceQ traceQ rawUpperQ = true := by decide +kernel
theorem reconstructed_check : checkCapturedQ sourceQ traceQ policyQ rawUpperQ reconstructedUpperQ = true := by decide +kernel
end PGOne
namespace PGTwo
theorem trace_check : checkTraceQ sourceQ traceQ = true := by decide +kernel
theorem binding_check : checkRawBindingQ sourceQ traceQ rawUpperQ = true := by decide +kernel
theorem raw_rejected : checkCapturedRawQ sourceQ traceQ rawUpperQ = false := by decide +kernel
theorem reconstructed_check : checkCapturedQ sourceQ traceQ policyQ rawUpperQ reconstructedUpperQ = true := by decide +kernel
end PGTwo
namespace PGThree
theorem trace_check : checkTraceQ sourceQ traceQ = true := by decide +kernel
theorem binding_check : checkRawBindingQ sourceQ traceQ rawUpperQ = true := by decide +kernel
theorem raw_rejected : checkCapturedRawQ sourceQ traceQ rawUpperQ = false := by decide +kernel
theorem reconstructed_check : checkCapturedQ sourceQ traceQ policyQ rawUpperQ reconstructedUpperQ = true := by decide +kernel
end PGThree

/-- The *old* D8 check knows nothing about a separately submitted capture trace. -/
theorem old_d8_passes : Adapters.ProximalGradientReconstruction.checkReconstructedQ
    PGOne.sourceQ PGOne.policyQ PGOne.rawUpperQ PGOne.reconstructedUpperQ = true := by decide +kernel

def wrongBoundTraceQ : TraceQ 0 10 := { PGOne.traceQ with bound := PGOne.traceQ.bound + 1 }
theorem wrong_bound_trace_source_passes : checkTraceQ PGOne.sourceQ wrongBoundTraceQ = true := by decide +kernel
theorem wrong_bound_trace_rejected :
    checkCapturedQ PGOne.sourceQ wrongBoundTraceQ PGOne.policyQ PGOne.rawUpperQ PGOne.reconstructedUpperQ = false := by
  decide +kernel

def wrongResidualTraceQ : TraceQ 0 10 :=
  { PGOne.traceQ with
    residual := fun i j => PGOne.traceQ.residual i j + if i = 0 ∧ j = 1 then 1 else 0 }
theorem wrong_residual_trace_rejected : checkRawBindingQ PGOne.sourceQ wrongResidualTraceQ PGOne.rawUpperQ = false := by
  decide +kernel

def wrongWeightsTraceQ : TraceQ 0 10 :=
  { PGOne.traceQ with weights := fun i => PGOne.traceQ.weights i + if i = 0 then 1 else 0 }
theorem wrong_weights_trace_rejected : checkRawBindingQ PGOne.sourceQ wrongWeightsTraceQ PGOne.rawUpperQ = false := by
  decide +kernel

def wrongValuesTraceQ : TraceQ 0 10 :=
  { PGOne.traceQ with values := ExactReindexing.IndexMapQ.identity 6 }
theorem wrong_tau_placement_rejected : checkTraceQ PGOne.sourceQ wrongValuesTraceQ = false := by decide +kernel

/-- Both candidates can share an added zero term and still pass D8, but neither
is the capture's exactly one-entry-per-prepared-row sequence anymore. -/
def extraZeroRawQ : UpperCertQ PGOne.sourceQ.model :=
  { PGOne.rawUpperQ with
    assumptionTerms := PGOne.rawUpperQ.assumptionTerms ++ [{ weight := 0, index := ⟨0, by decide +kernel⟩ }] }
def extraZeroReconstructedQ : UpperCertQ PGOne.sourceQ.model :=
  { PGOne.reconstructedUpperQ with
    assumptionTerms := PGOne.reconstructedUpperQ.assumptionTerms ++ [{ weight := 0, index := ⟨0, by decide +kernel⟩ }] }
theorem extra_zero_old_d8_passes : Adapters.ProximalGradientReconstruction.checkReconstructedQ
    PGOne.sourceQ PGOne.policyQ extraZeroRawQ extraZeroReconstructedQ = true := by decide +kernel
theorem extra_zero_capture_rejected :
    checkCapturedQ PGOne.sourceQ PGOne.traceQ PGOne.policyQ extraZeroRawQ extraZeroReconstructedQ = false := by decide +kernel

end LeanPEP.Imported.CompositeCapture
