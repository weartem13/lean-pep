import LeanPEP

open scoped NNReal
open LeanPEP LeanPEP.GramPEP LeanPEP.GramPEP.RationalReconstructionAudit
open LeanPEP.Adapters.ProximalGradientCapture

#check checkTraceQ_eq_true_iff
#check captured_row_eval
#check captured_objective_eval
#check checkRawBindingQ_eq_true_iff
#check captured_numerics_preserved
#check checkCapturedQ_eq_true_iff
#check checkCapturedRawQ_eq_true_iff
#check reconstructed_check
#check captured_raw_check
#check checked_certificate
#check Imported.CompositeCapture.PGOne.trace_check
#check Imported.CompositeCapture.PGOne.binding_check
#check Imported.CompositeCapture.PGOne.raw_check
#check Imported.CompositeCapture.PGThree.reconstructed_check
#check Imported.CompositeCapture.PGThree.raw_rejected
#check Imported.CompositeCapture.wrong_bound_trace_source_passes
#check Imported.CompositeCapture.wrong_bound_trace_rejected
#check Imported.CompositeCapture.wrong_tau_placement_rejected
#check Imported.CompositeCapture.extra_zero_old_d8_passes
#check Imported.CompositeCapture.extra_zero_capture_rejected
#check ActualFunction.ProximalGradientCaptureAudit.upper_firstOrder
#check ActualFunction.ProximalGradientCaptureAudit.raw_upper_firstOrder
#check ActualFunction.ProximalGradientCaptureAudit.three_step_upper

example {n k : ℕ} (s : Adapters.ProximalGradientSparse.SourceQ n k)
    (t : TraceQ n k) (raw : UpperCertQ s.model) (h : checkRawBindingQ s t raw = true) :
    raw.dualMatrix = t.residual := (captured_numerics_preserved s t raw h).2.2

example {n k : ℕ} (s : Adapters.ProximalGradientSparse.SourceQ n k)
    (t : TraceQ n k) (policy : PolicyQ) (raw reconstructed : UpperCertQ s.model)
    (h : checkCapturedQ s t policy raw reconstructed = true) :
    Adapters.ProximalGradientReconstruction.checkReconstructedQ s policy raw reconstructed = true :=
  reconstructed_check s t policy raw reconstructed h

example : checkCapturedRawQ Imported.CompositeCapture.PGOne.sourceQ
    Imported.CompositeCapture.PGOne.traceQ Imported.CompositeCapture.PGOne.rawUpperQ = true :=
  Imported.CompositeCapture.PGOne.raw_check

example : checkCapturedRawQ Imported.CompositeCapture.PGThree.sourceQ
    Imported.CompositeCapture.PGThree.traceQ Imported.CompositeCapture.PGThree.rawUpperQ = false :=
  Imported.CompositeCapture.PGThree.raw_rejected

example : checkCapturedQ Imported.CompositeCapture.PGThree.sourceQ
    Imported.CompositeCapture.PGThree.traceQ Imported.CompositeCapture.PGThree.policyQ
    Imported.CompositeCapture.PGThree.rawUpperQ Imported.CompositeCapture.PGThree.reconstructedUpperQ = true :=
  Imported.CompositeCapture.PGThree.reconstructed_check

example : checkCapturedQ Imported.CompositeCapture.PGOne.sourceQ
    Imported.CompositeCapture.wrongBoundTraceQ Imported.CompositeCapture.PGOne.policyQ
    Imported.CompositeCapture.PGOne.rawUpperQ Imported.CompositeCapture.PGOne.reconstructedUpperQ = false :=
  Imported.CompositeCapture.wrong_bound_trace_rejected

example : (Imported.CompositeCapture.PGThree.reconstructedUpperQ.bound : ℝ) = 1/12 := by
  norm_num [Imported.CompositeCapture.PGThree.reconstructedUpperQ]

example : IsGreatest
    (ActualFunction.ProximalGradientCanonical.oneDimensionalHilbertValues 7 (3 : ℝ≥0) 2) (3/8 : ℝ) := by
  convert ActualFunction.ProximalGradientCanonical.hilbert_tight_all 7
    (L := (3 : ℝ≥0)) (R := 2) (by norm_num) (by norm_num) using 1 <;> norm_num

example : IsGreatest
    (ActualFunction.ProximalGradientCanonical.oneDimensionalHilbertValues 7 (3 : ℝ≥0) 0) 0 := by
  convert ActualFunction.ProximalGradientCanonical.hilbert_tight_all 7
    (L := (3 : ℝ≥0)) (R := 0) (by norm_num) (by norm_num) using 1 <;> norm_num

#print axioms LeanPEP.Adapters.ProximalGradientCapture.captured_row_eval
#print axioms LeanPEP.Adapters.ProximalGradientCapture.captured_objective_eval
#print axioms LeanPEP.Adapters.ProximalGradientCapture.captured_numerics_preserved
#print axioms LeanPEP.Adapters.ProximalGradientCapture.checked_certificate
#print axioms LeanPEP.Imported.CompositeCapture.wrong_bound_trace_rejected
#print axioms LeanPEP.Imported.CompositeCapture.extra_zero_capture_rejected
#print axioms LeanPEP.Imported.CompositeCapture.PGThree.reconstructed_check
#print axioms LeanPEP.ActualFunction.ProximalGradientCaptureAudit.three_step_upper
