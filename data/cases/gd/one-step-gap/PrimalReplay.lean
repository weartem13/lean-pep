import LeanPEP.Adapters.GDOnePrimal
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace LeanPEP.Imported.GDOnePrimal003
open LeanPEP.GramPEP LeanPEP.GramPEP.UpperCertificateExamples
open LeanPEP.ActualFunction.GDOneCapture LeanPEP.Adapters
def sourceQ : SourceQ := { position := ![![(0 : ℚ), (0 : ℚ), (0 : ℚ)], ![(1 : ℚ), (0 : ℚ), (0 : ℚ)], ![(1 : ℚ), (-1 : ℚ), (0 : ℚ)]], gradient := ![![(0 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (1 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (1 : ℚ)]], rows := [{ constCoeff := (0 : ℚ),   valueCoeff := ![(1 : ℚ), (0 : ℚ), (-1 : ℚ), (1 : ℚ)],   gramCoeff := ![![(0 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (0 : ℚ)]] }, { constCoeff := (-1 : ℚ),   valueCoeff := ![(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)],   gramCoeff := ![![(1 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (0 : ℚ)]] }, { constCoeff := (0 : ℚ),   valueCoeff := ![(-1 : ℚ), (1 : ℚ), (0 : ℚ), (0 : ℚ)],   gramCoeff := ![![(0 : ℚ), ((-1 : ℚ) / 2), (0 : ℚ)], ![((-1 : ℚ) / 2), ((1 : ℚ) / 2), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (0 : ℚ)]] }, { constCoeff := (0 : ℚ),   valueCoeff := ![(-1 : ℚ), (0 : ℚ), (1 : ℚ), (0 : ℚ)],   gramCoeff := ![![(0 : ℚ), (0 : ℚ), ((-1 : ℚ) / 2)], ![(0 : ℚ), (0 : ℚ), ((1 : ℚ) / 2)], ![((-1 : ℚ) / 2), ((1 : ℚ) / 2), ((1 : ℚ) / 2)]] }, { constCoeff := (0 : ℚ),   valueCoeff := ![(1 : ℚ), (-1 : ℚ), (0 : ℚ), (0 : ℚ)],   gramCoeff := ![![(0 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), ((1 : ℚ) / 2), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (0 : ℚ)]] }, { constCoeff := (0 : ℚ),   valueCoeff := ![(0 : ℚ), (-1 : ℚ), (1 : ℚ), (0 : ℚ)],   gramCoeff := ![![(0 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), ((1 : ℚ) / 2), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), ((1 : ℚ) / 2)]] }, { constCoeff := (0 : ℚ),   valueCoeff := ![(1 : ℚ), (0 : ℚ), (-1 : ℚ), (0 : ℚ)],   gramCoeff := ![![(0 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), ((1 : ℚ) / 2)]] }, { constCoeff := (0 : ℚ),   valueCoeff := ![(0 : ℚ), (1 : ℚ), (-1 : ℚ), (0 : ℚ)],   gramCoeff := ![![(0 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), ((-1 : ℚ) / 2), ((-1 : ℚ) / 2)], ![(0 : ℚ), ((-1 : ℚ) / 2), ((1 : ℚ) / 2)]] }], labels := [(0,0,0),(1,0,0),(2,0,1),(2,0,2),(2,1,0),(2,1,2),(2,2,0),(2,2,1)], metric := { constCoeff := (0 : ℚ),   valueCoeff := ![(-1 : ℚ), (0 : ℚ), (1 : ℚ), (0 : ℚ)],   gramCoeff := ![![(0 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (0 : ℚ)]] }, objective := { constCoeff := (0 : ℚ),   valueCoeff := ![(0 : ℚ), (0 : ℚ), (0 : ℚ), (1 : ℚ)],   gramCoeff := ![![(0 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (0 : ℚ)]] }, steps := 1, stepSize := 1 }
def rawPrimalQ : GDOnePrimal.NativeQ := { gram := ![![((4999999999952779 : ℚ) / 5000000000000000), ((16666610121368783 : ℚ) / 50000000000000000), ((8333305060601169 : ℚ) / 25000000000000000)], ![((16666610121368783 : ℚ) / 50000000000000000), ((1388879464704567 : ℚ) / 12500000000000000), ((5555517858719787 : ℚ) / 50000000000000000)], ![((8333305060601169 : ℚ) / 25000000000000000), ((5555517858719787 : ℚ) / 50000000000000000), ((11111035717618349 : ℚ) / 100000000000000000)]], values := ![((-118577028386799 : ℚ) / 800000000000000), ((6477786917724701 : ℚ) / 50000000000000000), ((18445381178166957 : ℚ) / 1000000000000000000), ((2083333333286579 : ℚ) / 12500000000000000)] }
def candidateQ : GDOnePrimal.NativeQ := { gram := ![![(1 : ℚ), ((333333 : ℚ) / 1000000), ((333333 : ℚ) / 1000000)], ![((333333 : ℚ) / 1000000), ((111111 : ℚ) / 1000000), ((111111 : ℚ) / 1000000)], ![((333333 : ℚ) / 1000000), ((111111 : ℚ) / 1000000), ((111111 : ℚ) / 1000000)]], values := ![((-148221 : ℚ) / 1000000), ((32389 : ℚ) / 250000), ((3689 : ℚ) / 200000), ((83333 : ℚ) / 500000)] }
def nativeFactorQ : PSDFactorCertQ 3 := { factors := [{ weight := (1 : ℚ), vector := ![(1 : ℚ), ((333333 : ℚ) / 1000000), ((333333 : ℚ) / 1000000)] }, { weight := ((111111 : ℚ) / 1000000000000), vector := ![(0 : ℚ), (1 : ℚ), (1 : ℚ)] }] }
def rawFactorQ : PSDFactorCertQ 3 := { factors := [{ weight := ((4999999999952779 : ℚ) / 5000000000000000), vector := ![(1 : ℚ), ((16666610121368783 : ℚ) / 49999999999527790), ((8333305060601169 : ℚ) / 24999999999763895)] }, { weight := ((577669310245938766631 : ℚ) / 2499999999976389500000000000000000), vector := ![(0 : ℚ), (1 : ℚ), ((-1572306768056330433924 : ℚ) / 577669310245938766631)] }, { weight := ((32155848130611744656647207 : ℚ) / 57766931024593876663100000000000000000), vector := ![(0 : ℚ), (0 : ℚ), (1 : ℚ)] }] }
def canonicalQ := GDOnePrimal.canonicalData candidateQ
theorem source_check : checkSourceQ sourceQ = true := by decide +kernel
theorem source_rows_binding : sourceQ.rows.map RationalReconstructionAudit.exprCoefficientsQ = expectedRows.map RationalReconstructionAudit.exprCoefficientsQ := by decide +kernel
theorem policy_check : GDOnePrimal.policy rawPrimalQ candidateQ = true := by decide +kernel
theorem native_psd_check : checkPSDFactorQ candidateQ.gram nativeFactorQ = true := by decide +kernel
theorem raw_psd_check : checkPSDFactorQ rawPrimalQ.gram rawFactorQ = true := by decide +kernel
theorem raw_rows_rejected : checkAssumptionsFeasibleQ nativeModelQ rawPrimalQ.data = false := by decide +kernel
theorem raw_performance_value : (expectedRows.get ⟨0, by decide +kernel⟩).evalQ rawPrimalQ.data = ((1260613 : ℚ) / 1000000000000000000) := by decide +kernel
theorem native_rows_check : checkAssumptionsFeasibleQ nativeModelQ candidateQ.data = true := by decide +kernel
theorem full_rows_check : checkAssumptionsFeasibleQ GDOnePrimal.fullNativeModelQ candidateQ.data = true := by decide +kernel
theorem model_check : checkDataRealizesModelQ oneStepModelQ canonicalQ = true := by decide +kernel
theorem interpolation_check : checkInterpolationFeasibleQ canonicalQ = true := by decide +kernel
theorem radius_check : checkAssumptionsFeasibleQ oneStepModelQ canonicalQ = true := by decide +kernel
theorem finite_check : GDOnePrimal.checkFinite candidateQ nativeFactorQ = true := by decide +kernel
theorem tau_beta : candidateQ.values 3 ≤ GDOnePrimal.beta candidateQ := by decide +kernel
theorem beta_value : GDOnePrimal.beta candidateQ = ((83333 : ℚ) / 500000) := by decide +kernel
theorem tau_value : candidateQ.values 3 = ((83333 : ℚ) / 500000) := by decide +kernel
theorem counts : expectedRows.length = 8 ∧ GDOnePrimal.fullNativeModelQ.assumptions.length = 11 ∧ (pointIndexPairs 3).length = 9 ∧ oneStepModelQ.assumptions.length = 1 ∧ (gramIndexPairs 3).length + (List.finRange 4).length = 13 := by decide +kernel
theorem self_rows_zero : ∀ i : Fin 3, checkLinearExprEqQ (interpolationExprQ oneStepModelQ i i) (LinearExprQ.zero 3 3) = true := by decide +kernel
theorem native_gram_binding : canonicalQ.gram = candidateQ.gram := by decide +kernel
theorem value_binding : ∀ i : Fin 3, canonicalQ.value i = candidateQ.values i.castSucc := by decide +kernel

theorem native_primal_checked : IsGramPosSemidef (castDataQ candidateQ.data).gram ∧
    AssumptionsFeasibleR nativeModelQ (castDataQ candidateQ.data) ∧
    AssumptionsFeasibleR GDOnePrimal.fullNativeModelQ (castDataQ candidateQ.data) := by
  have h := GDOnePrimal.checkFinite_sound candidateQ nativeFactorQ finite_check
  exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem finite_primal_verified :
    RealizesModelQ oneStepModelQ (castDataQ canonicalQ) ∧
    CoreFeasible (castDataQ canonicalQ) ∧
    AssumptionsFeasibleR oneStepModelQ (castDataQ canonicalQ) := by
  have h := GDOnePrimal.checkFinite_sound candidateQ nativeFactorQ finite_check
  exact ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

theorem objective_verified : oneStepObjectiveQ.evalR (castDataQ canonicalQ) =
    (GDOnePrimal.beta candidateQ : ℝ) ∧ 0 < (GDOnePrimal.beta candidateQ : ℝ) := by
  have h := GDOnePrimal.checkFinite_sound candidateQ nativeFactorQ finite_check
  exact ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

theorem concrete_primal_transport :
    (castDataQ canonicalQ).gram = (castDataQ candidateQ.data).gram ∧
    ∀ i : Fin 3, (castDataQ canonicalQ).value i = (candidateQ.values i.castSucc : ℝ) :=
  GDOnePrimal.primal_transport candidateQ
#print axioms source_check
#print axioms source_rows_binding
#print axioms policy_check
#print axioms native_psd_check
#print axioms raw_psd_check
#print axioms raw_rows_rejected
#print axioms raw_performance_value
#print axioms native_rows_check
#print axioms full_rows_check
#print axioms model_check
#print axioms interpolation_check
#print axioms radius_check
#print axioms finite_check
#print axioms tau_beta
#print axioms beta_value
#print axioms tau_value
#print axioms counts
#print axioms self_rows_zero
#print axioms native_gram_binding
#print axioms value_binding
#print axioms native_primal_checked
#print axioms finite_primal_verified
#print axioms objective_verified
#print axioms concrete_primal_transport
#print axioms GDOnePrimal.checkFinite_sound
#print axioms GDOnePrimal.primal_transport
end LeanPEP.Imported.GDOnePrimal003
