import LeanPEP.ActualFunction.GDOneCapture
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace LeanPEP.Imported.GDOneStructured003
open LeanPEP.GramPEP LeanPEP.ActualFunction LeanPEP.ActualFunction.GDOneCapture
open LeanPEP.GramPEP.RationalReconstructionAudit
open scoped NNReal
def sourceQ : SourceQ := {position := ![![(0 : ℚ), (0 : ℚ), (0 : ℚ)], ![(1 : ℚ), (0 : ℚ), (0 : ℚ)], ![(1 : ℚ), (-1 : ℚ), (0 : ℚ)]], gradient := ![![(0 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (1 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (1 : ℚ)]], rows := [{ constCoeff := (0 : ℚ),   valueCoeff := ![(1 : ℚ), (0 : ℚ), (-1 : ℚ), (1 : ℚ)],   gramCoeff := ![![(0 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (0 : ℚ)]] }, { constCoeff := (-1 : ℚ),   valueCoeff := ![(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ)],   gramCoeff := ![![(1 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (0 : ℚ)]] }, { constCoeff := (0 : ℚ),   valueCoeff := ![(-1 : ℚ), (1 : ℚ), (0 : ℚ), (0 : ℚ)],   gramCoeff := ![![(0 : ℚ), ((-1 : ℚ) / 2), (0 : ℚ)], ![((-1 : ℚ) / 2), ((1 : ℚ) / 2), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (0 : ℚ)]] }, { constCoeff := (0 : ℚ),   valueCoeff := ![(-1 : ℚ), (0 : ℚ), (1 : ℚ), (0 : ℚ)],   gramCoeff := ![![(0 : ℚ), (0 : ℚ), ((-1 : ℚ) / 2)], ![(0 : ℚ), (0 : ℚ), ((1 : ℚ) / 2)], ![((-1 : ℚ) / 2), ((1 : ℚ) / 2), ((1 : ℚ) / 2)]] }, { constCoeff := (0 : ℚ),   valueCoeff := ![(1 : ℚ), (-1 : ℚ), (0 : ℚ), (0 : ℚ)],   gramCoeff := ![![(0 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), ((1 : ℚ) / 2), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (0 : ℚ)]] }, { constCoeff := (0 : ℚ),   valueCoeff := ![(0 : ℚ), (-1 : ℚ), (1 : ℚ), (0 : ℚ)],   gramCoeff := ![![(0 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), ((1 : ℚ) / 2), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), ((1 : ℚ) / 2)]] }, { constCoeff := (0 : ℚ),   valueCoeff := ![(1 : ℚ), (0 : ℚ), (-1 : ℚ), (0 : ℚ)],   gramCoeff := ![![(0 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), ((1 : ℚ) / 2)]] }, { constCoeff := (0 : ℚ),   valueCoeff := ![(0 : ℚ), (1 : ℚ), (-1 : ℚ), (0 : ℚ)],   gramCoeff := ![![(0 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), ((-1 : ℚ) / 2), ((-1 : ℚ) / 2)], ![(0 : ℚ), ((-1 : ℚ) / 2), ((1 : ℚ) / 2)]] }], labels := [(0,0,0),(1,0,0),(2,0,1),(2,0,2),(2,1,0),(2,1,2),(2,2,0),(2,2,1)], metric := { constCoeff := (0 : ℚ),   valueCoeff := ![(-1 : ℚ), (0 : ℚ), (1 : ℚ), (0 : ℚ)],   gramCoeff := ![![(0 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (0 : ℚ)]] }, objective := { constCoeff := (0 : ℚ),   valueCoeff := ![(0 : ℚ), (0 : ℚ), (0 : ℚ), (1 : ℚ)],   gramCoeff := ![![(0 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (0 : ℚ)]] }, steps := 1, stepSize := 1 }

def traceQ : TraceQ := {bound := ((208333333336233 : ℚ) / 1250000000000000), multipliers := [((10000000000047669 : ℚ) / 10000000000000000),((208333333336233 : ℚ) / 1250000000000000),((3443700654963083 : ℚ) / 10000000000000000),((327814967265223 : ℚ) / 500000000000000),((9081341948518489 : ℚ) / 1000000000000000000000000000),((6556310175716147 : ℚ) / 10000000000000000),((17707068559743983 : ℚ) / 1000000000000000000000000000),((1556304760421849 : ℚ) / 5000000000000000)], residual := ![![((8333333333434277 : ℚ) / 50000000000000000), ((-8609251637286963 : ℚ) / 50000000000000000), ((-3278149672628081 : ℚ) / 10000000000000000)], ![((-8609251637286963 : ℚ) / 50000000000000000), ((3443700654959493 : ℚ) / 10000000000000000), ((17218449122304477 : ℚ) / 100000000000000000)], ![((-3278149672628081 : ℚ) / 10000000000000000), ((17218449122304477 : ℚ) / 100000000000000000), ((8112609520969121 : ℚ) / 10000000000000000)]]}

def policyQ : PolicyQ := {maxDenominator := 1000000, maxAbsError := 1/1000000}

def rawUpperQ : UpperCertQ nativeModelQ := { bound := ((208333333336233 : ℚ) / 1250000000000000), objective := { constCoeff := (0 : ℚ),   valueCoeff := ![(0 : ℚ), (0 : ℚ), (0 : ℚ), (1 : ℚ)],   gramCoeff := ![![(0 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (0 : ℚ)]] }, interpTerms := [], assumptionTerms := [{ weight := ((10000000000047669 : ℚ) / 10000000000000000), index := ⟨0, by decide +kernel⟩ }, { weight := ((208333333336233 : ℚ) / 1250000000000000), index := ⟨1, by decide +kernel⟩ }, { weight := ((3443700654963083 : ℚ) / 10000000000000000), index := ⟨2, by decide +kernel⟩ }, { weight := ((327814967265223 : ℚ) / 500000000000000), index := ⟨3, by decide +kernel⟩ }, { weight := ((9081341948518489 : ℚ) / 1000000000000000000000000000), index := ⟨4, by decide +kernel⟩ }, { weight := ((6556310175716147 : ℚ) / 10000000000000000), index := ⟨5, by decide +kernel⟩ }, { weight := ((17707068559743983 : ℚ) / 1000000000000000000000000000), index := ⟨6, by decide +kernel⟩ }, { weight := ((1556304760421849 : ℚ) / 5000000000000000), index := ⟨7, by decide +kernel⟩ }], dualMatrix := ![![((8333333333434277 : ℚ) / 50000000000000000), ((-8609251637286963 : ℚ) / 50000000000000000), ((-3278149672628081 : ℚ) / 10000000000000000)], ![((-8609251637286963 : ℚ) / 50000000000000000), ((3443700654959493 : ℚ) / 10000000000000000), ((17218449122304477 : ℚ) / 100000000000000000)], ![((-3278149672628081 : ℚ) / 10000000000000000), ((17218449122304477 : ℚ) / 100000000000000000), ((8112609520969121 : ℚ) / 10000000000000000)]], dualFactor := {factors := []} }

def structuredUpperQ : UpperCertQ nativeModelQ := { bound := ((83333 : ℚ) / 499997), objective := { constCoeff := (0 : ℚ),   valueCoeff := ![(0 : ℚ), (0 : ℚ), (0 : ℚ), (1 : ℚ)],   gramCoeff := ![![(0 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (0 : ℚ), (0 : ℚ)]] }, interpTerms := [], assumptionTerms := [{ weight := (1 : ℚ), index := ⟨0, by decide +kernel⟩ }, { weight := ((83333 : ℚ) / 499997), index := ⟨1, by decide +kernel⟩ }, { weight := ((172184 : ℚ) / 499997), index := ⟨2, by decide +kernel⟩ }, { weight := ((327813 : ℚ) / 499997), index := ⟨3, by decide +kernel⟩ }, { weight := (0 : ℚ), index := ⟨4, by decide +kernel⟩ }, { weight := ((327814 : ℚ) / 499997), index := ⟨5, by decide +kernel⟩ }, { weight := (0 : ℚ), index := ⟨6, by decide +kernel⟩ }, { weight := ((155630 : ℚ) / 499997), index := ⟨7, by decide +kernel⟩ }], dualMatrix := ![![((83333 : ℚ) / 499997), ((-86092 : ℚ) / 499997), ((-327813 : ℚ) / 999994)], ![((-86092 : ℚ) / 499997), ((172184 : ℚ) / 499997), ((172183 : ℚ) / 999994)], ![((-327813 : ℚ) / 999994), ((172183 : ℚ) / 999994), ((811257 : ℚ) / 999994)]], dualFactor := {factors := [{ weight := ((83333 : ℚ) / 499997),   vector := ![(1 : ℚ), ((-86092 : ℚ) / 83333), ((-327813 : ℚ) / 166666)] }, { weight := ((6936776808 : ℚ) / 41666250001),   vector := ![(0 : ℚ), (1 : ℚ), ((-13873550857 : ℚ) / 13873553616)] }, { weight := ((41620577515 : ℚ) / 13873470374678304),   vector := ![(0 : ℚ), (0 : ℚ), (1 : ℚ)] }]} } 
theorem source_check : checkSourceQ sourceQ = true := by decide +kernel
#print axioms source_check
theorem raw_check : checkRawQ sourceQ traceQ rawUpperQ = true := by decide +kernel
#print axioms raw_check
theorem policy_check : checkChangesQ policyQ rawUpperQ structuredUpperQ = true := by decide +kernel
#print axioms policy_check
theorem psd_check : checkPSDFactorQ structuredUpperQ.dualMatrix structuredUpperQ.dualFactor = true := by decide +kernel
#print axioms psd_check
theorem upper_check : checkUpperCertQ structuredUpperQ = true := by decide +kernel
#print axioms upper_check
theorem centered_check : checkUpperCertQ (centered structuredUpperQ) = true := by decide +kernel
#print axioms centered_check
theorem tau_rhs_transport : checkLinearExprEqQ (eraseTau (certificateRhsExprQ structuredUpperQ)) (certificateRhsExprQ (centered structuredUpperQ)) = true := by decide +kernel
#print axioms tau_rhs_transport
theorem tau_target_transport : checkLinearExprEqQ (eraseTau (upperTargetExprQ structuredUpperQ.bound structuredUpperQ.objective)) (upperTargetExprQ (centered structuredUpperQ).bound (centered structuredUpperQ).objective) = true := by decide +kernel
#print axioms tau_target_transport
theorem accepted_check : checkAcceptedQ sourceQ traceQ policyQ rawUpperQ structuredUpperQ = true := by decide +kernel
#print axioms accepted_check
theorem bound_exact : structuredUpperQ.bound = ((83333 : ℚ) / 499997) := rfl
theorem actual_upper {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {L : ℝ≥0} {R : ℝ} {f : E → ℝ} {g : E → E} {xStar x0 x1 : E}
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar ≤ f y) (hstep : x1 = x0-(L : ℝ)⁻¹ • g x0)
    (hradius : ‖x0-xStar‖^2 ≤ R^2) :
    f x1-f xStar ≤ (L : ℝ)*R^2*(structuredUpperQ.bound : ℝ) :=
  GDOneCapture.upper_analytic sourceQ traceQ policyQ rawUpperQ structuredUpperQ accepted_check
    hf hL hR hmin hstep hradius
#print axioms actual_upper
#print axioms GDOneCapture.tau_substitution
#print axioms GDOneCapture.stationary_of_min
end LeanPEP.Imported.GDOneStructured003
