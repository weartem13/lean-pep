import LeanPEP

open LeanPEP
open LeanPEP.GramPEP
open LeanPEP.Profiles.ProximalGradientCertificate
open scoped BigOperators

#check Profiles.Composite.rowMajorList_getElem?
#check smoothIndex_get
#check nonsmoothIndex_get
#check radiusIndex_get
#check smoothStarWeightQ_flow
#check nonsmoothStarWeightQ_flow
#check weighted_flux_sum
#check smooth_weighted_sum
#check nonsmooth_weighted_sum
#check smooth_value_balance
#check nonsmooth_value_balance
#check CoefficientAlgebra.coefficients_injective
#check CoefficientAlgebra.coefficients_factorGramQ
#check potentialQ_zero
#check potentialQ_last
#check local_weight_identities
#check local_scalar_identity
#check local_gram_identity
#check fin_telescope
#check smooth_component_balance
#check nonsmooth_component_balance
#check certificateIdentityQ_all
#check upperCertQ_check_all
#check upperCertQ_valid_all
#check ActualFunction.ProximalGradientRate.upper_all
#check ActualFunction.ProximalGradientRate.upper_analytic_all
#check ActualFunction.ProximalGradientRate.upper_analytic_steps
#check ActualFunction.ProximalGradientRate.finite_tight_all
#check ActualFunction.ProximalGradientRate.analytic_tight_all
#check ActualFunction.ProximalGradientRate.analytic_upper_and_oneDimensional_tight_all

-- Symbolic horizon: these are not a finite enumeration of checker evaluations.
example (n : ℕ) : CertificateIdentityQ n := certificateIdentityQ_all n
example (n : ℕ) : checkUpperCertQ (upperCertQ n) = true := upperCertQ_check_all n
example (n : ℕ) : UpperCertValidQ (upperCertQ n) := upperCertQ_valid_all n
example : checkUpperCertQ (upperCertQ 7) = true := upperCertQ_check_all 7
example : checkUpperCertQ (upperCertQ 15) = true := upperCertQ_check_all 15
example : checkUpperCertQ (upperCertQ 63) = true := upperCertQ_check_all 63

-- n=0 still means one step; there is no zero-step 1/(4T) claim.
example : IsGreatest (ActualFunction.ProximalGradient.oneDimensionalAnalyticValues 0)
    ((1 : ℝ) / 4) := by
  convert ActualFunction.ProximalGradientRate.analytic_tight_all 0 using 1 <;> norm_num
example : IsGreatest (ActualFunction.ProximalGradient.oneDimensionalAnalyticValues 7)
    ((1 : ℝ) / 32) := by
  convert ActualFunction.ProximalGradientRate.analytic_tight_all 7 using 1 <;> norm_num
example : IsGreatest (Profiles.ProximalGradient.finiteValues 63) ((1 : ℝ) / 256) := by
  convert ActualFunction.ProximalGradientRate.finite_tight_all 63 using 1 <;> norm_num

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : ℕ) (hT : 0 < T) {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : ActualFunction.IsOneSmoothConvexAnalytic f g) (hh : ConvexOn ℝ Set.univ h)
    (hs : ActualFunction.Proximal.SubgradientAt h (-g xStar) xStar)
    (hrun : ActualFunction.ProximalGradient.IsProxRun T h g x)
    (hR : ‖x 0 - xStar‖ ^ 2 ≤ 1) :
    f (x T) + h (x T) - (f xStar + h xStar) ≤ 1 / (4 * (T : ℝ)) :=
  ActualFunction.ProximalGradientRate.upper_analytic_steps T hT hf hh hs hrun hR

-- The old negative tests and witness remain in force.
example : checkUpperCertQ wrongTwoStepBoundQ = false := wrongTwoStepBoundQ_rejected
example : checkUpperCertQ wrongTwoStepObjectiveQ = false := wrongTwoStepObjectiveQ_rejected
example (n : ℕ) : (boundQ n : ℝ) ∈ ActualFunction.ProximalGradient.oneDimensionalAnalyticValues n :=
  ActualFunction.ProximalGradientWitness.bound_mem_analyticValues n

#print axioms Profiles.Composite.rowMajorList_getElem?
#print axioms local_gram_identity
#print axioms certificateIdentityQ_all
#print axioms upperCertQ_check_all
#print axioms ActualFunction.ProximalGradientRate.upper_analytic_steps
#print axioms ActualFunction.ProximalGradientRate.analytic_tight_all
