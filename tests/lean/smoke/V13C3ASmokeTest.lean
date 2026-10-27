import LeanPEP

open LeanPEP
open LeanPEP.GramPEP
open LeanPEP.Profiles.ProximalGradientCertificate

#check boundQ_pos
#check smoothStarWeightQ_nonneg
#check smoothChainWeightQ_nonneg
#check nonsmoothStarWeightQ_nonneg
#check nonsmoothChainWeightQ_nonneg
#check pivotNumeratorQ_pos
#check mixedWeightQ_nonneg
#check gradientDifferenceWeightQ_nonneg
#check assumptionTermsQ_nonneg
#check dualFactorsQ_nonneg
#check dualValidQ_all
#check upperCertQ_check_iff_identity
#check upperCertQ_check_one
#check upperCertQ_check_two
#check upperCertQ_check_three
#check upperCertQ_check_four
#check upperCertQ_check_small
#check ActualFunction.ProximalGradientWitness.nonsmooth_convex
#check ActualFunction.ProximalGradientWitness.star_subgradient
#check ActualFunction.ProximalGradientWitness.witnessPoint_nonneg
#check ActualFunction.ProximalGradientWitness.residual_value
#check ActualFunction.ProximalGradientWitness.actual_run
#check ActualFunction.ProximalGradientWitness.attains
#check ActualFunction.ProximalGradientWitness.bound_mem_analyticValues
#check ActualFunction.ProximalGradientWitness.bound_mem_finiteValues
#check ActualFunction.ProximalGradientWitness.bound_le_any_upper
#check ActualFunction.ProximalGradientRate.upper_analytic_of_check
#check ActualFunction.ProximalGradientRate.upper_analytic_small
#check ActualFunction.ProximalGradientRate.finite_tight_small
#check ActualFunction.ProximalGradientRate.analytic_tight_small
#check ActualFunction.ProximalGradientRate.analytic_upper_and_oneDimensional_tight

-- All-horizon facts must retain symbolic n, rather than just numerical cases.
example (n : ℕ) : 0 < boundQ n := boundQ_pos n
example (n : ℕ) : (dualFactorsQ n).length = 3 * (n + 1) + 1 := dualFactorsQ_count n
example (n : ℕ) : (assumptionTermsQ n).length = 4 * (n + 1) + 1 := assumptionTermsQ_count n
example (n : ℕ) : checkUpperCertQ (upperCertQ n) = true ↔ CertificateIdentityQ n :=
  upperCertQ_check_iff_identity n

example : checkUpperCertQ (upperCertQ 1) = true := upperCertQ_check_two
example : checkUpperCertQ (upperCertQ 3) = true := upperCertQ_check_four
example : checkUpperCertQ wrongTwoStepBoundQ = false := wrongTwoStepBoundQ_rejected
example : checkUpperCertQ wrongTwoStepObjectiveQ = false := wrongTwoStepObjectiveQ_rejected

example (n : ℕ) : (boundQ n : ℝ) ∈
    ActualFunction.ProximalGradient.oneDimensionalAnalyticValues n :=
  ActualFunction.ProximalGradientWitness.bound_mem_analyticValues n

example : IsGreatest (ActualFunction.ProximalGradient.oneDimensionalAnalyticValues 1)
    ((1 : ℝ) / 8) := ActualFunction.ProximalGradientRate.twoStep_analytic_tight

example : IsGreatest (ActualFunction.ProximalGradient.oneDimensionalAnalyticValues 3)
    ((1 : ℝ) / 16) := ActualFunction.ProximalGradientRate.fourStep_analytic_tight

-- Eight-step actual LOWER membership: no eight-step upper theorem is asserted.
example : (1 : ℝ) / 32 ∈ ActualFunction.ProximalGradient.oneDimensionalAnalyticValues 7 := by
  convert ActualFunction.ProximalGradientWitness.bound_mem_analyticValues 7 using 1 <;>
    norm_num [boundQ]

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : ActualFunction.IsOneSmoothConvexAnalytic f g) (hh : ConvexOn ℝ Set.univ h)
    (hs : ActualFunction.Proximal.SubgradientAt h (-g xStar) xStar)
    (hrun : ActualFunction.ProximalGradient.IsProxRun 2 h g x)
    (hradius : ‖x 0 - xStar‖ ^ 2 ≤ 1) :
    f (x 2) + h (x 2) - (f xStar + h xStar) ≤ (1 : ℝ) / 8 := by
  have hb := ActualFunction.ProximalGradientRate.upper_analytic_small 1 (by omega)
    hf hh hs hrun hradius
  norm_num at hb ⊢
  exact hb

#print axioms LeanPEP.Profiles.ProximalGradientCertificate.dualValidQ_all
#print axioms LeanPEP.Profiles.ProximalGradientCertificate.upperCertQ_check_four
#print axioms LeanPEP.ActualFunction.ProximalGradientWitness.actual_run
#print axioms LeanPEP.ActualFunction.ProximalGradientWitness.attains
#print axioms LeanPEP.ActualFunction.ProximalGradientRate.upper_analytic_small
#print axioms LeanPEP.ActualFunction.ProximalGradientRate.analytic_tight_small
