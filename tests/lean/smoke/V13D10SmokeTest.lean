import LeanPEP

open scoped NNReal BigOperators
open LeanPEP LeanPEP.GramPEP
open LeanPEP.GramPEP.RationalLinearSystem
open LeanPEP.Adapters.ProximalGradientCompletion

#check checkSolutionQ_eq_true_iff
#check checkObstructionQ_eq_true_iff
#check obstruction_not_solution
#check checked_obstruction
#check checkFixedTargetsQ_eq_true_iff
#check checkCompletedQ_eq_true_iff
#check captured_check
#check residual_preserved
#check completion_within_raw_policy
#check checked_certificate
#check Imported.CompositeCompletion.PGOne.seed_rejected
#check Imported.CompositeCompletion.PGOne.fixed_targets_check
#check Imported.CompositeCompletion.PGTwo.completed_check
#check Imported.CompositeCompletion.PGThree.linear_solution_check
#check Imported.CompositeCompletion.Inconsistent.seed_psd_check
#check Imported.CompositeCompletion.Inconsistent.no_linear_solution
#check Imported.CompositeCompletion.changed_seed_within_policy
#check Imported.CompositeCompletion.changed_seed_fixed_rejected
#check ActualFunction.ProximalGradientCompletionAudit.upper_firstOrder
#check ActualFunction.ProximalGradientCompletionAudit.upper_analytic
#check ActualFunction.ProximalGradientCompletionAudit.three_step_upper

example : checkSolutionQ (⟨![], ![]⟩ : SystemQ 0 0) ![] = true := by decide +kernel
example : checkSolutionQ (⟨![![1, 2], ![3, 4]], ![5, 11]⟩ : SystemQ 2 2) ![1, 2] = true := by decide +kernel
example : checkSolutionQ (⟨![![1, 1]], ![3]⟩ : SystemQ 1 2) ![2, 1] = true := by decide +kernel
example : checkObstructionQ (⟨![![1], ![1]], ![1, 2]⟩ : SystemQ 2 1) ![-1, 1] = true := by decide +kernel
example : ¬ ∃ x, IsSolutionQ (⟨![![1], ![1]], ![1, 2]⟩ : SystemQ 2 1) x :=
  checked_obstruction _ ![-1, 1] (by decide +kernel)
example : checkSolutionQ Imported.CompositeCompletion.PGThree.coefficientSystemQ
    Imported.CompositeCompletion.PGThree.completionVectorQ = true :=
  Imported.CompositeCompletion.PGThree.linear_solution_check
example : Imported.CompositeCompletion.PGThree.completedUpperQ.bound = 1/12 := by decide +kernel
example : checkCompletedQ Imported.CompositeCompletion.PGOne.sourceQ Imported.CompositeCompletion.PGOne.traceQ
    Imported.CompositeCompletion.PGOne.policyQ Imported.CompositeCompletion.PGOne.rawUpperQ
    Imported.CompositeCompletion.PGOne.reconstructedUpperQ Imported.CompositeCompletion.PGOne.completedUpperQ = true :=
  Imported.CompositeCompletion.PGOne.completed_check

section Actual
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {L : ℝ≥0} {R : ℝ} {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
example (hf : ActualFunction.IsSmoothConvexAnalytic L f g) (hh : ConvexOn ℝ Set.univ h)
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar + h xStar ≤ f y + h y)
    (hrun : ActualFunction.ProximalGradientScaling.IsSmoothProxRun 3 L h g x)
    (hradius : ‖x 0 - xStar‖ ^ 2 ≤ R ^ 2) :
    f (x 3) + h (x 3) - (f xStar + h xStar) ≤ (L : ℝ) * R ^ 2 / 12 :=
  ActualFunction.ProximalGradientCompletionAudit.three_step_upper hf hh hL hR hmin hrun hradius
end Actual

#print axioms obstruction_not_solution
#print axioms checked_obstruction
#print axioms residual_preserved
#print axioms completion_within_raw_policy
#print axioms checked_certificate
#print axioms Imported.CompositeCompletion.Inconsistent.no_linear_solution
#print axioms Imported.CompositeCompletion.PGThree.completed_check
#print axioms ActualFunction.ProximalGradientCompletionAudit.three_step_upper
