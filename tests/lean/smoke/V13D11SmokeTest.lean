import LeanPEP

open scoped NNReal BigOperators
open LeanPEP LeanPEP.GramPEP
open LeanPEP.GramPEP.RationalBoxSystem

#check checkFeasibleQ_eq_true_iff
#check checkObstructionQ_eq_true_iff
#check margin_eq_slacks
#check obstruction_not_feasible
#check checked_obstruction
#check policy_interval_iff
#check policy_box_iff
#check Imported.CompositeBoundedCompletion.PGOne.raw_vector_check
#check Imported.CompositeBoundedCompletion.PGOne.completion_vector_check
#check Imported.CompositeBoundedCompletion.PGOne.negative_free_seed
#check Imported.CompositeBoundedCompletion.PGOne.free_seed_rejected
#check Imported.CompositeBoundedCompletion.PGOne.free_variable_repaired
#check Imported.CompositeBoundedCompletion.PGThree.box_bounds_check
#check Imported.CompositeBoundedCompletion.PGThree.box_feasible_check
#check Imported.CompositeBoundedCompletion.PGThree.completed_check
#check Imported.CompositeBoundedCompletion.Budget.affine_certificate_valid
#check Imported.CompositeBoundedCompletion.Budget.no_box_solution
#check Imported.CompositeBoundedCompletion.coupled_repaired
#check Imported.CompositeBoundedCompletion.impossible_no_solution
#check Imported.CompositeBoundedCompletion.third_denominator_rejected
#check ActualFunction.ProximalGradientCompletionAudit.upper_analytic
#check ActualFunction.ProximalGradientBoundedCompletionAudit.three_step_upper

example : checkFeasibleQ (⟨⟨![], ![]⟩, ![], ![]⟩ : BoxQ 0 0) ![] = true := by
  decide +kernel
example : checkObstructionQ (⟨⟨![![]], ![1]⟩, ![], ![]⟩ : BoxQ 1 0)
    (⟨![-1], ![], ![]⟩ : ObstructionQ 1 0) = true := by
  decide +kernel
example : checkObstructionQ (⟨⟨![], ![]⟩, ![2], ![1]⟩ : BoxQ 0 1)
    (⟨![], ![1], ![1]⟩ : ObstructionQ 0 1) = true := by
  decide +kernel
example : checkFeasibleQ Imported.CompositeBoundedCompletion.coupledQ ![1,0] = true :=
  Imported.CompositeBoundedCompletion.coupled_repaired
example : ¬ ∃ x, FeasibleQ Imported.CompositeBoundedCompletion.Budget.boxQ x :=
  Imported.CompositeBoundedCompletion.Budget.no_box_solution
example : Imported.CompositeBoundedCompletion.PGThree.completedUpperQ.bound = 1/12 := by
  decide +kernel
example : Imported.CompositeBoundedCompletion.PGOne.completionVectorQ 11 = 0 :=
  Imported.CompositeBoundedCompletion.PGOne.free_variable_repaired
example {r c : ℕ} (s : RationalLinearSystem.SystemQ r c) (raw x : Fin c → ℚ)
    (eta : ℚ) (mask : Fin c → Bool) :
    FeasibleQ
      { system := s
        lower := policyLowerQ raw eta mask
        upper := policyUpperQ raw eta } x ↔
      RationalLinearSystem.IsSolutionQ s x ∧
        ∀ j, |x j - raw j| ≤ eta ∧ (mask j = true → 0 ≤ x j) :=
  policy_box_iff s raw x eta mask

section Actual
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {L : ℝ≥0} {R : ℝ} {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
example (hf : ActualFunction.IsSmoothConvexAnalytic L f g) (hh : ConvexOn ℝ Set.univ h)
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar + h xStar ≤ f y + h y)
    (hrun : ActualFunction.ProximalGradientScaling.IsSmoothProxRun 3 L h g x)
    (hradius : ‖x 0 - xStar‖ ^ 2 ≤ R ^ 2) :
    f (x 3) + h (x 3) - (f xStar + h xStar) ≤ (L : ℝ) * R ^ 2 / 12 :=
  ActualFunction.ProximalGradientBoundedCompletionAudit.three_step_upper hf hh hL hR hmin hrun hradius
end Actual

#print axioms margin_eq_slacks
#print axioms obstruction_not_feasible
#print axioms checked_obstruction
#print axioms policy_box_iff
#print axioms Imported.CompositeBoundedCompletion.Budget.no_box_solution
#print axioms Imported.CompositeBoundedCompletion.PGOne.free_seed_rejected
#print axioms Imported.CompositeBoundedCompletion.PGThree.completed_check
#print axioms ActualFunction.ProximalGradientBoundedCompletionAudit.three_step_upper
