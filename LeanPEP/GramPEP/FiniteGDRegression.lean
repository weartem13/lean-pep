import LeanPEP.GramPEP.FiniteGD
import LeanPEP.Toy.FiniteGD.OneStepRegression
import LeanPEP.Toy.TwoStep.Data
import LeanPEP.Toy.ThreeStep.Data

/-!
# Regression of the verified one-dimensional witnesses through Gram semantics

These theorems ensure that the exact `N = 1`, `N = 2`, and `N = 3` rational
witnesses accepted by the existing scalar checker are also feasible in the new
one-dimensional Gram semantic core.  A known bad two-step candidate remains
infeasible after embedding.
-/

namespace LeanPEP
namespace GramPEP
namespace FiniteGDRegression

/-- Generic `N = 1` rational datum corresponding to the original witness. -/
def oneStepWitnessQ : LeanPEP.Toy.FiniteGD.DataQ 1 :=
  LeanPEP.Toy.FiniteGD.fromOneStepQ LeanPEP.Toy.OneStep.exactWitnessQ

/-- The verified one-step witness is feasible in the Gram semantic core. -/
theorem oneStepWitness_coreFeasible :
    CoreFeasible (ofFiniteGD oneStepWitnessQ) := by
  apply (coreFeasible_ofFiniteGD_iff oneStepWitnessQ).2
  apply LeanPEP.Toy.FiniteGD.checkFeasibleQ_sound
  simpa [oneStepWitnessQ] using
    LeanPEP.Toy.FiniteGD.oneStep_exactWitness_generic_check

/-- The verified two-step witness is feasible in the Gram semantic core. -/
theorem twoStepWitness_coreFeasible :
    CoreFeasible (ofFiniteGD LeanPEP.Toy.TwoStep.exactWitnessQ) := by
  apply (coreFeasible_ofFiniteGD_iff LeanPEP.Toy.TwoStep.exactWitnessQ).2
  exact LeanPEP.Toy.FiniteGD.checkFeasibleQ_sound LeanPEP.Toy.TwoStep.exactWitnessQ
    LeanPEP.Toy.TwoStep.exactWitnessQ_check

/-- The verified three-step witness is feasible in the Gram semantic core. -/
theorem threeStepWitness_coreFeasible :
    CoreFeasible (ofFiniteGD LeanPEP.Toy.ThreeStep.exactWitnessQ) := by
  apply (coreFeasible_ofFiniteGD_iff LeanPEP.Toy.ThreeStep.exactWitnessQ).2
  exact LeanPEP.Toy.FiniteGD.checkFeasibleQ_sound LeanPEP.Toy.ThreeStep.exactWitnessQ
    LeanPEP.Toy.ThreeStep.exactWitnessQ_check

/-- Embedding does not repair an invalid scalar candidate. -/
theorem twoStepBadCandidate_notInterpolationFeasible :
    ¬ InterpolationFeasible (ofFiniteGD LeanPEP.Toy.TwoStep.badCandidateQ) := by
  intro h
  have hfeasible : LeanPEP.Toy.FiniteGD.Feasible LeanPEP.Toy.TwoStep.badCandidateQ :=
    (interpolationFeasible_ofFiniteGD_iff LeanPEP.Toy.TwoStep.badCandidateQ).mp h
  have hcheck : LeanPEP.Toy.FiniteGD.checkFeasibleQ LeanPEP.Toy.TwoStep.badCandidateQ = true :=
    LeanPEP.Toy.FiniteGD.checkFeasibleQ_complete LeanPEP.Toy.TwoStep.badCandidateQ hfeasible
  rw [LeanPEP.Toy.TwoStep.badCandidateQ_check] at hcheck
  simp at hcheck

end FiniteGDRegression
end GramPEP
end LeanPEP
