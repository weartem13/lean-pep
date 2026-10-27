import LeanPEP

#check LeanPEP.ActualFunction.ParametricGDHilbert.linearCombination
#check LeanPEP.ActualFunction.ParametricGDHilbert.evalVector
#check LeanPEP.ActualFunction.ParametricGDHilbert.evalHilbert
#check LeanPEP.ActualFunction.ParametricGDHilbert.evalHilbert_slackPolyQ
#check LeanPEP.ActualFunction.ParametricGDHilbert.upperCertValidQ_sound
#check LeanPEP.ActualFunction.ParametricGDHilbert.gd_upper
#check LeanPEP.ActualFunction.ParametricGDHilbert.gd_upper_normSq

namespace LeanPEP.ActualFunction.V12C1Smoke

open LeanPEP.Toy.FiniteGD
open LeanPEP.Toy.FiniteGD.ParametricUpper
open LeanPEP.ActualFunction.ParametricGDHilbert

/-- The abstract Hilbert theorem applies to the zero trajectory at arbitrary
length. -/
example (N : ℕ) :
    let grad : Fin (N + 1) → ℝ := fun _ => 0
    let value : Fin (N + 1) → ℝ := fun _ => 0
    value (gdObjective N) ≤
      (gdBoundQ N : ℝ) * ‖(0 : ℝ)‖ ^ 2 := by
  let grad : Fin (N + 1) → ℝ := fun _ => 0
  let value : Fin (N + 1) → ℝ := fun _ => 0
  have hfeasible : ParametricGDHilbert.Feasible (0 : ℝ) grad value := by
    intro i j
    cases i <;> cases j <;>
      simp [ParametricGDHilbert.interpolationSlack,
        ParametricGDHilbert.pointValue,
        ParametricGDHilbert.pointGradient,
        ParametricGDHilbert.pointPosition,
        ParametricGDHilbert.prefixVector, grad, value]
  exact ParametricGDHilbert.gd_upper_normSq N (0 : ℝ) grad value hfeasible

end LeanPEP.ActualFunction.V12C1Smoke
