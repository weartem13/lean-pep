import LeanPEP.Toy.OneStep.Data

/-!
# Exact lower witness for the normalized one-dimensional one-step finite PEP

This file proves feasibility of the datum attaining value `1 / 6`.
-/

namespace LeanPEP
namespace Toy
namespace OneStep

/-- Exact datum attaining the one-step finite PEP value. -/
noncomputable def exactWitness : OneStepData :=
  { g0 := (1 : ℝ) / 3
    g1 := (1 : ℝ) / 3
    f0 := (5 : ℝ) / 18
    f1 := (1 : ℝ) / 6 }

/-- The exact witness satisfies every pairwise interpolation inequality. -/
theorem exactWitness_feasible :
    OneStepFeasible exactWitness := by
  constructor
  intro i j
  cases i <;> cases j <;>
    norm_num [slack, x, grad, val, exactWitness]

/-- The exact witness has objective value `1 / 6`. -/
theorem exactWitness_value :
    exactWitness.f1 = (1 : ℝ) / 6 := by
  norm_num [exactWitness]

end OneStep
end Toy
end LeanPEP
