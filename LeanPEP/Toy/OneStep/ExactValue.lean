import LeanPEP.Toy.OneStep.Upper
import LeanPEP.Toy.OneStep.Lower

/-!
# Exact value of the normalized one-dimensional one-step finite PEP

The feasible objective values have greatest element `1 / 6`.
-/

namespace LeanPEP
namespace Toy
namespace OneStep

/-- The set of finite one-step PEP objective values. -/
def pepValues : Set ℝ :=
  { v | ∃ d : OneStepData, OneStepFeasible d ∧ v = d.f1 }

/-- Every finite feasible value is at most `1 / 6`. -/
theorem oneStep_all_values_le :
    ∀ v ∈ pepValues, v ≤ (1 : ℝ) / 6 := by
  intro v hv
  rcases hv with ⟨d, hd, hv_eq⟩
  rw [hv_eq]
  exact oneStep_upper d hd

/-- The value `1 / 6` is attained by the exact witness. -/
theorem oneStep_value_attained :
    ((1 : ℝ) / 6) ∈ pepValues := by
  refine ⟨exactWitness, exactWitness_feasible, ?_⟩
  norm_num [exactWitness]

/-- The exact value of the finite one-step PEP is `1 / 6`. -/
theorem oneStep_exact_value :
    IsGreatest pepValues ((1 : ℝ) / 6) := by
  constructor
  · exact oneStep_value_attained
  · intro v hv
    exact oneStep_all_values_le v hv

end OneStep
end Toy
end LeanPEP
