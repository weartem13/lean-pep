import LeanPEP.Toy.TwoStep.Upper

/-!
# Exact value of the normalized two-step finite PEP

The generic rational checker supplies an exact feasible witness with value
`1 / 10`, while `twoStep_upper` proves that no feasible real finite datum can
exceed it.
-/

namespace LeanPEP
namespace Toy
namespace TwoStep

/-- Attainable final values for the normalized two-step finite PEP. -/
def pepValues : Set ℝ :=
  {v | ∃ d : TwoStepData, FiniteGD.Feasible d ∧ v = d.value 2}

/-- Every attainable two-step value is at most `1 / 10`. -/
theorem twoStep_all_values_le :
    ∀ v ∈ pepValues, v ≤ (1 : ℝ) / 10 := by
  intro v hv
  rcases hv with ⟨d, hd, rfl⟩
  exact twoStep_upper d hd

/-- The value `1 / 10` is attained by the exact witness. -/
theorem twoStep_value_attained :
    ((1 : ℝ) / 10) ∈ pepValues := by
  refine ⟨exactWitness, exactWitness_feasible, ?_⟩
  exact exactWitness_value.symm

/-- The exact normalized two-step finite PEP value is `1 / 10`. -/
theorem twoStep_exact_value :
    IsGreatest pepValues ((1 : ℝ) / 10) := by
  exact ⟨twoStep_value_attained, twoStep_all_values_le⟩

end TwoStep
end Toy
end LeanPEP
