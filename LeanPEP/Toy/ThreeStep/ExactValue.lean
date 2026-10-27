import LeanPEP.Toy.ThreeStep.Upper

/-!
# Exact value of the normalized three-step finite PEP

The generic rational primal checker accepts an exact witness with final value
`1 / 14`, and the generic upper-certificate checker proves that every feasible
real finite datum has final value at most `1 / 14`.
-/

namespace LeanPEP
namespace Toy
namespace ThreeStep

/-- Attainable final values for the normalized three-step finite PEP. -/
def pepValues : Set ℝ :=
  {v | ∃ d : ThreeStepData, FiniteGD.Feasible d ∧ v = d.value 3}

/-- Every attainable three-step value is at most `1 / 14`. -/
theorem threeStep_all_values_le :
    ∀ v ∈ pepValues, v ≤ (1 : ℝ) / 14 := by
  intro v hv
  rcases hv with ⟨d, hd, rfl⟩
  exact threeStep_upper d hd

/-- The value `1 / 14` is attained by the exact witness. -/
theorem threeStep_value_attained :
    ((1 : ℝ) / 14) ∈ pepValues := by
  refine ⟨exactWitness, exactWitness_feasible, ?_⟩
  exact exactWitness_value.symm

/-- The exact normalized three-step finite PEP value is `1 / 14`. -/
theorem threeStep_exact_value :
    IsGreatest pepValues ((1 : ℝ) / 14) := by
  exact ⟨threeStep_value_attained, threeStep_all_values_le⟩

end ThreeStep
end Toy
end LeanPEP
