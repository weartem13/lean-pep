import LeanPEP.Toy.FiniteGD.RationalBridge

/-!
# Normalized one-dimensional three-step finite PEP data

This file instantiates the generic finite-gradient-descent semantics at `N = 3`.
The exact candidate witness is

`g₀ = g₁ = g₂ = g₃ = 1/7`,
`f₀ = 13/98`, `f₁ = 11/98`, `f₂ = 9/98`, `f₃ = 1/14`.
-/

namespace LeanPEP
namespace Toy
namespace ThreeStep

abbrev Pt := FiniteGD.Point 3
abbrev ThreeStepData := FiniteGD.DataR 3
abbrev ThreeStepDataQ := FiniteGD.DataQ 3

/-- Optimum point. -/
def star : Pt := FiniteGD.Point.star

/-- Initial iterate. -/
def p0 : Pt := FiniteGD.Point.iter 0

/-- First gradient-descent iterate. -/
def p1 : Pt := FiniteGD.Point.iter 1

/-- Second gradient-descent iterate. -/
def p2 : Pt := FiniteGD.Point.iter 2

/-- Third gradient-descent iterate. -/
def p3 : Pt := FiniteGD.Point.iter 3

@[simp] theorem x_p0 (d : FiniteGD.Data 3 ℝ) :
    FiniteGD.x d p0 = 1 := by
  simp [p0, FiniteGD.x, FiniteGD.iterX, FiniteGD.prefixSum]

@[simp] theorem x_p1 (d : FiniteGD.Data 3 ℝ) :
    FiniteGD.x d p1 = 1 - d.grad 0 := by
  simp [p1, FiniteGD.x, FiniteGD.iterX, FiniteGD.prefixSum]

@[simp] theorem x_p2 (d : FiniteGD.Data 3 ℝ) :
    FiniteGD.x d p2 = 1 - d.grad 0 - d.grad 1 := by
  simp [p2, FiniteGD.x, FiniteGD.iterX, FiniteGD.prefixSum]
  ring

@[simp] theorem x_p3 (d : FiniteGD.Data 3 ℝ) :
    FiniteGD.x d p3 = 1 - d.grad 0 - d.grad 1 - d.grad 2 := by
  simp [p3, FiniteGD.x, FiniteGD.iterX, FiniteGD.prefixSum]
  ring

/-- Exact rational datum attaining the candidate three-step value `1 / 14`. -/
def exactWitnessQ : ThreeStepDataQ :=
  { grad :=
      ![(1 : ℚ) / 7, (1 : ℚ) / 7, (1 : ℚ) / 7, (1 : ℚ) / 7]
    value :=
      ![(13 : ℚ) / 98, (11 : ℚ) / 98, (9 : ℚ) / 98, (1 : ℚ) / 14] }

/-- The generic point-pair generator creates all twenty-five ordered constraints. -/
theorem threeStep_pointPair_count :
    (FiniteGD.pointPairs 3).length = 25 := by
  native_decide

/-- The generated checker accepts the exact rational witness. -/
theorem exactWitnessQ_check :
    FiniteGD.checkFeasibleQ exactWitnessQ = true := by
  native_decide

/-- Real copy of the exact rational witness. -/
noncomputable def exactWitness : ThreeStepData :=
  FiniteGD.toRealData exactWitnessQ

/-- Checker acceptance reconstructs real finite PEP feasibility. -/
theorem exactWitness_feasible :
    FiniteGD.Feasible exactWitness := by
  simpa [exactWitness] using
    FiniteGD.checkFeasibleQ_sound_real exactWitnessQ exactWitnessQ_check

/-- The rational witness has final objective value `1 / 14`. -/
@[simp] theorem exactWitnessQ_value :
    exactWitnessQ.value 3 = (1 : ℚ) / 14 := by
  native_decide

/-- The exact real witness has final objective value `1 / 14`. -/
theorem exactWitness_value :
    exactWitness.value 3 = (1 : ℝ) / 14 := by
  change ((exactWitnessQ.value 3 : ℚ) : ℝ) = (1 : ℝ) / 14
  rw [exactWitnessQ_value]
  norm_num

end ThreeStep
end Toy
end LeanPEP
