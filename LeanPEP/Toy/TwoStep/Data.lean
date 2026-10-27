import LeanPEP.Toy.FiniteGD.RationalBridge

/-!
# Normalized one-dimensional two-step finite PEP data

This file instantiates the generic finite-gradient-descent semantics at `N = 2`.
The exact witness is the constant-gradient Huber-type finite datum

`g₀ = g₁ = g₂ = 1/5`,
`f₀ = 9/50`, `f₁ = 7/50`, `f₂ = 1/10`.
-/

namespace LeanPEP
namespace Toy
namespace TwoStep

abbrev Pt := FiniteGD.Point 2
abbrev TwoStepData := FiniteGD.DataR 2
abbrev TwoStepDataQ := FiniteGD.DataQ 2

/-- Optimum point. -/
def star : Pt := FiniteGD.Point.star

/-- Initial iterate. -/
def p0 : Pt := FiniteGD.Point.iter 0

/-- First gradient-descent iterate. -/
def p1 : Pt := FiniteGD.Point.iter 1

/-- Second gradient-descent iterate. -/
def p2 : Pt := FiniteGD.Point.iter 2


@[simp] theorem x_p0 (d : FiniteGD.Data 2 ℝ) :
    FiniteGD.x d p0 = 1 := by
  simp [p0, FiniteGD.x, FiniteGD.iterX, FiniteGD.prefixSum]

@[simp] theorem x_p1 (d : FiniteGD.Data 2 ℝ) :
    FiniteGD.x d p1 = 1 - d.grad 0 := by
  simp [p1, FiniteGD.x, FiniteGD.iterX, FiniteGD.prefixSum]

@[simp] theorem x_p2 (d : FiniteGD.Data 2 ℝ) :
    FiniteGD.x d p2 = 1 - d.grad 0 - d.grad 1 := by
  simp [p2, FiniteGD.x, FiniteGD.iterX, FiniteGD.prefixSum]
  ring

@[simp] theorem gradAt_p0 (d : FiniteGD.Data 2 ℝ) :
    FiniteGD.gradAt d p0 = d.grad 0 := by
  rfl

@[simp] theorem gradAt_p1 (d : FiniteGD.Data 2 ℝ) :
    FiniteGD.gradAt d p1 = d.grad 1 := by
  rfl

@[simp] theorem gradAt_p2 (d : FiniteGD.Data 2 ℝ) :
    FiniteGD.gradAt d p2 = d.grad 2 := by
  rfl

@[simp] theorem valueAt_p0 (d : FiniteGD.Data 2 ℝ) :
    FiniteGD.valueAt d p0 = d.value 0 := by
  rfl

@[simp] theorem valueAt_p1 (d : FiniteGD.Data 2 ℝ) :
    FiniteGD.valueAt d p1 = d.value 1 := by
  rfl

@[simp] theorem valueAt_p2 (d : FiniteGD.Data 2 ℝ) :
    FiniteGD.valueAt d p2 = d.value 2 := by
  rfl

/-- Exact rational datum attaining the two-step value `1 / 10`. -/
def exactWitnessQ : TwoStepDataQ :=
  { grad := ![(1 : ℚ) / 5, (1 : ℚ) / 5, (1 : ℚ) / 5]
    value := ![(9 : ℚ) / 50, (7 : ℚ) / 50, (1 : ℚ) / 10] }

/-- A deliberately invalid two-step candidate for generated-audit tests. -/
def badCandidateQ : TwoStepDataQ :=
  { grad := ![0, 0, 0]
    value := ![0, 0, (1 : ℚ) / 5] }

/-- The generic point-pair generator creates all sixteen ordered constraints. -/
theorem twoStep_pointPair_count :
    (FiniteGD.pointPairs 2).length = 16 := by
  native_decide

/-- The generated checker accepts the exact rational witness. -/
theorem exactWitnessQ_check :
    FiniteGD.checkFeasibleQ exactWitnessQ = true := by
  native_decide

/-- The generated checker rejects the deliberately invalid candidate. -/
theorem badCandidateQ_check :
    FiniteGD.checkFeasibleQ badCandidateQ = false := by
  native_decide

/-- Real copy of the exact rational witness. -/
noncomputable def exactWitness : TwoStepData :=
  FiniteGD.toRealData exactWitnessQ

/-- Checker acceptance reconstructs real finite PEP feasibility. -/
theorem exactWitness_feasible :
    FiniteGD.Feasible exactWitness := by
  simpa [exactWitness] using
    FiniteGD.checkFeasibleQ_sound_real exactWitnessQ exactWitnessQ_check

/-- The rational witness has final objective value `1 / 10`.

This small lemma isolates evaluation of the finite vector at index `2`, so the
real-valued theorem below does not depend on simplifier support for vector
notation. -/
@[simp] theorem exactWitnessQ_value :
    exactWitnessQ.value 2 = (1 : ℚ) / 10 := by
  native_decide

/-- The exact real witness has final objective value `1 / 10`. -/
theorem exactWitness_value :
    exactWitness.value 2 = (1 : ℝ) / 10 := by
  change ((exactWitnessQ.value 2 : ℚ) : ℝ) = (1 : ℝ) / 10
  rw [exactWitnessQ_value]
  norm_num

end TwoStep
end Toy
end LeanPEP
