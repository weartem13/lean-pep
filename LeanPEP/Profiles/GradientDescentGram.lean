import LeanPEP.Profiles.GramCompilation
import LeanPEP.Profiles.GradientDescent
import LeanPEP.GramPEP.ExternalBundle
import LeanPEP.GramPEP.UpperCertificateExamples

/-!
# Gradient descent compiled to the general Gram-PEP model

This module instantiates the v0.13A2 Gram compiler with the exact unit-step GD
profile from v0.13A1, unit initial radius, and the final function-value gap.
For every horizon it produces the model with point order

```text
(x_star, x_0, ..., x_N)
```

and Gram-basis order

```text
(x_0 - x_star, g_0, ..., g_N).
```

At horizon `N = 1`, the generated model and objective are proved exactly equal
to the previously verified hand-written one-step Gram formulation.  Hence the
existing general Gram checker and its accepted exact certificate apply to the
compiler output without any checker change.
-/

namespace LeanPEP
namespace Profiles
namespace GradientDescentGram

open LeanPEP.Toy.FiniteGD
open LeanPEP.Profiles.FixedStepFirstOrder
open LeanPEP.Profiles.GradientDescent
open LeanPEP.Profiles.GramCompilation
open LeanPEP.GramPEP
open LeanPEP.GramPEP.UpperCertificateExamples

/-- Composed normalized unit-step GD PEP profile. -/
def unitGDGramProfileQ (N : ℕ) : PEPProfileQ N :=
  { algorithm := unitGDProfileQ N
    normalization := unitRadiusNormalizationQ
    objective := finalGapObjectiveProfileQ N }

/-- General Gram model generated from the unit-step GD profile. -/
def unitGDModelQ (N : ℕ) : ModelQ (N + 2) (N + 2) :=
  compileModelQ (unitGDGramProfileQ N)

/-- General Gram objective generated from the final-iterate gap profile. -/
def unitGDObjectiveQ (N : ℕ) : LinearExprQ (N + 2) (N + 2) :=
  compileObjectiveQ (unitGDGramProfileQ N)

/-- The generated GD positions are exactly the homogenized legacy scalar
positions, for every horizon and every source point. -/
@[simp] theorem unitGDModelQ_position_pointIndex
    {N : ℕ} (i : Point N) :
    (unitGDModelQ N).position (pointIndex i) =
      affineVecQ (xAffineQ i) := by
  change
    (compileModelQ (unitGDGramProfileQ N)).position (pointIndex i) =
      affineVecQ (xAffineQ i)
  rw [compileModelQ_position_pointIndex]
  change
    affineVecQ (pointAffineQ (unitGDProfileQ N) i) =
      affineVecQ (xAffineQ i)
  rw [pointAffineQ_unitGD]

/-- The generated gradients use the declared gradient-basis coordinates and a
zero stationary gradient at the optimum. -/
@[simp] theorem unitGDModelQ_gradient_pointIndex
    {N : ℕ} (i : Point N) :
    (unitGDModelQ N).gradient (pointIndex i) =
      pointGradientVecQ i := by
  exact compileModelQ_gradient_pointIndex (unitGDGramProfileQ N) i

/-- The coefficient of `g_j` in the compiled unit-step GD point `x_i` is `-1`
exactly for a strict predecessor and zero otherwise. -/
theorem unitGDModelQ_iter_gradient_coordinate
    {N : ℕ} (i j : Fin (N + 1)) :
    (unitGDModelQ N).position (pointIndex (Point.iter i))
        (gradientBasisIndex j) =
      if j.val < i.val then -1 else 0 := by
  rw [unitGDModelQ_position_pointIndex, affineVecQ_gradient]
  rw [← iterateAffineQ_unitGD, iterateAffineQ_gradCoeff]
  by_cases hji : j.val < i.val <;>
    simp [unitGDProfileQ_stepCoeff, hji]

/-- In particular, the general Gram compiler preserves the causality theorem. -/
theorem unitGDModelQ_iter_gradient_coordinate_of_le
    {N : ℕ} (i j : Fin (N + 1)) (hij : i.val ≤ j.val) :
    (unitGDModelQ N).position (pointIndex (Point.iter i))
        (gradientBasisIndex j) = 0 := by
  exact compileModelQ_iter_gradient_coordinate_of_le
    (unitGDGramProfileQ N) i j hij

/-- The generated objective is the final function-value gap. -/
@[simp] theorem unitGDObjectiveQ_evalR
    {N : ℕ} (d : LeanPEP.GramPEP.DataR (Fin (N + 2)) (N + 2)) :
    (unitGDObjectiveQ N).evalR d =
      d.value (pointIndex (Point.iter (Fin.last N))) -
        d.value (pointIndex (Point.star : Point N)) := by
  simp [unitGDObjectiveQ, unitGDGramProfileQ, compileObjectiveQ,
    finalGapObjectiveProfileQ]

/-- Turn one model's exact position/gradient fields into rational Gram data.
The zero Gram matrix and zero values are irrelevant; this object is used only
with the existing exact model-realization checker. -/
def modelSkeletonQ {p m : ℕ} (model : ModelQ p m) :
    LeanPEP.GramPEP.DataQ (Fin p) m :=
  { gram := 0
    position := model.position
    gradient := model.gradient
    value := 0 }

/-- At `N = 1`, the generated position and gradient arrays agree exactly with
the established one-step Gram model. -/
theorem unitGDModelQ_one_vectors :
    RealizesModelExactQ oneStepModelQ (modelSkeletonQ (unitGDModelQ 1)) := by
  apply (checkDataRealizesModelQ_eq_true_iff
    oneStepModelQ (modelSkeletonQ (unitGDModelQ 1))).mp
  native_decide

/-- At `N = 1`, the generated radius assumption is exactly the established
one-step normalization expression. -/
theorem unitGDModelQ_one_assumptions :
    (unitGDModelQ 1).assumptions = oneStepModelQ.assumptions := by
  change
    [initialRadiusExprQ (N := 1) unitRadiusNormalizationQ] =
      [oneNormalizationQ]
  have h :
      initialRadiusExprQ (N := 1) unitRadiusNormalizationQ =
        oneNormalizationQ :=
    checkLinearExprEqQ_sound _ _ (by native_decide)
  rw [h]

/-- The complete compiler-generated `N = 1` model is exactly the previously
verified hand-written one-step model: positions, gradients, ordering, and
normalization all coincide. -/
theorem unitGDModelQ_one_eq :
    unitGDModelQ 1 = oneStepModelQ := by
  apply ModelQ.ext
  · funext i
    exact unitGDModelQ_one_vectors.position i
  · funext i
    exact unitGDModelQ_one_vectors.gradient i
  · exact unitGDModelQ_one_assumptions

/-- The generated `N = 1` final-gap objective is exactly the established
one-step objective. -/
theorem unitGDObjectiveQ_one_eq :
    unitGDObjectiveQ 1 = oneStepObjectiveQ := by
  exact checkLinearExprEqQ_sound _ _ (by native_decide)

/-- Therefore every ordered interpolation expression generated from the new
model is exactly the corresponding expression of the established model. -/
theorem unitGDInterpolationExprQ_one (i j : Fin 3) :
    interpolationExprQ (unitGDModelQ 1) i j =
      interpolationExprQ oneStepModelQ i j := by
  rw [unitGDModelQ_one_eq]

/-- The unchanged general Gram checker has an accepted exact certificate for
the compiler-generated one-step model, with the generated objective and bound
`1/6`. -/
theorem unitGD_oneStep_exact_certificate :
    ∃ c : LeanPEP.GramPEP.UpperCertQ (unitGDModelQ 1),
      c.bound = (1 : ℚ) / 6 ∧
      c.objective = unitGDObjectiveQ 1 ∧
      LeanPEP.GramPEP.checkUpperCertQ c = true := by
  rw [unitGDModelQ_one_eq, unitGDObjectiveQ_one_eq]
  exact ⟨oneStepUpperCertQ, rfl, rfl, oneStepUpperCertQ_check⟩

/-- The previously verified one-step upper theorem is now routed through the
profile-generated general Gram model and objective. -/
theorem unitGD_oneStep_upper
    (d : LeanPEP.GramPEP.DataR (Fin 3) 3)
    (hrealizes : RealizesModelQ (unitGDModelQ 1) d)
    (hcore : CoreFeasible d)
    (hassumptions : AssumptionsFeasibleR (unitGDModelQ 1) d) :
    (unitGDObjectiveQ 1).evalR d ≤ (1 : ℝ) / 6 := by
  rw [unitGDModelQ_one_eq] at hrealizes hassumptions
  rw [unitGDObjectiveQ_one_eq]
  simpa using oneStep_upper d hrealizes hcore hassumptions

end GradientDescentGram
end Profiles
end LeanPEP
