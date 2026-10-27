import LeanPEP.ActualFunction.FiniteGram
import LeanPEP.GramPEP.UpperCertificateExamples
import Mathlib.Tactic

/-!
# Actual one-step gradient descent realizes the fixed one-step Gram model

This file instantiates the generic finite-sample Gram bridge for the existing
three-point, three-vector one-step formulation
`GramPEP.UpperCertificateExamples.oneStepModelQ`.

The three sampled points are `(x★, x₀, x₁)`.  The ambient Gram basis is

`(x₀ - x★, g x₀, g x₁)`.

The model's symbolic equations then express

* the optimum point as the zero centered displacement;
* `x₀` as the first basis vector;
* `x₁ = x₀ - g x₀` as the first basis vector minus the second;
* the stationary gradient at `x★` as zero; and
* the gradients at `x₀` and `x₁` as the second and third basis vectors.

Under the analytic smooth-convex assumptions, stationarity, the one-step GD
equation, and the initial-radius bound, the resulting real datum realizes the
fixed rational model, is `CoreFeasible`, and satisfies its normalization
assumption.  This file deliberately stops before applying the accepted `1/6`
upper certificate; that final transport is the v0.12A4 step.
-/

namespace LeanPEP
namespace ActualFunction
namespace OneStepGram

open GramPEP
open GramPEP.UpperCertificateExamples

variable
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Ordered actual samples `(x★, x₀, x₁)`. -/
def oneStepSamples (xStar x0 x1 : E) : Fin 3 → E :=
  ![xStar, x0, x1]

/-- Ambient vector family corresponding to the abstract Gram basis
`(x₀ - x★, g₀, g₁)`. -/
def oneStepBase (g : E → E) (xStar x0 x1 : E) : Fin 3 → E :=
  ![x0 - xStar, g x0, g x1]

/-- Exact real Gram datum attached to one actual one-step execution. -/
noncomputable def oneStepData
    (f : E → ℝ) (g : E → E) (xStar x0 x1 : E) :
    DataR (Fin 3) 3 :=
  FiniteGram.dataOfModel
    (oneStepBase g xStar x0 x1)
    oneStepModelQ
    (oneStepSamples xStar x0 x1)
    f

/-- The first symbolic basis vector realizes the actual centered initial
point. -/
theorem realize_oneX0Q
    (g : E → E) (xStar x0 x1 : E) :
    FiniteGram.realize (oneStepBase g xStar x0 x1)
        (castVecQ oneX0Q) =
      x0 - xStar := by
  simp [FiniteGram.realize, oneStepBase, oneX0Q, castVecQ,
    Fin.sum_univ_three]

/-- The symbolic one-step positions realize the three centered actual
samples. -/
theorem oneStepPositionRealization
    (g : E → E) (xStar x0 x1 : E)
    (hstep : x1 = x0 - g x0) :
    ∀ i,
      FiniteGram.realize (oneStepBase g xStar x0 x1)
          (castVecQ (oneStepModelQ.position i)) =
        oneStepSamples xStar x0 x1 i - xStar := by
  intro i
  fin_cases i <;>
    simp [FiniteGram.realize, oneStepBase, oneStepSamples,
      oneStepModelQ, castVecQ, Fin.sum_univ_three, hstep] <;>
    abel

/-- The symbolic gradients realize the actual sampled gradients when the
reference point is stationary. -/
theorem oneStepGradientRealization
    (g : E → E) (xStar x0 x1 : E)
    (hstationary : g xStar = 0) :
    ∀ i,
      FiniteGram.realize (oneStepBase g xStar x0 x1)
          (castVecQ (oneStepModelQ.gradient i)) =
        g (oneStepSamples xStar x0 x1 i) := by
  intro i
  fin_cases i <;>
    simp [FiniteGram.realize, oneStepBase, oneStepSamples,
      oneStepModelQ, castVecQ, Fin.sum_univ_three, hstationary]

/-- The one-step symbolic vectors have their intended ambient meaning. -/
theorem oneStepRealizesActualSamples
    (g : E → E) (xStar x0 x1 : E)
    (hstationary : g xStar = 0)
    (hstep : x1 = x0 - g x0) :
    FiniteGram.RealizesActualSamples
      (oneStepBase g xStar x0 x1)
      oneStepModelQ
      (oneStepSamples xStar x0 x1)
      xStar
      g := by
  constructor
  · exact oneStepPositionRealization g xStar x0 x1 hstep
  · exact oneStepGradientRealization g xStar x0 x1 hstationary

/-- The exact coefficient fields of the actual one-step datum realize the
fixed rational `oneStepModelQ`. -/
theorem oneStepData_realizesModel
    (f : E → ℝ) (g : E → E) (xStar x0 x1 : E) :
    RealizesModelQ oneStepModelQ
      (oneStepData f g xStar x0 x1) :=
  FiniteGram.dataOfModel_realizes
    (oneStepBase g xStar x0 x1)
    oneStepModelQ
    (oneStepSamples xStar x0 x1)
    f

/-- Actual analytic smooth-convex samples produce a core-feasible one-step
Gram datum. -/
theorem oneStepData_coreFeasible
    [CompleteSpace E]
    {f : E → ℝ} {g : E → E} {xStar x0 x1 : E}
    (hfun : IsOneSmoothConvexAnalytic f g)
    (hstationary : g xStar = 0)
    (hstep : x1 = x0 - g x0) :
    CoreFeasible (oneStepData f g xStar x0 x1) :=
  FiniteGram.dataOfModel_coreFeasible hfun
    (oneStepRealizesActualSamples g xStar x0 x1 hstationary hstep)

/-- The model's sole normalization expression evaluates to the actual centered
initial squared-radius slack. -/
theorem oneStepNormalization_eval
    (f : E → ℝ) (g : E → E) (xStar x0 x1 : E) :
    oneNormalizationQ.evalR (oneStepData f g xStar x0 x1) =
      1 - inner ℝ (x0 - xStar) (x0 - xStar) := by
  have hsym :
      IsGramSymmetric (oneStepData f g xStar x0 x1).gram := by
    change IsGramSymmetric
      (FiniteGram.gramOfVectors (oneStepBase g xStar x0 x1))
    exact FiniteGram.gramOfVectors_symmetric _
  unfold oneNormalizationQ
  rw [LinearExprQ.evalR_sub, LinearExprQ.evalR_const]
  rw [LinearExprQ.evalR_gramNorm oneX0Q
    (oneStepData f g xStar x0 x1) hsym]
  simp [oneStepData, FiniteGram.gramNormSq_gramOfVectors,
    realize_oneX0Q g xStar x0 x1]

/-- The initial radius bound discharges the sole formulation-specific
assumption in `oneStepModelQ`. -/
theorem oneStepData_assumptionsFeasible
    (f : E → ℝ) (g : E → E) (xStar x0 x1 : E)
    (hradius : inner ℝ (x0 - xStar) (x0 - xStar) ≤ 1) :
    AssumptionsFeasibleR oneStepModelQ
      (oneStepData f g xStar x0 x1) := by
  intro k
  fin_cases k
  change
    0 ≤ oneNormalizationQ.evalR (oneStepData f g xStar x0 x1)
  rw [oneStepNormalization_eval]
  exact sub_nonneg.mpr hradius

/-- Complete v0.12A3 feasibility package for one actual unit-gradient step. -/
theorem oneStepData_feasible
    [CompleteSpace E]
    {f : E → ℝ} {g : E → E} {xStar x0 x1 : E}
    (hfun : IsOneSmoothConvexAnalytic f g)
    (hstationary : g xStar = 0)
    (hstep : x1 = x0 - g x0)
    (hradius : inner ℝ (x0 - xStar) (x0 - xStar) ≤ 1) :
    RealizesModelQ oneStepModelQ (oneStepData f g xStar x0 x1) ∧
      CoreFeasible (oneStepData f g xStar x0 x1) ∧
      AssumptionsFeasibleR oneStepModelQ
        (oneStepData f g xStar x0 x1) :=
  ⟨oneStepData_realizesModel f g xStar x0 x1,
    oneStepData_coreFeasible hfun hstationary hstep,
    oneStepData_assumptionsFeasible f g xStar x0 x1 hradius⟩

end OneStepGram
end ActualFunction
end LeanPEP
