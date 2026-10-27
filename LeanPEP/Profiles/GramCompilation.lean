import LeanPEP.Profiles.FixedStepFirstOrder
import LeanPEP.GramPEP.UpperCertificate
import LeanPEP.GramPEP.Coordinate
import Mathlib.Tactic

/-!
# Compiling fixed-step profiles to the general Gram-PEP model

This module is the second profile/compiler slice of Lean-PEP.  It keeps the
function class fixed to normalized smooth convex interpolation and composes
three exact profile components:

* a causal fixed-step first-order algorithm profile;
* an initial-radius normalization profile; and
* a function-value-gap objective profile.

For a horizon `N`, both sampled points and Gram-basis vectors use `N + 2`
coordinates.  Their deterministic order is

```text
points:  (x_star, x_0, ..., x_N)
basis:   (x_0 - x_star, g_0, ..., g_N).
```

The compiler maps this profile to the existing `GramPEP.ModelQ`; it does not
change the general Gram semantics, interpolation expressions, primal checker,
upper-certificate checker, or PSD factor checker.
-/

namespace LeanPEP
namespace Profiles
namespace GramCompilation

open LeanPEP.Toy.FiniteGD
open LeanPEP.Profiles.FixedStepFirstOrder
open LeanPEP.GramPEP

/-- Deterministic point order used by the compiled Gram formulation:
`star, iter 0, ..., iter N`. -/
def pointAtIndex {N : ℕ} : Fin (N + 2) → Point N :=
  Fin.cases (Point.star : Point N) (fun i => Point.iter i)

/-- Index of one source point in the compiled point order. -/
def pointIndex {N : ℕ} : Point N → Fin (N + 2)
  | Point.star => 0
  | Point.iter i => Fin.succ i

@[simp] theorem pointAtIndex_zero {N : ℕ} :
    pointAtIndex (0 : Fin (N + 2)) = (Point.star : Point N) := rfl

@[simp] theorem pointAtIndex_succ {N : ℕ} (i : Fin (N + 1)) :
    pointAtIndex (Fin.succ i) = Point.iter i := rfl

@[simp] theorem pointIndex_star {N : ℕ} :
    pointIndex (Point.star : Point N) = (0 : Fin (N + 2)) := rfl

@[simp] theorem pointIndex_iter {N : ℕ} (i : Fin (N + 1)) :
    pointIndex (Point.iter i) = Fin.succ i := rfl

/-- The point encoder and decoder are inverse in the source-to-compiled
direction. -/
@[simp] theorem pointAtIndex_pointIndex {N : ℕ} (i : Point N) :
    pointAtIndex (pointIndex i) = i := by
  cases i <;> rfl

/-- The point encoder and decoder are inverse in the compiled-to-source
direction. -/
@[simp] theorem pointIndex_pointAtIndex {N : ℕ} (i : Fin (N + 2)) :
    pointIndex (pointAtIndex i) = i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

/-- The deterministic point encoding is injective. -/
theorem pointIndex_injective {N : ℕ} :
    Function.Injective (pointIndex (N := N)) := by
  intro i j hij
  have h := congrArg (pointAtIndex (N := N)) hij
  simpa using h

/-- The deterministic point encoding covers every compiled point index. -/
theorem pointIndex_surjective {N : ℕ} :
    Function.Surjective (pointIndex (N := N)) := by
  intro i
  exact ⟨pointAtIndex i, pointIndex_pointAtIndex i⟩

/-- Gram-basis index of the centered initial displacement `x_0 - x_star`. -/
def initialBasisIndex (N : ℕ) : Fin (N + 2) := 0

/-- Gram-basis index of sampled gradient `g_i`. -/
def gradientBasisIndex {N : ℕ} (i : Fin (N + 1)) : Fin (N + 2) :=
  Fin.succ i

/-- Standard basis expression representing `x_0 - x_star`. -/
def initialBasisQ (N : ℕ) : VecExpr (N + 2) ℚ :=
  standardBasisExpr (𝕜 := ℚ) (initialBasisIndex N)

/-- Standard basis expression representing sampled gradient `g_i`. -/
def sampledGradientBasisQ {N : ℕ}
    (i : Fin (N + 1)) : VecExpr (N + 2) ℚ :=
  standardBasisExpr (𝕜 := ℚ) (gradientBasisIndex i)

/-- Homogenize a scalar affine form into the Gram basis
`(x_0 - x_star, g_0, ..., g_N)`.  The old scalar constant coefficient becomes
the coefficient of the centered initial-displacement basis vector. -/
def affineVecQ {N : ℕ} (a : GradAffineQ N) : VecExpr (N + 2) ℚ :=
  Fin.cases a.constCoeff a.gradCoeff

@[simp] theorem affineVecQ_initial {N : ℕ} (a : GradAffineQ N) :
    affineVecQ a (initialBasisIndex N) = a.constCoeff := rfl

@[simp] theorem affineVecQ_gradient {N : ℕ}
    (a : GradAffineQ N) (i : Fin (N + 1)) :
    affineVecQ a (gradientBasisIndex i) = a.gradCoeff i := rfl

/-- Compiled Gram coefficient vector of one source point position. -/
def pointPositionVecQ {N : ℕ}
    (profile : ProfileQ N) (i : Point N) : VecExpr (N + 2) ℚ :=
  affineVecQ (pointAffineQ profile i)

/-- Compiled Gram coefficient vector of one sampled gradient.  Stationarity at
the reference optimum is built into the model as the zero vector. -/
def pointGradientVecQ {N : ℕ} : Point N → VecExpr (N + 2) ℚ
  | Point.star => 0
  | Point.iter i => sampledGradientBasisQ i

/-- Exact initial-radius normalization profile.  Its compiled assumption is
`radiusSq - ||x_0 - x_star||^2_G >= 0`. -/
structure NormalizationProfileQ where
  radiusSq : ℚ

/-- Unit-radius normalization used by the normalized PEP developments. -/
def unitRadiusNormalizationQ : NormalizationProfileQ :=
  { radiusSq := 1 }

/-- Compile the initial-radius normalization into one general Gram expression. -/
def initialRadiusExprQ {N : ℕ}
    (normalization : NormalizationProfileQ) :
    LinearExprQ (N + 2) (N + 2) :=
  LinearExprQ.sub
    (LinearExprQ.const (N + 2) (N + 2) normalization.radiusSq)
    (LinearExprQ.gramNorm (p := N + 2) (initialBasisQ N))

/-- The current normalization compiler emits one initial-radius assumption. -/
def normalizationAssumptionsQ {N : ℕ}
    (normalization : NormalizationProfileQ) :
    List (LinearExprQ (N + 2) (N + 2)) :=
  [initialRadiusExprQ normalization]

/-- Function-value-gap objective profile `f(target) - f(reference)`. -/
structure ObjectiveProfileQ (N : ℕ) where
  target : Point N
  reference : Point N

/-- Final-iterate function gap `f(x_N) - f(x_star)`. -/
def finalGapObjectiveProfileQ (N : ℕ) : ObjectiveProfileQ N :=
  { target := Point.iter (Fin.last N)
    reference := Point.star }

/-- Compile a source-level function-value gap into the general Gram linear
expression language. -/
def objectiveExprQ {N : ℕ} (objective : ObjectiveProfileQ N) :
    LinearExprQ (N + 2) (N + 2) :=
  LinearExprQ.sub
    (LinearExprQ.valueVar (m := N + 2) (pointIndex objective.target))
    (LinearExprQ.valueVar (m := N + 2) (pointIndex objective.reference))

/-- First composed exact PEP profile.  In this slice the function class and
oracle are still the fixed normalized smooth-convex gradient-interpolation
semantics already implemented by `GramPEP`. -/
structure PEPProfileQ (N : ℕ) where
  algorithm : ProfileQ N
  normalization : NormalizationProfileQ
  objective : ObjectiveProfileQ N

/-- Compile a composed fixed-step PEP profile into the existing general Gram
model. -/
def compileModelQ {N : ℕ} (profile : PEPProfileQ N) :
    ModelQ (N + 2) (N + 2) :=
  { position := fun i =>
      pointPositionVecQ profile.algorithm (pointAtIndex i)
    gradient := fun i => pointGradientVecQ (pointAtIndex i)
    assumptions := normalizationAssumptionsQ profile.normalization }

/-- Compile the objective component of a composed PEP profile. -/
def compileObjectiveQ {N : ℕ} (profile : PEPProfileQ N) :
    LinearExprQ (N + 2) (N + 2) :=
  objectiveExprQ profile.objective

/-- Reading a compiled position through the declared point order recovers the
source point-position compiler exactly. -/
@[simp] theorem compileModelQ_position_pointIndex {N : ℕ}
    (profile : PEPProfileQ N) (i : Point N) :
    (compileModelQ profile).position (pointIndex i) =
      pointPositionVecQ profile.algorithm i := by
  simp [compileModelQ]

/-- Reading a compiled gradient through the declared point order recovers the
source point-gradient compiler exactly. -/
@[simp] theorem compileModelQ_gradient_pointIndex {N : ℕ}
    (profile : PEPProfileQ N) (i : Point N) :
    (compileModelQ profile).gradient (pointIndex i) =
      pointGradientVecQ i := by
  simp [compileModelQ]

/-- Every compiled iterate has coefficient one on the centered initial
position basis vector. -/
@[simp] theorem compileModelQ_iter_initial_coordinate {N : ℕ}
    (profile : PEPProfileQ N) (i : Fin (N + 1)) :
    (compileModelQ profile).position (pointIndex (Point.iter i))
        (initialBasisIndex N) = 1 := by
  simp [compileModelQ, pointPositionVecQ]

/-- Causality survives Gram compilation: the position of `x_i` has no
coefficient on the current or a future gradient basis vector. -/
theorem compileModelQ_iter_gradient_coordinate_of_le {N : ℕ}
    (profile : PEPProfileQ N)
    (i j : Fin (N + 1)) (hij : i.val ≤ j.val) :
    (compileModelQ profile).position (pointIndex (Point.iter i))
        (gradientBasisIndex j) = 0 := by
  simpa [compileModelQ, pointPositionVecQ] using
    iterateAffineQ_gradCoeff_of_le profile.algorithm i j hij

/-- The compiled objective has the exact intended function-value semantics. -/
@[simp] theorem objectiveExprQ_evalR {N : ℕ}
    (objective : ObjectiveProfileQ N)
    (d : LeanPEP.GramPEP.DataR (Fin (N + 2)) (N + 2)) :
    (objectiveExprQ objective).evalR d =
      d.value (pointIndex objective.target) -
        d.value (pointIndex objective.reference) := by
  simp [objectiveExprQ]

/-- The compiled radius expression has the exact general Gram norm semantics. -/
theorem initialRadiusExprQ_evalR {N : ℕ}
    (normalization : NormalizationProfileQ)
    (d : LeanPEP.GramPEP.DataR (Fin (N + 2)) (N + 2))
    (hG : IsGramSymmetric d.gram) :
    (initialRadiusExprQ normalization).evalR d =
      (normalization.radiusSq : ℝ) -
        gramNormSq d.gram (castVecQ (initialBasisQ N)) := by
  unfold initialRadiusExprQ
  rw [LinearExprQ.evalR_sub, LinearExprQ.evalR_const]
  rw [LinearExprQ.evalR_gramNorm (initialBasisQ N) d hG]

end GramCompilation
end Profiles
end LeanPEP
