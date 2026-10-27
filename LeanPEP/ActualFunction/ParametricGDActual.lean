import LeanPEP.ActualFunction.AnalyticBridge
import LeanPEP.ActualFunction.ParametricGDHilbert
import Mathlib.Tactic

/-!
# Arbitrary-length actual unit-step gradient descent

The arbitrary-`N` certificate has already been interpreted in an abstract real
Hilbert space.  This file realizes that abstract trajectory with samples from
one actual normalized smooth-convex function.

For a gradient field `g` and initial point `x0`, `unitGDIterate g x0 k` is the
usual unit-step gradient-descent recursion

```text
x_(k+1) = x_k - g(x_k).
```

The sampled gradients and centered function values are then shown to realize
exactly the prefix-based trajectory used by `ParametricGDHilbert`.  Every
ordered generated interpolation inequality follows from the already verified
actual-function pairwise interpolation theorem.  Applying the kernel-verified
arbitrary-`N` certificate yields

```text
f(x_N) - f(xStar) <= gdBoundQ N * ||x0 - xStar||^2,
```

where `gdBoundQ N = 1 / (4N + 2)`.

This is a universal normalized actual-function upper theorem.  It does not
provide a matching actual lower witness or interpolation completeness.
-/

namespace LeanPEP
namespace ActualFunction
namespace ParametricGDActual

open Toy.FiniteGD
open Toy.FiniteGD.ParametricUpper
open ParametricGDHilbert

variable
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The ordinary unit-step gradient-descent recursion. -/
def unitGDIterate (g : E → E) (x0 : E) : ℕ → E
  | 0 => x0
  | k + 1 => unitGDIterate g x0 k - g (unitGDIterate g x0 k)

@[simp] theorem unitGDIterate_zero (g : E → E) (x0 : E) :
    unitGDIterate g x0 0 = x0 := rfl

@[simp] theorem unitGDIterate_succ
    (g : E → E) (x0 : E) (k : ℕ) :
    unitGDIterate g x0 (k + 1) =
      unitGDIterate g x0 k - g (unitGDIterate g x0 k) := rfl

/-- Gradients sampled along the first `N + 1` actual iterates. -/
def sampledGradient
    (N : ℕ) (g : E → E) (x0 : E) : Fin (N + 1) → E :=
  fun k => g (unitGDIterate g x0 k.val)

/-- Function values sampled along the actual iterates and centered at
`f xStar`. -/
def sampledValue
    (N : ℕ) (f : E → ℝ) (g : E → E) (xStar x0 : E) :
    Fin (N + 1) → ℝ :=
  fun k => f (unitGDIterate g x0 k.val) - f xStar

/-- Actual point represented by one generated finite-GD point. -/
def actualPoint
    (N : ℕ) (xStar : E) (g : E → E) (x0 : E) : Point N → E
  | Point.star => xStar
  | Point.iter k => unitGDIterate g x0 k.val

/-- The generated prefix sum of sampled gradients is exactly the displacement
from the current actual iterate back to `x0`. -/
theorem prefixVector_sampledGradient
    (N : ℕ) (g : E → E) (x0 : E) :
    ∀ (k : ℕ) (hk : k ≤ N + 1),
      prefixVector (sampledGradient N g x0) k hk =
        x0 - unitGDIterate g x0 k := by
  intro k
  induction k with
  | zero =>
      intro hk
      simp [prefixVector]
  | succ k ih =>
      intro hk
      simp [prefixVector, sampledGradient, ih, unitGDIterate] <;> abel

/-- The C1 centered generated position is the actual iterate translated by
`-xStar`. -/
theorem pointPosition_sampledGradient
    (N : ℕ) (xStar : E) (g : E → E) (x0 : E)
    (i : Point N) :
    pointPosition (x0 - xStar) (sampledGradient N g x0) i =
      actualPoint N xStar g x0 i - xStar := by
  cases i with
  | star =>
      simp [pointPosition, actualPoint]
  | iter k =>
      simp [pointPosition, actualPoint,
        prefixVector_sampledGradient] <;> abel

/-- In particular, the first generated iterate is exactly `x0`. -/
@[simp] theorem actualPoint_iter_zero
    (N : ℕ) (xStar : E) (g : E → E) (x0 : E) :
    actualPoint N xStar g x0 (Point.iter ⟨0, by omega⟩) = x0 := by
  simp [actualPoint]

/-- Consecutive generated iterates satisfy the actual unit-step GD update. -/
theorem actualPoint_iter_succ
    (N : ℕ) (xStar : E) (g : E → E) (x0 : E)
    (k : Fin N) :
    actualPoint N xStar g x0
        (Point.iter ⟨k.val + 1, by omega⟩) =
      actualPoint N xStar g x0
          (Point.iter ⟨k.val, by omega⟩) -
        g (actualPoint N xStar g x0
          (Point.iter ⟨k.val, by omega⟩)) := by
  rfl

/-- Centered generated function values are the actual function values at the
represented points. -/
theorem pointValue_sampledValue
    (N : ℕ) (f : E → ℝ) (g : E → E) (xStar x0 : E)
    (i : Point N) :
    pointValue (sampledValue N f g xStar x0) i =
      f (actualPoint N xStar g x0 i) - f xStar := by
  cases i with
  | star =>
      simp [pointValue, actualPoint]
  | iter k =>
      rfl

/-- Under stationarity at `xStar`, generated point gradients are the actual
function gradients at the represented points. -/
theorem pointGradient_sampledGradient
    (N : ℕ) (g : E → E) (xStar x0 : E)
    (hstationary : g xStar = 0)
    (i : Point N) :
    pointGradient (sampledGradient N g x0) i =
      g (actualPoint N xStar g x0 i) := by
  cases i with
  | star =>
      simpa [pointGradient, actualPoint] using hstationary.symm
  | iter k =>
      rfl

/-- Translation by the common reference point preserves all position
differences. -/
theorem pointPosition_sub_eq_actualPoint_sub
    (N : ℕ) (xStar : E) (g : E → E) (x0 : E)
    (i j : Point N) :
    pointPosition (x0 - xStar) (sampledGradient N g x0) i -
        pointPosition (x0 - xStar) (sampledGradient N g x0) j =
      actualPoint N xStar g x0 i - actualPoint N xStar g x0 j := by
  rw [pointPosition_sampledGradient, pointPosition_sampledGradient]
  abel

/-- The abstract C1 interpolation slack for the generated samples is exactly
the actual-function interpolation slack. -/
theorem interpolationSlack_sampled
    {f : E → ℝ} {g : E → E}
    (N : ℕ) (xStar x0 : E)
    (hstationary : g xStar = 0)
    (i j : Point N) :
    ParametricGDHilbert.interpolationSlack
        (x0 - xStar)
        (sampledGradient N g x0)
        (sampledValue N f g xStar x0)
        i j =
      ActualFunction.interpolationSlack f g
        (actualPoint N xStar g x0 i)
        (actualPoint N xStar g x0 j) := by
  unfold ParametricGDHilbert.interpolationSlack
    ActualFunction.interpolationSlack
  rw [pointValue_sampledValue N f g xStar x0 i,
    pointValue_sampledValue N f g xStar x0 j,
    pointGradient_sampledGradient N g xStar x0 hstationary i,
    pointGradient_sampledGradient N g xStar x0 hstationary j,
    pointPosition_sub_eq_actualPoint_sub N xStar g x0 i j]
  ring

/-- Actual normalized first-order smooth-convex samples satisfy every ordered
C1 generated interpolation inequality. -/
theorem feasible_of_firstOrder
    {f : E → ℝ} {g : E → E}
    (h : IsOneSmoothConvexFirstOrder f g)
    (N : ℕ) {xStar x0 : E}
    (hstationary : g xStar = 0) :
    ParametricGDHilbert.Feasible
      (x0 - xStar)
      (sampledGradient N g x0)
      (sampledValue N f g xStar x0) := by
  intro i j
  rw [interpolationSlack_sampled N xStar x0 hstationary i j]
  exact ActualFunction.interpolationSlack_nonneg h
    (actualPoint N xStar g x0 i)
    (actualPoint N xStar g x0 j)

end ParametricGDActual

namespace IsOneSmoothConvexFirstOrder

open Toy.FiniteGD.ParametricUpper
open ParametricGDActual

variable
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {g : E → E}

/-- Arbitrary-length normalized actual-function GD upper theorem, with the
initial distance kept exactly rather than bounded by an external radius. -/
theorem parametricGD_upper_exact_radius
    (h : IsOneSmoothConvexFirstOrder f g)
    (N : ℕ) {xStar x0 : E}
    (hstationary : g xStar = 0) :
    f (unitGDIterate g x0 N) - f xStar ≤
      (gdBoundQ N : ℝ) * ‖x0 - xStar‖ ^ 2 := by
  have hfeasible :=
    ParametricGDActual.feasible_of_firstOrder
      (xStar := xStar) (x0 := x0) h N hstationary
  have hupper :=
    ParametricGDHilbert.gd_upper_normSq
      N (x0 - xStar)
      (sampledGradient N g x0)
      (sampledValue N f g xStar x0)
      hfeasible
  simpa [sampledValue, gdObjective] using hupper

/-- Unit-radius form of the arbitrary-length normalized actual-function GD
upper theorem. -/
theorem parametricGD_upper_unit_radius
    (h : IsOneSmoothConvexFirstOrder f g)
    (N : ℕ) {xStar x0 : E}
    (hstationary : g xStar = 0)
    (hradius : ‖x0 - xStar‖ ^ 2 ≤ 1) :
    f (unitGDIterate g x0 N) - f xStar ≤
      (gdBoundQ N : ℝ) := by
  have hmain := h.parametricGD_upper_exact_radius
    (xStar := xStar) (x0 := x0) N hstationary
  have hboundQ : 0 ≤ gdBoundQ N := by
    unfold gdBoundQ
    positivity
  have hboundR : 0 ≤ (gdBoundQ N : ℝ) :=
    Rat.cast_nonneg.mpr hboundQ
  calc
    f (unitGDIterate g x0 N) - f xStar ≤
        (gdBoundQ N : ℝ) * ‖x0 - xStar‖ ^ 2 := hmain
    _ ≤ (gdBoundQ N : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hradius hboundR
    _ = (gdBoundQ N : ℝ) := by ring

end IsOneSmoothConvexFirstOrder

namespace IsOneSmoothConvexAnalytic

open ParametricGDActual
open Toy.FiniteGD.ParametricUpper

variable
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {g : E → E}

/-- Analysis-facing arbitrary-length normalized actual-function theorem. -/
theorem parametricGD_upper_exact_radius
    (h : IsOneSmoothConvexAnalytic f g)
    (N : ℕ) {xStar x0 : E}
    (hstationary : g xStar = 0) :
    f (unitGDIterate g x0 N) - f xStar ≤
      (gdBoundQ N : ℝ) * ‖x0 - xStar‖ ^ 2 :=
  h.toFirstOrder.parametricGD_upper_exact_radius
    (xStar := xStar) (x0 := x0) N hstationary

/-- Analysis-facing unit-radius arbitrary-length normalized actual-function
theorem. -/
theorem parametricGD_upper_unit_radius
    (h : IsOneSmoothConvexAnalytic f g)
    (N : ℕ) {xStar x0 : E}
    (hstationary : g xStar = 0)
    (hradius : ‖x0 - xStar‖ ^ 2 ≤ 1) :
    f (unitGDIterate g x0 N) - f xStar ≤
      (gdBoundQ N : ℝ) :=
  h.toFirstOrder.parametricGD_upper_unit_radius
    (xStar := xStar) (x0 := x0) N hstationary hradius

end IsOneSmoothConvexAnalytic
end ActualFunction
end LeanPEP
