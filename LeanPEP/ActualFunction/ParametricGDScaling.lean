import LeanPEP.ActualFunction.OneStepScaling
import LeanPEP.ActualFunction.ParametricGDActual
import Mathlib.Tactic

/-!
# General smoothness and radius scaling for arbitrary-length actual GD

The v0.12C2 theorem proves the exact arbitrary-length rate for a normalized
first-order smooth-convex pair and the unit-step recursion

```text
x_(k+1) = x_k - g(x_k).
```

For a positive smoothness constant `L`, this file divides function values and
the gradient field by `L`.  The resulting pair is normalized to smoothness
one, and its unit-step recursion is exactly the original gradient-descent
recursion with step size `1 / L`:

```text
x_(k+1) = x_k - (1/L) • g(x_k).
```

Applying the already verified v0.12C2 theorem and transporting the result back
gives, for every trajectory length `N`,

```text
f(x_N) - f(xStar) <= L * ||x0 - xStar||^2 * gdBoundQ N,
```

and therefore under `||x0 - xStar||^2 <= R^2`,

```text
f(x_N) - f(xStar) <= L * R^2 * gdBoundQ N.
```

Since `gdBoundQ N = 1 / (4N + 2)`, this is the planned general
`L R^2 / (4N + 2)` upper theorem.  No lower witness or interpolation
completeness result is introduced here.
-/

open scoped NNReal

namespace LeanPEP
namespace ActualFunction
namespace ParametricGDScaling

open ParametricGDActual

variable
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Function-value normalization that removes a positive smoothness constant
without changing the ambient coordinates.  The subtraction of `f 0` is only a
harmless additive normalization. -/
noncomputable def normalizedFunction
    (L : ℝ≥0) (f : E → ℝ) (x : E) : ℝ :=
  (f x - f 0) / (L : ℝ)

/-- Gradient normalization corresponding to `normalizedFunction`. -/
noncomputable def normalizedGradient
    (L : ℝ≥0) (g : E → E) (x : E) : E :=
  (L : ℝ)⁻¹ • g x

/-- The general exact first-order models become the normalized first-order
models after dividing function values and gradients by a positive `L`. -/
theorem normalizedFirstOrder
    {L : ℝ≥0} {f : E → ℝ} {g : E → E}
    (h : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) :
    IsOneSmoothConvexFirstOrder
      (normalizedFunction L f)
      (normalizedGradient L g) := by
  have hscaled :=
    SmoothScaling.normalizedFirstOrder
      (xStar := (0 : E)) (R := (1 : ℝ)) h hL (by norm_num)
  constructor
  · intro x y
    simpa [normalizedFunction, normalizedGradient,
      SmoothScaling.normalizedFunction,
      SmoothScaling.normalizedGradient,
      SmoothScaling.scaledPoint] using hscaled.lowerModel x y
  · intro x y
    simpa [normalizedFunction, normalizedGradient,
      SmoothScaling.normalizedFunction,
      SmoothScaling.normalizedGradient,
      SmoothScaling.scaledPoint] using hscaled.upperModel x y

/-- Gradient descent with step size `1 / L`, defined through the normalized
unit-step recursion so that transport to v0.12C2 is definitionally direct. -/
noncomputable def smoothGDIterate
    (L : ℝ≥0) (g : E → E) (x0 : E) : ℕ → E :=
  unitGDIterate (normalizedGradient L g) x0

@[simp] theorem smoothGDIterate_zero
    (L : ℝ≥0) (g : E → E) (x0 : E) :
    smoothGDIterate L g x0 0 = x0 := rfl

@[simp] theorem smoothGDIterate_succ
    (L : ℝ≥0) (g : E → E) (x0 : E) (k : ℕ) :
    smoothGDIterate L g x0 (k + 1) =
      smoothGDIterate L g x0 k -
        (L : ℝ)⁻¹ • g (smoothGDIterate L g x0 k) := rfl

/-- Stationarity is preserved by the smoothness normalization. -/
theorem normalizedGradient_stationary
    {L : ℝ≥0} {g : E → E} {xStar : E}
    (hstationary : g xStar = 0) :
    normalizedGradient L g xStar = 0 := by
  simp [normalizedGradient, hstationary]

end ParametricGDScaling

namespace IsSmoothConvexFirstOrder

open Toy.FiniteGD.ParametricUpper
open ParametricGDScaling

variable
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {L : ℝ≥0} {f : E → ℝ} {g : E → E}

/-- Arbitrary-length actual-function GD upper theorem for positive smoothness,
keeping the exact initial distance.  The iteration uses step size `1 / L`. -/
theorem parametricGD_upper_exact_radius
    (h : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ))
    (N : ℕ) {xStar x0 : E}
    (hstationary : g xStar = 0) :
    f (smoothGDIterate L g x0 N) - f xStar ≤
      (L : ℝ) * ‖x0 - xStar‖ ^ 2 * (gdBoundQ N : ℝ) := by
  have hnormalized :
      IsOneSmoothConvexFirstOrder
        (normalizedFunction L f)
        (normalizedGradient L g) :=
    ParametricGDScaling.normalizedFirstOrder h hL
  have hunit :=
    hnormalized.parametricGD_upper_exact_radius
      (xStar := xStar) (x0 := x0) N
      (normalizedGradient_stationary hstationary)
  have hdiv :
      (f (smoothGDIterate L g x0 N) - f xStar) / (L : ℝ) ≤
        (gdBoundQ N : ℝ) * ‖x0 - xStar‖ ^ 2 := by
    calc
      (f (smoothGDIterate L g x0 N) - f xStar) / (L : ℝ) =
          normalizedFunction L f (smoothGDIterate L g x0 N) -
            normalizedFunction L f xStar := by
        unfold normalizedFunction
        ring
      _ ≤ (gdBoundQ N : ℝ) * ‖x0 - xStar‖ ^ 2 := by
        simpa [smoothGDIterate] using hunit
  have hscaled := (div_le_iff₀ hL).1 hdiv
  calc
    f (smoothGDIterate L g x0 N) - f xStar ≤
        ((gdBoundQ N : ℝ) * ‖x0 - xStar‖ ^ 2) * (L : ℝ) := hscaled
    _ = (L : ℝ) * ‖x0 - xStar‖ ^ 2 * (gdBoundQ N : ℝ) := by
      ring

/-- Radius-bounded form of the arbitrary-length general-smoothness theorem. -/
theorem parametricGD_upper_radius
    (h : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ))
    (N : ℕ) {xStar x0 : E} {R : ℝ}
    (hstationary : g xStar = 0)
    (hradius : ‖x0 - xStar‖ ^ 2 ≤ R ^ 2) :
    f (smoothGDIterate L g x0 N) - f xStar ≤
      (L : ℝ) * R ^ 2 * (gdBoundQ N : ℝ) := by
  have hmain := h.parametricGD_upper_exact_radius
    hL (xStar := xStar) (x0 := x0) N hstationary
  have hboundQ : 0 ≤ gdBoundQ N := by
    unfold gdBoundQ
    positivity
  have hcoef : 0 ≤ (L : ℝ) * (gdBoundQ N : ℝ) := by
    exact mul_nonneg (le_of_lt hL) (Rat.cast_nonneg.mpr hboundQ)
  calc
    f (smoothGDIterate L g x0 N) - f xStar ≤
        (L : ℝ) * ‖x0 - xStar‖ ^ 2 * (gdBoundQ N : ℝ) := hmain
    _ = ((L : ℝ) * (gdBoundQ N : ℝ)) * ‖x0 - xStar‖ ^ 2 := by
      ring
    _ ≤ ((L : ℝ) * (gdBoundQ N : ℝ)) * R ^ 2 :=
      mul_le_mul_of_nonneg_left hradius hcoef
    _ = (L : ℝ) * R ^ 2 * (gdBoundQ N : ℝ) := by
      ring

/-- Unit-radius form of the arbitrary-length general-smoothness theorem. -/
theorem parametricGD_upper_unit_radius
    (h : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ))
    (N : ℕ) {xStar x0 : E}
    (hstationary : g xStar = 0)
    (hradius : ‖x0 - xStar‖ ^ 2 ≤ 1) :
    f (smoothGDIterate L g x0 N) - f xStar ≤
      (L : ℝ) * (gdBoundQ N : ℝ) := by
  have hradius' : ‖x0 - xStar‖ ^ 2 ≤ (1 : ℝ) ^ 2 := by
    simpa using hradius
  simpa using
    h.parametricGD_upper_radius hL
      (R := (1 : ℝ)) N hstationary hradius'

end IsSmoothConvexFirstOrder

namespace IsSmoothConvexAnalytic

open Toy.FiniteGD.ParametricUpper
open ParametricGDScaling

variable
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {L : ℝ≥0} {f : E → ℝ} {g : E → E}

/-- Analysis-facing arbitrary-length step-size-`1/L` theorem with the exact
initial distance. -/
theorem parametricGD_upper_exact_radius
    (h : IsSmoothConvexAnalytic L f g)
    (hL : 0 < (L : ℝ))
    (N : ℕ) {xStar x0 : E}
    (hstationary : g xStar = 0) :
    f (smoothGDIterate L g x0 N) - f xStar ≤
      (L : ℝ) * ‖x0 - xStar‖ ^ 2 * (gdBoundQ N : ℝ) :=
  h.toFirstOrder.parametricGD_upper_exact_radius
    hL (xStar := xStar) (x0 := x0) N hstationary

/-- Analysis-facing radius-bounded arbitrary-length theorem. -/
theorem parametricGD_upper_radius
    (h : IsSmoothConvexAnalytic L f g)
    (hL : 0 < (L : ℝ))
    (N : ℕ) {xStar x0 : E} {R : ℝ}
    (hstationary : g xStar = 0)
    (hradius : ‖x0 - xStar‖ ^ 2 ≤ R ^ 2) :
    f (smoothGDIterate L g x0 N) - f xStar ≤
      (L : ℝ) * R ^ 2 * (gdBoundQ N : ℝ) :=
  h.toFirstOrder.parametricGD_upper_radius
    hL (xStar := xStar) (x0 := x0) (R := R) N hstationary hradius

/-- Analysis-facing unit-radius arbitrary-length theorem. -/
theorem parametricGD_upper_unit_radius
    (h : IsSmoothConvexAnalytic L f g)
    (hL : 0 < (L : ℝ))
    (N : ℕ) {xStar x0 : E}
    (hstationary : g xStar = 0)
    (hradius : ‖x0 - xStar‖ ^ 2 ≤ 1) :
    f (smoothGDIterate L g x0 N) - f xStar ≤
      (L : ℝ) * (gdBoundQ N : ℝ) :=
  h.toFirstOrder.parametricGD_upper_unit_radius
    hL (xStar := xStar) (x0 := x0) N hstationary hradius

end IsSmoothConvexAnalytic
end ActualFunction
end LeanPEP
