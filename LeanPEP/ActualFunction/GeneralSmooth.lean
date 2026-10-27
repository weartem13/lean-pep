import LeanPEP.ActualFunction.AnalyticBridge
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

/-!
# Actual smooth-convex functions with a general Lipschitz constant

The normalized v0.12A interface fixes the gradient Lipschitz constant to one.
This file introduces the corresponding analysis-facing and first-order
contracts for an arbitrary nonnegative constant `L : ℝ≥0` and proves the
analytic-to-first-order bridge.

The proof deliberately mirrors the already verified normalized bridge:

* the supporting-hyperplane lower model is independent of `L`;
* the descent upper model uses the quadratic remainder with coefficient
  `L / 2`; and
* the derivative of that remainder is nonpositive by the `L`-Lipschitz
  gradient bound and Cauchy--Schwarz.

No finite-dimensional coordinates, Gram matrices, certificates, numerical
artifacts, or interpolation-completeness assumption are used here.
-/

open scoped NNReal

namespace LeanPEP
namespace ActualFunction

/-- Standard analysis-facing contract for a differentiable convex function
whose actual gradient is `L`-Lipschitz on a real Hilbert space. -/
structure IsSmoothConvexAnalytic
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (L : ℝ≥0) (f : E → ℝ) (g : E → E) : Prop where
  hasGradientAt : ∀ x, HasGradientAt f (g x) x
  convexOn : ConvexOn ℝ Set.univ f
  gradientLipschitz : LipschitzWith L g

/-- Exact first-order semantic contract for an `L`-smooth convex
function/gradient pair. -/
structure IsSmoothConvexFirstOrder
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : ℝ≥0) (f : E → ℝ) (g : E → E) : Prop where
  lowerModel :
    ∀ x y,
      f x + inner ℝ (g x) (y - x) ≤ f y
  upperModel :
    ∀ x y,
      f y ≤
        f x + inner ℝ (g x) (y - x)
          + ((L : ℝ) / 2) * inner ℝ (y - x) (y - x)

namespace IsSmoothConvexAnalytic

variable
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {L : ℝ≥0} {f : E → ℝ} {g : E → E}

/-- The supplied gradient field agrees with mathlib's gradient. -/
theorem gradient_eq (h : IsSmoothConvexAnalytic L f g) :
    gradient f = g :=
  _root_.gradient_eq h.hasGradientAt

/-- The general analysis-facing contract implies differentiability
everywhere. -/
theorem differentiable (h : IsSmoothConvexAnalytic L f g) :
    Differentiable ℝ f :=
  fun x => (h.hasGradientAt x).differentiableAt

/-- Derivative of the restriction of `f` to the affine line from `x` to
`y`. -/
private theorem hasDerivAt_lineRestriction
    (h : IsSmoothConvexAnalytic L f g) (x y : E) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => f (AffineMap.lineMap x y s))
      (inner ℝ (g (AffineMap.lineMap x y t)) (y - x))
      t := by
  simpa [Function.comp_def] using
    (h.hasGradientAt (AffineMap.lineMap x y t)).hasFDerivAt.comp_hasDerivAt
      t (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t))

/-- Convexity and the supplied gradient imply the supporting-hyperplane
inequality. -/
theorem lowerModel
    (h : IsSmoothConvexAnalytic L f g) (x y : E) :
    f x + inner ℝ (g x) (y - x) ≤ f y := by
  have hconv :
      ConvexOn ℝ Set.univ
        (fun t : ℝ => f (AffineMap.lineMap x y t)) := by
    simpa [Function.comp_def] using
      h.convexOn.comp_affineMap (AffineMap.lineMap x y)
  have hderiv :
      HasDerivAt
        (fun t : ℝ => f (AffineMap.lineMap x y t))
        (inner ℝ (g x) (y - x))
        0 := by
    simpa using hasDerivAt_lineRestriction h x y 0
  have hslope :
      inner ℝ (g x) (y - x) ≤
        slope (fun t : ℝ => f (AffineMap.lineMap x y t)) 0 1 :=
    hconv.le_slope_of_hasDerivAt (by simp) (by simp) (by norm_num) hderiv
  have hslope' :
      inner ℝ (g x) (y - x) ≤ f y - f x := by
    simpa [slope_def_field] using hslope
  linarith

/-- Scalar derivative of the `L`-quadratic remainder along the segment from
`x` to `y`. -/
private theorem hasDerivAt_quadraticRemainder
    (h : IsSmoothConvexAnalytic L f g) (x y : E) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ =>
        f (AffineMap.lineMap x y s)
          - s * inner ℝ (g x) (y - x)
          - ((L : ℝ) / 2) * s ^ 2 * inner ℝ (y - x) (y - x))
      (inner ℝ (g (AffineMap.lineMap x y t)) (y - x)
        - inner ℝ (g x) (y - x)
        - (L : ℝ) * t * inner ℝ (y - x) (y - x))
      t := by
  have hline := hasDerivAt_lineRestriction h x y t
  have hlinear :
      HasDerivAt
        (fun s : ℝ => s * inner ℝ (g x) (y - x))
        (inner ℝ (g x) (y - x))
        t := by
    simpa using (hasDerivAt_id t).mul_const (inner ℝ (g x) (y - x))
  have hsquare : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t)
  have hquadratic :
      HasDerivAt
        (fun s : ℝ => ((L : ℝ) / 2) * s ^ 2 * inner ℝ (y - x) (y - x))
        ((L : ℝ) * t * inner ℝ (y - x) (y - x))
        t := by
    have hraw :
        HasDerivAt
          (fun s : ℝ => ((L : ℝ) / 2) * s ^ 2 * inner ℝ (y - x) (y - x))
          ((((L : ℝ) / 2) * (2 * t)) * inner ℝ (y - x) (y - x))
          t :=
      ((hsquare.const_mul ((L : ℝ) / 2)).mul_const
        (inner ℝ (y - x) (y - x)))
    have hcoeff :
        (((L : ℝ) / 2) * (2 * t)) * inner ℝ (y - x) (y - x) =
          (L : ℝ) * t * inner ℝ (y - x) (y - x) := by
      ring
    rw [hcoeff] at hraw
    exact hraw
  exact (hline.sub hlinear).sub hquadratic

/-- The derivative of the `L`-quadratic remainder is nonpositive on
`[0,1]`. -/
private theorem quadraticRemainder_deriv_nonpos
    (h : IsSmoothConvexAnalytic L f g) (x y : E) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    inner ℝ (g (AffineMap.lineMap x y t)) (y - x)
        - inner ℝ (g x) (y - x)
        - (L : ℝ) * t * inner ℝ (y - x) (y - x)
      ≤ 0 := by
  let d : E := y - x
  let p : E := AffineMap.lineMap x y t
  have hline : p - x = t • d := by
    simpa [p, d] using (AffineMap.lineMap_vsub_left x y t)
  have hlipDist := h.gradientLipschitz.dist_le_mul p x
  have hlip : ‖g p - g x‖ ≤ (L : ℝ) * t * ‖d‖ := by
    rw [dist_eq_norm, dist_eq_norm] at hlipDist
    rw [hline, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at hlipDist
    simpa [mul_assoc] using hlipDist
  have hcs :
      inner ℝ (g p - g x) d ≤ ‖g p - g x‖ * ‖d‖ :=
    real_inner_le_norm _ _
  have hmul :
      ‖g p - g x‖ * ‖d‖ ≤ ((L : ℝ) * t * ‖d‖) * ‖d‖ :=
    mul_le_mul_of_nonneg_right hlip (norm_nonneg d)
  have hbound :
      inner ℝ (g p - g x) d ≤
        (L : ℝ) * t * inner ℝ d d := by
    rw [real_inner_self_eq_norm_mul_norm]
    simpa [mul_assoc] using hcs.trans hmul
  have hdiff :
      inner ℝ (g p) d - inner ℝ (g x) d = inner ℝ (g p - g x) d := by
    rw [inner_sub_left]
  change
    inner ℝ (g p) d - inner ℝ (g x) d
        - (L : ℝ) * t * inner ℝ d d ≤ 0
  rw [hdiff]
  linarith

/-- An `L`-Lipschitz gradient implies the standard quadratic upper model. -/
theorem upperModel
    (h : IsSmoothConvexAnalytic L f g) (x y : E) :
    f y ≤
      f x + inner ℝ (g x) (y - x)
        + ((L : ℝ) / 2) * inner ℝ (y - x) (y - x) := by
  let q : ℝ → ℝ := fun t =>
    f (AffineMap.lineMap x y t)
      - t * inner ℝ (g x) (y - x)
      - ((L : ℝ) / 2) * t ^ 2 * inner ℝ (y - x) (y - x)
  let q' : ℝ → ℝ := fun t =>
    inner ℝ (g (AffineMap.lineMap x y t)) (y - x)
      - inner ℝ (g x) (y - x)
      - (L : ℝ) * t * inner ℝ (y - x) (y - x)
  have hqderiv : ∀ t, HasDerivAt q (q' t) t := by
    intro t
    simpa [q, q'] using hasDerivAt_quadraticRemainder h x y t
  have hanti : AntitoneOn q (Set.Icc (0 : ℝ) 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (0 : ℝ) 1)
    · intro t ht
      exact (hqderiv t).continuousAt.continuousWithinAt
    · intro t ht
      exact (hqderiv t).hasDerivWithinAt
    · intro t ht
      exact quadraticRemainder_deriv_nonpos h x y (interior_subset ht)
  have hq10 : q 1 ≤ q 0 :=
    hanti (by norm_num) (by norm_num) (by norm_num)
  norm_num [q] at hq10
  rw [real_inner_self_eq_norm_sq]
  calc
    f y ≤
        f x + ((L : ℝ) / 2) * ‖y - x‖ ^ 2
          + inner ℝ (g x) (y - x) := hq10
    _ =
        f x + inner ℝ (g x) (y - x)
          + ((L : ℝ) / 2) * ‖y - x‖ ^ 2 := by
      ring

/-- Standard analytic `L`-smooth convex assumptions imply the exact general
first-order contract. -/
theorem toFirstOrder
    (h : IsSmoothConvexAnalytic L f g) :
    IsSmoothConvexFirstOrder L f g where
  lowerModel := h.lowerModel
  upperModel := h.upperModel

end IsSmoothConvexAnalytic

namespace IsOneSmoothConvexAnalytic

variable
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {g : E → E}

/-- The existing normalized analytic contract embeds into the general API at
`L = 1`. -/
theorem toSmooth
    (h : IsOneSmoothConvexAnalytic f g) :
    IsSmoothConvexAnalytic 1 f g where
  hasGradientAt := h.hasGradientAt
  convexOn := h.convexOn
  gradientLipschitz := h.gradientLipschitz

end IsOneSmoothConvexAnalytic

namespace IsOneSmoothConvexFirstOrder

variable
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {g : E → E}

/-- The existing normalized first-order contract embeds into the general API
at `L = 1`. -/
theorem toSmooth
    (h : IsOneSmoothConvexFirstOrder f g) :
    IsSmoothConvexFirstOrder 1 f g := by
  constructor
  · exact h.lowerModel
  · intro x y
    simpa using h.upperModel x y

end IsOneSmoothConvexFirstOrder

end ActualFunction
end LeanPEP
