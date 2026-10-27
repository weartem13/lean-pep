import LeanPEP.ActualFunction.Interpolation
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

/-!
# Analytic smooth-convex assumptions imply the first-order PEP models

This file closes the analysis-facing part of the pairwise interpolation bridge.
For a globally convex differentiable function with a `1`-Lipschitz gradient,
it proves:

* the supporting-hyperplane lower model; and
* the normalized quadratic upper model (the descent lemma).

Both proofs restrict the function to the affine line from `x` to `y`.  The
lower model follows from the derivative/slope inequality for a convex
one-dimensional restriction.  For the upper model, the quadratic remainder
has nonpositive derivative on `[0, 1]`; this is proved from the Lipschitz bound
and Cauchy--Schwarz, and then converted to antitonicity on that interval.

No finite-dimensional coordinates, Gram representation, numerical solver, or
interpolation-completeness assumption is used.
-/

namespace LeanPEP
namespace ActualFunction
namespace IsOneSmoothConvexAnalytic

variable
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {g : E → E}

/-- Derivative of the restriction of `f` to the affine line from `x` to `y`. -/
private theorem hasDerivAt_lineRestriction
    (h : IsOneSmoothConvexAnalytic f g) (x y : E) (t : ℝ) :
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
    (h : IsOneSmoothConvexAnalytic f g) (x y : E) :
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

/-- The scalar derivative of the normalized quadratic remainder along the
segment from `x` to `y`. -/
private theorem hasDerivAt_quadraticRemainder
    (h : IsOneSmoothConvexAnalytic f g) (x y : E) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ =>
        f (AffineMap.lineMap x y s)
          - s * inner ℝ (g x) (y - x)
          - ((1 : ℝ) / 2) * s ^ 2 * inner ℝ (y - x) (y - x))
      (inner ℝ (g (AffineMap.lineMap x y t)) (y - x)
        - inner ℝ (g x) (y - x)
        - t * inner ℝ (y - x) (y - x))
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
        (fun s : ℝ => ((1 : ℝ) / 2) * s ^ 2 * inner ℝ (y - x) (y - x))
        (t * inner ℝ (y - x) (y - x))
        t := by
    have hraw :
        HasDerivAt
          (fun s : ℝ => ((1 : ℝ) / 2) * s ^ 2 * inner ℝ (y - x) (y - x))
          ((((1 : ℝ) / 2) * (2 * t)) * inner ℝ (y - x) (y - x))
          t :=
      ((hsquare.const_mul ((1 : ℝ) / 2)).mul_const
        (inner ℝ (y - x) (y - x)))
    have hcoeff :
        (((1 : ℝ) / 2) * (2 * t)) * inner ℝ (y - x) (y - x) =
          t * inner ℝ (y - x) (y - x) := by
      ring
    rw [hcoeff] at hraw
    exact hraw
  exact (hline.sub hlinear).sub hquadratic

/-- The derivative of the quadratic remainder is nonpositive on `[0, 1]`. -/
private theorem quadraticRemainder_deriv_nonpos
    (h : IsOneSmoothConvexAnalytic f g) (x y : E) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    inner ℝ (g (AffineMap.lineMap x y t)) (y - x)
        - inner ℝ (g x) (y - x)
        - t * inner ℝ (y - x) (y - x)
      ≤ 0 := by
  let d : E := y - x
  let p : E := AffineMap.lineMap x y t
  have hline : p - x = t • d := by
    simpa [p, d] using (AffineMap.lineMap_vsub_left x y t)
  have hlipDist := h.gradientLipschitz.dist_le_mul p x
  have hlip : ‖g p - g x‖ ≤ t * ‖d‖ := by
    rw [dist_eq_norm, dist_eq_norm] at hlipDist
    rw [hline, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at hlipDist
    simpa using hlipDist
  have hcs :
      inner ℝ (g p - g x) d ≤ ‖g p - g x‖ * ‖d‖ :=
    real_inner_le_norm _ _
  have hmul :
      ‖g p - g x‖ * ‖d‖ ≤ (t * ‖d‖) * ‖d‖ :=
    mul_le_mul_of_nonneg_right hlip (norm_nonneg d)
  have hbound :
      inner ℝ (g p - g x) d ≤ t * inner ℝ d d := by
    rw [real_inner_self_eq_norm_mul_norm]
    simpa [mul_assoc] using hcs.trans hmul
  have hdiff :
      inner ℝ (g p) d - inner ℝ (g x) d = inner ℝ (g p - g x) d := by
    rw [inner_sub_left]
  change
    inner ℝ (g p) d - inner ℝ (g x) d - t * inner ℝ d d ≤ 0
  rw [hdiff]
  linarith

/-- A `1`-Lipschitz gradient implies the normalized quadratic upper model. -/
theorem upperModel
    (h : IsOneSmoothConvexAnalytic f g) (x y : E) :
    f y ≤
      f x + inner ℝ (g x) (y - x)
        + ((1 : ℝ) / 2) * inner ℝ (y - x) (y - x) := by
  let q : ℝ → ℝ := fun t =>
    f (AffineMap.lineMap x y t)
      - t * inner ℝ (g x) (y - x)
      - ((1 : ℝ) / 2) * t ^ 2 * inner ℝ (y - x) (y - x)
  let q' : ℝ → ℝ := fun t =>
    inner ℝ (g (AffineMap.lineMap x y t)) (y - x)
      - inner ℝ (g x) (y - x)
      - t * inner ℝ (y - x) (y - x)
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
        f x + ((1 : ℝ) / 2) * ‖y - x‖ ^ 2
          + inner ℝ (g x) (y - x) := hq10
    _ =
        f x + inner ℝ (g x) (y - x)
          + ((1 : ℝ) / 2) * ‖y - x‖ ^ 2 := by
      ring

/-- The standard analytic smooth-convex assumptions imply exactly the two
first-order models consumed by the PEP semantics. -/
theorem toFirstOrder
    (h : IsOneSmoothConvexAnalytic f g) :
    IsOneSmoothConvexFirstOrder f g where
  lowerModel := h.lowerModel
  upperModel := h.upperModel

/-- Analytic assumptions imply nonnegativity of every exact pairwise
interpolation slack. -/
theorem interpolationSlack_nonneg
    (h : IsOneSmoothConvexAnalytic f g) (x y : E) :
    0 ≤ ActualFunction.interpolationSlack f g x y :=
  ActualFunction.interpolationSlack_nonneg h.toFirstOrder x y

/-- Inequality-oriented analytic form of the smooth-convex interpolation
condition. -/
theorem pairwise_interpolation
    (h : IsOneSmoothConvexAnalytic f g) (x y : E) :
    f y + inner ℝ (g y) (x - y)
        + ((1 : ℝ) / 2) * inner ℝ (g x - g y) (g x - g y)
      ≤ f x :=
  ActualFunction.pairwise_interpolation h.toFirstOrder x y

end IsOneSmoothConvexAnalytic
end ActualFunction
end LeanPEP
