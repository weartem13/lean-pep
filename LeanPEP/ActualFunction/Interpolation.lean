import LeanPEP.ActualFunction.Basic
import Mathlib.Tactic

/-!
# Pairwise smooth-convex interpolation inequality

For an actual function satisfying the exact normalized first-order lower and
upper models, this file proves the scalar inequality used by the Gram-PEP
semantic core:

`f x - f y - ⟪g y, x - y⟫ - 1/2 * ‖g x - g y‖² ≥ 0`.

The proof introduces the gradient-step comparison point
`z = x - (g x - g y)`, combines the lower model at `y` with the upper model at
`x`, and then performs exact inner-product algebra.  No finite-dimensionality,
coordinate basis, Gram matrix, solver output, or floating-point argument is
used.
-/

namespace LeanPEP
namespace ActualFunction

variable
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {g : E → E}

/-- The exact scalar interpolation slack for two samples of an actual
function/gradient pair. -/
noncomputable def interpolationSlack (f : E → ℝ) (g : E → E) (x y : E) : ℝ :=
  f x - f y
    - inner ℝ (g y) (x - y)
    - ((1 : ℝ) / 2) * inner ℝ (g x - g y) (g x - g y)

/-- The normalized `1`-smooth convex pairwise interpolation inequality follows
from the exact first-order lower and upper models. -/
theorem interpolationSlack_nonneg
    (h : IsOneSmoothConvexFirstOrder f g) (x y : E) :
    0 ≤ interpolationSlack f g x y := by
  let d : E := g x - g y
  let z : E := x - d
  have hchain :
      f y + inner ℝ (g y) (z - y) ≤
        f x + inner ℝ (g x) (z - x)
          + ((1 : ℝ) / 2) * inner ℝ (z - x) (z - x) :=
    le_trans (h.lowerModel y z) (h.upperModel x z)
  have hzy : z - y = (x - y) - d := by
    dsimp [z]
    abel
  have hzx : z - x = -d := by
    dsimp [z]
    abel
  rw [hzy, hzx] at hchain
  simp only [inner_sub_right, inner_neg_right, inner_neg_left, neg_neg] at hchain
  have hd :
      inner ℝ (g x) d - inner ℝ (g y) d = inner ℝ d d := by
    rw [← inner_sub_left]
  have hslack :
      0 ≤
        f x - f y - inner ℝ (g y) (x - y)
          - ((1 : ℝ) / 2) * inner ℝ d d := by
    rw [inner_sub_right]
    linarith [hchain, hd]
  simpa [interpolationSlack, d] using hslack

/-- Inequality-oriented form of `interpolationSlack_nonneg`. -/
theorem pairwise_interpolation
    (h : IsOneSmoothConvexFirstOrder f g) (x y : E) :
    f y + inner ℝ (g y) (x - y)
        + ((1 : ℝ) / 2) * inner ℝ (g x - g y) (g x - g y)
      ≤ f x := by
  have hslack := interpolationSlack_nonneg h x y
  unfold interpolationSlack at hslack
  linarith

end ActualFunction
end LeanPEP
