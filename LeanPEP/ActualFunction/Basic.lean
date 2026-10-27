import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Actual smooth-convex functions: semantic interfaces

This file starts the theorem-level side of Lean-PEP.  It deliberately keeps
three layers distinct:

* `IsOneSmoothConvexAnalytic` records the standard analysis-facing contract:
  an actual gradient at every point, global convexity, and a `1`-Lipschitz
  gradient;
* `IsOneSmoothConvexFirstOrder` records the two exact first-order models used
  by the finite PEP semantics; and
* the implication from the analytic contract to the first-order contract is a
  separate bridge theorem, not a definitional shortcut.

The separation prevents later finite-PEP theorems from silently assuming the
very actual-function soundness bridge that v0.12A is meant to prove.
-/

namespace LeanPEP
namespace ActualFunction

/-- Standard analysis-facing API for a differentiable convex function with a
`1`-Lipschitz gradient on a real Hilbert space.

This structure records the intended external theorem assumptions.  The
analytic-to-first-order implication is intentionally not a field of this
structure and is not yet claimed by this file.
-/
structure IsOneSmoothConvexAnalytic
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (g : E → E) : Prop where
  hasGradientAt : ∀ x, HasGradientAt f (g x) x
  convexOn : ConvexOn ℝ Set.univ f
  gradientLipschitz : LipschitzWith 1 g

/-- Exact first-order semantic contract used by the PEP interpolation proof.

The lower model is the supporting-hyperplane inequality.  The upper model is
its normalized `L = 1` quadratic counterpart.  Keeping this as a separate
structure makes the remaining analytic bridge visible in theorem statements.
-/
structure IsOneSmoothConvexFirstOrder
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (g : E → E) : Prop where
  lowerModel :
    ∀ x y,
      f x + inner ℝ (g x) (y - x) ≤ f y
  upperModel :
    ∀ x y,
      f y ≤
        f x + inner ℝ (g x) (y - x)
          + ((1 : ℝ) / 2) * inner ℝ (y - x) (y - x)

namespace IsOneSmoothConvexAnalytic

variable
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {g : E → E}

/-- The supplied gradient field agrees with mathlib's noncomputable gradient. -/
theorem gradient_eq (h : IsOneSmoothConvexAnalytic f g) :
    gradient f = g :=
  _root_.gradient_eq h.hasGradientAt

/-- The analysis-facing contract implies differentiability everywhere. -/
theorem differentiable (h : IsOneSmoothConvexAnalytic f g) :
    Differentiable ℝ f :=
  fun x => (h.hasGradientAt x).differentiableAt

end IsOneSmoothConvexAnalytic

end ActualFunction
end LeanPEP
