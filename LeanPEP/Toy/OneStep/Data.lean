import Mathlib.Tactic

/-!
# Normalized one-dimensional one-step finite PEP data

This file contains only the finite PEP semantics for the normalized one-step
problem.  It does not formalize Fréchet differentiability, global smoothness of
real functions, or the smooth convex interpolation theorem.
-/

namespace LeanPEP
namespace Toy
namespace OneStep

/-- The three finite interpolation points: optimum, initial point, and one
post-gradient-descent point. -/
inductive Pt where
  | star
  | p0
  | p1
  deriving DecidableEq, Repr

/-- Finite one-step PEP data after the normalizations
`x_star = 0`, `g_star = 0`, `f_star = 0`, `x_0 = 1`, and
`x_1 = x_0 - g_0 = 1 - g_0`. -/
@[ext]
structure OneStepData where
  g0 : ℝ
  g1 : ℝ
  f0 : ℝ
  f1 : ℝ

/-- Position of each finite point. -/
def x (d : OneStepData) : Pt → ℝ
  | Pt.star => 0
  | Pt.p0 => 1
  | Pt.p1 => 1 - d.g0

/-- Gradient value attached to each finite point. -/
def grad (d : OneStepData) : Pt → ℝ
  | Pt.star => 0
  | Pt.p0 => d.g0
  | Pt.p1 => d.g1

/-- Function value attached to each finite point. -/
def val (d : OneStepData) : Pt → ℝ
  | Pt.star => 0
  | Pt.p0 => d.f0
  | Pt.p1 => d.f1

/-- Pairwise scalar interpolation slack for 1-smooth convex functions.

The finite interpolation condition is `0 ≤ slack d i j` for every ordered pair
of points `i, j`.  This is deliberately a scalar inequality, not a PSD condition
on a matrix of slacks. -/
noncomputable def slack (d : OneStepData) (i j : Pt) : ℝ :=
  val d i - val d j
    - grad d j * (x d i - x d j)
    - ((1 : ℝ) / 2) * (grad d i - grad d j)^2

/-- Feasibility for the finite one-step PEP instance. -/
structure OneStepFeasible (d : OneStepData) : Prop where
  interp : ∀ i j : Pt, 0 ≤ slack d i j

end OneStep
end Toy
end LeanPEP
