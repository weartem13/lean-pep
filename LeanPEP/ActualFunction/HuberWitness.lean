import LeanPEP.ActualFunction.Basic
import LeanPEP.Toy.FiniteGD.ParametricUpperCertificate
import Mathlib.Tactic

/-!
# One-dimensional Huber-type lower-witness foundations

This file starts the lower-bound side of the arbitrary-length gradient-descent
result.  For a threshold `a : ℝ`, it defines the one-sided Huber-type function

```text
H_a(x) = x^2 / 2                 if x <= a,
         a*x - a^2 / 2           if a <= x,
```

with clipped gradient `min x a`.  The two formulas agree at `x = a`.

The main result of this slice is an exact first-order smooth-convex contract
for the explicit function/gradient pair.  It also instantiates the threshold
`1 / (2N + 1)` suggested by the verified upper certificate and proves
stationarity and global minimality at zero.

This is deliberately not yet the complete actual lower witness.  In
particular, this file does not prove the analytic derivative/Lipschitz API, the
closed-form GD trajectory, or attainment of `1 / (4N + 2)`.
-/

noncomputable section

namespace LeanPEP
namespace ActualFunction
namespace HuberWitness

open Toy.FiniteGD.ParametricUpper

/-- One-sided Huber-type function with quadratic branch to the left of `a` and
linear branch to the right. -/
def huberFunction (a x : ℝ) : ℝ :=
  if x ≤ a then x ^ 2 / 2 else a * x - a ^ 2 / 2

/-- Clipped gradient of `huberFunction`. -/
def huberGradient (a x : ℝ) : ℝ :=
  min x a

@[simp] theorem huberFunction_of_le
    {a x : ℝ} (hx : x ≤ a) :
    huberFunction a x = x ^ 2 / 2 := by
  simp [huberFunction, hx]

/-- The affine formula also holds at the joining point. -/
theorem huberFunction_of_ge
    {a x : ℝ} (hx : a ≤ x) :
    huberFunction a x = a * x - a ^ 2 / 2 := by
  rcases eq_or_lt_of_le hx with hEq | hlt
  · subst x
    simp only [huberFunction, le_rfl, if_true]
    ring
  · simp [huberFunction, not_le.mpr hlt]

@[simp] theorem huberGradient_of_le
    {a x : ℝ} (hx : x ≤ a) :
    huberGradient a x = x := by
  simp [huberGradient, min_eq_left hx]

@[simp] theorem huberGradient_of_ge
    {a x : ℝ} (hx : a ≤ x) :
    huberGradient a x = a := by
  simp [huberGradient, min_eq_right hx]

/-- Supporting-hyperplane inequality for the explicit scalar pair. -/
theorem lowerModel
    (a x y : ℝ) :
    huberFunction a x + huberGradient a x * (y - x) ≤
      huberFunction a y := by
  by_cases hx : x ≤ a
  · have hgx : huberGradient a x = x := huberGradient_of_le hx
    by_cases hy : y ≤ a
    · rw [huberFunction_of_le hx, huberFunction_of_le hy, hgx]
      nlinarith [sq_nonneg (y - x)]
    · have hay : a < y := lt_of_not_ge hy
      rw [huberFunction_of_le hx, huberFunction_of_ge (le_of_lt hay), hgx]
      have hax : 0 ≤ a - x := sub_nonneg.mpr hx
      have hsecond : 0 ≤ 2 * y - a - x := by
        nlinarith
      have hprod : 0 ≤ (a - x) * (2 * y - a - x) :=
        mul_nonneg hax hsecond
      nlinarith
  · have hax : a < x := lt_of_not_ge hx
    have hgx : huberGradient a x = a :=
      huberGradient_of_ge (le_of_lt hax)
    by_cases hy : y ≤ a
    · rw [huberFunction_of_ge (le_of_lt hax), huberFunction_of_le hy, hgx]
      nlinarith [sq_nonneg (y - a)]
    · have hay : a < y := lt_of_not_ge hy
      rw [huberFunction_of_ge (le_of_lt hax),
        huberFunction_of_ge (le_of_lt hay), hgx]
      nlinarith

/-- Unit-smooth quadratic upper model for the explicit scalar pair. -/
theorem upperModel
    (a x y : ℝ) :
    huberFunction a y ≤
      huberFunction a x + huberGradient a x * (y - x) +
        ((1 : ℝ) / 2) * (y - x) ^ 2 := by
  by_cases hx : x ≤ a
  · have hgx : huberGradient a x = x := huberGradient_of_le hx
    by_cases hy : y ≤ a
    · rw [huberFunction_of_le hx, huberFunction_of_le hy, hgx]
      nlinarith
    · have hay : a < y := lt_of_not_ge hy
      rw [huberFunction_of_le hx, huberFunction_of_ge (le_of_lt hay), hgx]
      nlinarith [sq_nonneg (y - a)]
  · have hax : a < x := lt_of_not_ge hx
    have hgx : huberGradient a x = a :=
      huberGradient_of_ge (le_of_lt hax)
    by_cases hy : y ≤ a
    · rw [huberFunction_of_ge (le_of_lt hax), huberFunction_of_le hy, hgx]
      have hxa : 0 ≤ x - a := sub_nonneg.mpr (le_of_lt hax)
      have hsecond : 0 ≤ x + a - 2 * y := by
        nlinarith
      have hprod : 0 ≤ (x - a) * (x + a - 2 * y) :=
        mul_nonneg hxa hsecond
      nlinarith
    · have hay : a < y := lt_of_not_ge hy
      rw [huberFunction_of_ge (le_of_lt hax),
        huberFunction_of_ge (le_of_lt hay), hgx]
      nlinarith [sq_nonneg (y - x)]

/-- Exact normalized first-order smooth-convex contract for the Huber-type
function. -/
theorem firstOrder (a : ℝ) :
    IsOneSmoothConvexFirstOrder (huberFunction a) (huberGradient a) := by
  constructor
  · intro x y
    simpa [RCLike.inner_apply, mul_comm] using lowerModel a x y
  · intro x y
    simpa [RCLike.inner_apply, mul_comm, pow_two] using upperModel a x y

@[simp] theorem huberFunction_zero
    {a : ℝ} (ha : 0 ≤ a) :
    huberFunction a 0 = 0 := by
  simp [huberFunction, ha]

@[simp] theorem huberGradient_zero
    {a : ℝ} (ha : 0 ≤ a) :
    huberGradient a 0 = 0 := by
  simp [huberGradient, min_eq_left ha]

/-- Zero is a global minimizer whenever the threshold is nonnegative. -/
theorem zero_isGlobalMin
    {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    huberFunction a 0 ≤ huberFunction a x := by
  have h := lowerModel a 0 x
  simpa [huberFunction_zero ha, huberGradient_zero ha] using h

/-- The certificate-centered threshold `1 / (2N + 1)`, interpreted in `ℝ`. -/
def threshold (N : ℕ) : ℝ :=
  (1 : ℝ) / (((2 * N + 1 : ℕ) : ℝ))

/-- Parameterized Huber function for an `N`-step lower witness. -/
def witnessFunction (N : ℕ) : ℝ → ℝ :=
  huberFunction (threshold N)

/-- Parameterized clipped gradient for an `N`-step lower witness. -/
def witnessGradient (N : ℕ) : ℝ → ℝ :=
  huberGradient (threshold N)

/-- Candidate closed-form iterate before it is identified with the actual GD
recursion in the next slice. -/
def witnessPoint (N k : ℕ) : ℝ :=
  1 - (k : ℝ) * threshold N

@[simp] theorem witnessPoint_zero (N : ℕ) :
    witnessPoint N 0 = 1 := by
  simp [witnessPoint]

@[simp] theorem witnessPoint_succ (N k : ℕ) :
    witnessPoint N (k + 1) = witnessPoint N k - threshold N := by
  unfold witnessPoint
  push_cast
  ring

/-- The threshold is strictly positive for every trajectory length. -/
theorem threshold_pos (N : ℕ) :
    0 < threshold N := by
  unfold threshold
  positivity

/-- The real threshold agrees with the exact rational center used by the
verified upper certificate. -/
theorem threshold_eq_gdCenterQ_cast (N : ℕ) :
    threshold N = (gdCenterQ N : ℝ) := by
  norm_num [threshold, gdCenterQ]

/-- The parameterized witness satisfies the same normalized first-order class
used by the arbitrary-length upper theorem. -/
theorem witness_firstOrder (N : ℕ) :
    IsOneSmoothConvexFirstOrder (witnessFunction N) (witnessGradient N) := by
  simpa [witnessFunction, witnessGradient] using firstOrder (threshold N)

@[simp] theorem witnessFunction_zero (N : ℕ) :
    witnessFunction N 0 = 0 := by
  simpa [witnessFunction] using
    huberFunction_zero (le_of_lt (threshold_pos N))

@[simp] theorem witnessGradient_zero (N : ℕ) :
    witnessGradient N 0 = 0 := by
  simpa [witnessGradient] using
    huberGradient_zero (le_of_lt (threshold_pos N))

/-- Zero is a global minimizer of every parameterized witness. -/
theorem witness_zero_isGlobalMin (N : ℕ) (x : ℝ) :
    witnessFunction N 0 ≤ witnessFunction N x := by
  simpa [witnessFunction] using
    zero_isGlobalMin (le_of_lt (threshold_pos N)) x

end HuberWitness
end ActualFunction
end LeanPEP
