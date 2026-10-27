import LeanPEP.Toy.TwoStep.Data

/-!
# Exact upper certificate for the normalized two-step finite PEP

The proof is organized around one explicit algebraic identity.  Five scalar
interpolation inequalities occur with nonnegative rational multipliers, and the
remainder is an exact rational sum of squares.
-/

namespace LeanPEP
namespace Toy
namespace TwoStep

/-- Exact certificate identity behind the `1 / 10` upper bound.

The interpolation multipliers are

* `1/4` on `(star,p0)` and `(p0,p1)`;
* `2/3` in total on `(p1,p2)`;
* `5/12` on `(star,p1)`;
* `1/3` on `(star,p2)`.

The displayed grouping records the three trajectory upper bounds from which
these multipliers arise. -/
theorem twoStep_certificate_identity (d : TwoStepData) :
    (1 : ℝ) / 10 - d.value 2 =
      ((1 : ℝ) / 4) *
        (FiniteGD.slack d star p0
          + FiniteGD.slack d p0 p1
          + FiniteGD.slack d p1 p2)
      + ((5 : ℝ) / 12) *
        (FiniteGD.slack d star p1
          + FiniteGD.slack d p1 p2)
      + ((1 : ℝ) / 3) * FiniteGD.slack d star p2
      + ((2 : ℝ) / 3) *
        ((d.grad 1 - (1 : ℝ) / 5)
          + ((1 : ℝ) / 4) * (d.grad 2 - (1 : ℝ) / 5)
          + ((5 : ℝ) / 16) * (d.grad 0 - (1 : ℝ) / 5))^2
      + ((11 : ℝ) / 24) *
        ((d.grad 2 - (1 : ℝ) / 5)
          + ((1 : ℝ) / 4) * (d.grad 0 - (1 : ℝ) / 5))^2
      + ((5 : ℝ) / 32) *
        (d.grad 0 - (1 : ℝ) / 5)^2 := by
  simp [FiniteGD.slack, star]
  ring

/-- Every feasible normalized two-step finite PEP datum satisfies
`f₂ ≤ 1 / 10`. -/
theorem twoStep_upper
    (d : TwoStepData)
    (h : FiniteGD.Feasible d) :
    d.value 2 ≤ (1 : ℝ) / 10 := by
  have hs0 : 0 ≤ FiniteGD.slack d star p0 := h star p0
  have h01 : 0 ≤ FiniteGD.slack d p0 p1 := h p0 p1
  have h12 : 0 ≤ FiniteGD.slack d p1 p2 := h p1 p2
  have hs1 : 0 ≤ FiniteGD.slack d star p1 := h star p1
  have hs2 : 0 ≤ FiniteGD.slack d star p2 := h star p2

  have hinterp :
      0 ≤
        ((1 : ℝ) / 4) *
          (FiniteGD.slack d star p0
            + FiniteGD.slack d p0 p1
            + FiniteGD.slack d p1 p2)
        + ((5 : ℝ) / 12) *
          (FiniteGD.slack d star p1
            + FiniteGD.slack d p1 p2)
        + ((1 : ℝ) / 3) * FiniteGD.slack d star p2 := by
    nlinarith [hs0, h01, h12, hs1, hs2]

  have hsquares :
      0 ≤
        ((2 : ℝ) / 3) *
          ((d.grad 1 - (1 : ℝ) / 5)
            + ((1 : ℝ) / 4) * (d.grad 2 - (1 : ℝ) / 5)
            + ((5 : ℝ) / 16) * (d.grad 0 - (1 : ℝ) / 5))^2
        + ((11 : ℝ) / 24) *
          ((d.grad 2 - (1 : ℝ) / 5)
            + ((1 : ℝ) / 4) * (d.grad 0 - (1 : ℝ) / 5))^2
        + ((5 : ℝ) / 32) *
          (d.grad 0 - (1 : ℝ) / 5)^2 := by
    positivity

  have hid := twoStep_certificate_identity d
  nlinarith

end TwoStep
end Toy
end LeanPEP
