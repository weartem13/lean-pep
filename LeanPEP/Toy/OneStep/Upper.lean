import LeanPEP.Toy.OneStep.Data

/-!
# Upper bound for the normalized one-dimensional one-step finite PEP

The main theorem in this file proves that every finite feasible datum satisfies
`f_1 ≤ 1 / 6`.
-/

namespace LeanPEP
namespace Toy
namespace OneStep

/-- The elementary quadratic inequality used in the one-step upper bound.

It is the exact rational identity

`1 / 6 - 1 / 2 * (g0 + g1 - g0^2 - g0*g1 - g1^2)
 = 1 / 2 * ((g0 - 1/3)^2 + (g0 - 1/3)*(g1 - 1/3) + (g1 - 1/3)^2)`

combined with

`a^2 + a*b + b^2 = (a^2 + b^2 + (a+b)^2) / 2 ≥ 0`.
-/
lemma quadratic_oneStep_bound (g0 g1 : ℝ) :
    ((1 : ℝ) / 2) * (g0 + g1 - g0^2 - g0 * g1 - g1^2) ≤ (1 : ℝ) / 6 := by
  nlinarith [
    sq_nonneg (g0 - (1 : ℝ) / 3),
    sq_nonneg (g1 - (1 : ℝ) / 3),
    sq_nonneg ((g0 - (1 : ℝ) / 3) + (g1 - (1 : ℝ) / 3))]

/-- The exact upper bound for the normalized one-dimensional one-step finite PEP. -/
theorem oneStep_upper
    (d : OneStepData)
    (h : OneStepFeasible d) :
    d.f1 ≤ (1 : ℝ) / 6 := by
  -- Interpolation from `star` to `p1`:
  -- `f1 ≤ g1 * (1 - g0) - (1/2) * g1^2`.
  have h_star_p1 : 0 ≤ slack d Pt.star Pt.p1 := h.interp Pt.star Pt.p1
  -- Interpolation from `star` to `p0`:
  -- `f0 ≤ g0 - (1/2) * g0^2`.
  have h_star_p0 : 0 ≤ slack d Pt.star Pt.p0 := h.interp Pt.star Pt.p0
  -- Interpolation from `p0` to `p1`:
  -- `f1 ≤ f0 - g0 * g1 - (1/2) * (g0 - g1)^2`.
  have h_p0_p1 : 0 ≤ slack d Pt.p0 Pt.p1 := h.interp Pt.p0 Pt.p1
  simp [slack, x, grad, val] at h_star_p1 h_star_p0 h_p0_p1

  have h_from_star_p1 :
      d.f1 ≤ d.g1 * (1 - d.g0) - ((1 : ℝ) / 2) * d.g1^2 := by
    nlinarith [h_star_p1]

  have h_from_star_p0_p0_p1 :
      d.f1 ≤ d.g0 - d.g0^2 - ((1 : ℝ) / 2) * d.g1^2 := by
    nlinarith [h_star_p0, h_p0_p1]

  have h_avg :
      d.f1 ≤ ((1 : ℝ) / 2) *
        (d.g0 + d.g1 - d.g0^2 - d.g0 * d.g1 - d.g1^2) := by
    nlinarith [h_from_star_p1, h_from_star_p0_p0_p1]

  exact le_trans h_avg (quadratic_oneStep_bound d.g0 d.g1)

end OneStep
end Toy
end LeanPEP
