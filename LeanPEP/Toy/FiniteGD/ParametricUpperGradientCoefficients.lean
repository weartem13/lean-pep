import LeanPEP.Toy.FiniteGD.ParametricUpperConstantTelescoping
import Mathlib.Algebra.BigOperators.Fin

/-!
# Gradient-linear coefficient reduction for the arbitrary-length GD certificate

The function-value and constant channels of the closed-form finite-GD
certificate are already closed for every trajectory length.  This module
isolates the next coefficient family: coefficients that are linear in the
sampled gradients.

The generated interpolation list contributes exactly the star-to-iterate
weight at each gradient index.  The consecutive-iterate interpolation terms
have no gradient-linear contribution because both symbolic iterate positions
have affine constant term `1`.  The square list contributes an explicit finite
sum of the linear coefficients of the weighted affine squares.

Consequently, equality of all gradient-linear coefficients is reduced to one
explicit rational identity at each sampled gradient index.  This module does
not yet prove those finite sums vanish for every `N`; that telescope is kept as
its own subsequent algebraic slice.
-/

namespace LeanPEP
namespace Toy
namespace FiniteGD
namespace ParametricUpper

open scoped BigOperators

/-- Symbolic function-value variables carry no sampled-gradient coefficient. -/
@[simp] theorem pointValuePolyQ_gradCoeff
    {N : ℕ} (i : Point N) (r : Fin (N + 1)) :
    (pointValuePolyQ i).gradCoeff r = 0 := by
  cases i <;> rfl

/-- Gradient-linear projection of one symbolic interpolation slack.

Only `-g_j * (x_i - x_j)` can contribute linearly in the sampled gradients:
the function-value terms have no gradient variables, while
`(g_i - g_j)^2` has zero affine constant term. -/
theorem slackPolyQ_gradCoeff
    {N : ℕ} (i j : Point N) (r : Fin (N + 1)) :
    (slackPolyQ i j).gradCoeff r =
      -(GradAffineQ.sub (xAffineQ i) (xAffineQ j)).constCoeff *
        (gradAffineQ j).gradCoeff r := by
  simp [slackPolyQ, QuadPolyQ.sub, QuadPolyQ.add, QuadPolyQ.neg,
    QuadPolyQ.scale, QuadPolyQ.square, QuadPolyQ.mulAffine,
    GradAffineQ.sub, GradAffineQ.add, GradAffineQ.neg,
    pointValuePolyQ_gradCoeff, gradAffineQ_constCoeff] <;> ring

/-- A star-to-iterate interpolation slack contributes the corresponding unit
gradient coefficient. -/
@[simp] theorem slackPolyQ_star_iter_gradCoeff
    (N : ℕ) (k r : Fin (N + 1)) :
    (slackPolyQ (Point.star : Point N) (Point.iter k)).gradCoeff r =
      unitCoeff k r := by
  rw [slackPolyQ_gradCoeff]
  simp [xAffineQ, gradAffineQ, GradAffineQ.sub, GradAffineQ.add,
    GradAffineQ.neg, GradAffineQ.zero, GradAffineQ.const,
    GradAffineQ.basis, prefixAffine_constCoeff]

/-- Any iterate-to-iterate interpolation slack has no gradient-linear term:
both symbolic iterate positions have affine constant term `1`. -/
@[simp] theorem slackPolyQ_iter_iter_gradCoeff
    (N : ℕ) (i j r : Fin (N + 1)) :
    (slackPolyQ (Point.iter i) (Point.iter j)).gradCoeff r = 0 := by
  rw [slackPolyQ_gradCoeff]
  simp [xAffineQ, gradAffineQ, GradAffineQ.sub, GradAffineQ.add,
    GradAffineQ.neg, GradAffineQ.const, GradAffineQ.basis,
    prefixAffine_constCoeff]

/-- Projecting a weighted interpolation list to one gradient-linear
coefficient produces the corresponding scalar list sum. -/
theorem interpPolySumQ_gradCoeff
    {N : ℕ} (terms : List (InterpTermQ N)) (r : Fin (N + 1)) :
    (interpPolySumQ terms).gradCoeff r =
      (terms.map (fun t =>
        t.weight * (slackPolyQ t.i t.j).gradCoeff r)).sum := by
  induction terms with
  | nil =>
      rfl
  | cons t ts ih =>
      simp [interpPolySumQ, QuadPolyQ.add, QuadPolyQ.scale, ih]

/-- Gradient-linear projection commutes with concatenating interpolation-term
lists. -/
theorem interpPolySumQ_append_gradCoeff
    {N : ℕ} (left right : List (InterpTermQ N))
    (r : Fin (N + 1)) :
    (interpPolySumQ (left ++ right)).gradCoeff r =
      (interpPolySumQ left).gradCoeff r +
        (interpPolySumQ right).gradCoeff r := by
  rw [interpPolySumQ_gradCoeff, interpPolySumQ_gradCoeff,
    interpPolySumQ_gradCoeff]
  simp

/-- The star interpolation list contributes exactly its star weight at the
corresponding sampled-gradient index. -/
theorem gdStarTermsQ_gradCoeff
    (N : ℕ) (r : Fin (N + 1)) :
    (interpPolySumQ (gdStarTermsQ N)).gradCoeff r =
      gdStarWeightQ N r := by
  classical
  rw [interpPolySumQ_gradCoeff]
  simp only [gdStarTermsQ, List.map_map, Function.comp_apply,
    slackPolyQ_star_iter_gradCoeff]
  rw [← Fin.sum_univ_def]
  rw [Fintype.sum_eq_single r (by
    intro k hkr
    simp [unitCoeff, hkr, Ne.symm hkr])]
  simp [unitCoeff]

/-- The consecutive-iterate interpolation list has no gradient-linear
coefficient. -/
theorem gdChainTermsQ_gradCoeff
    (N : ℕ) (r : Fin (N + 1)) :
    (interpPolySumQ (gdChainTermsQ N)).gradCoeff r = 0 := by
  rw [interpPolySumQ_gradCoeff]
  simp only [gdChainTermsQ, List.map_map]
  rw [← Fin.sum_univ_def]
  apply Finset.sum_eq_zero
  intro k hk
  simp only [Function.comp_apply, slackPolyQ_iter_iter_gradCoeff, mul_zero]

/-- The complete generated interpolation list contributes exactly the
star-to-iterate weight at each sampled-gradient index. -/
theorem gdInterpTermsQ_gradCoeff
    (N : ℕ) (r : Fin (N + 1)) :
    (interpPolySumQ (gdInterpTermsQ N)).gradCoeff r =
      gdStarWeightQ N r := by
  rw [gdInterpTermsQ, interpPolySumQ_append_gradCoeff,
    gdStarTermsQ_gradCoeff, gdChainTermsQ_gradCoeff]
  simp

/-- Projecting a weighted affine-square list to one gradient-linear
coefficient produces the sum of `2 * weight * constant * gradientCoeff`. -/
theorem squarePolySumQ_gradCoeff
    {N : ℕ} (terms : List (SquareTermQ N)) (r : Fin (N + 1)) :
    (squarePolySumQ terms).gradCoeff r =
      (terms.map (fun t =>
        t.weight *
          (2 * t.form.constCoeff * t.form.gradCoeff r))).sum := by
  induction terms with
  | nil =>
      rfl
  | cons t ts ih =>
      change
        t.weight *
              (t.form.constCoeff * t.form.gradCoeff r +
                t.form.constCoeff * t.form.gradCoeff r) +
            (squarePolySumQ ts).gradCoeff r =
          t.weight *
              (2 * t.form.constCoeff * t.form.gradCoeff r) +
            (ts.map (fun t =>
              t.weight *
                (2 * t.form.constCoeff * t.form.gradCoeff r))).sum
      rw [ih]
      ring

/-- Gradient-linear contribution of one generated square term at sampled
index `r`. -/
def gdGradientSquareContributionQ
    (N : ℕ) (r k : Fin (N + 1)) : ℚ :=
  gdSquareWeightQ N k *
    (2 * (gdSquareFormQ N k).constCoeff *
      (gdSquareFormQ N k).gradCoeff r)

/-- Complete gradient-linear contribution of the generated square list at
sampled index `r`. -/
def gdGradientSquareSumQ
    (N : ℕ) (r : Fin (N + 1)) : ℚ :=
  ((List.finRange (N + 1)).map
    (gdGradientSquareContributionQ N r)).sum

/-- The generated square-term list projects to the explicit finite rational
sum above. -/
theorem gdSquareTermsQ_gradCoeff
    (N : ℕ) (r : Fin (N + 1)) :
    (squarePolySumQ (gdSquareTermsQ N)).gradCoeff r =
      gdGradientSquareSumQ N r := by
  rw [squarePolySumQ_gradCoeff]
  unfold gdSquareTermsQ gdGradientSquareSumQ
    gdGradientSquareContributionQ
  rw [List.map_map]
  rfl

/-- Closed structural formula for the complete generated certificate's
sampled-gradient coefficient. -/
theorem gdCertificateRhs_gradCoeff_eq_gradientSumQ
    (N : ℕ) (r : Fin (N + 1)) :
    (certificateRhsPolyQ (gdUpperCertQ N)).gradCoeff r =
      gdStarWeightQ N r + gdGradientSquareSumQ N r := by
  simp [certificateRhsPolyQ, gdUpperCertQ, QuadPolyQ.add,
    gdInterpTermsQ_gradCoeff, gdSquareTermsQ_gradCoeff]

/-- The target `bound - f_N` contains no sampled-gradient-linear term. -/
@[simp] theorem upperTargetPolyQ_gradCoeff
    {N : ℕ} (bound : ℚ) (objective r : Fin (N + 1)) :
    (upperTargetPolyQ bound objective).gradCoeff r = 0 := by
  simp [upperTargetPolyQ, QuadPolyQ.sub, QuadPolyQ.add,
    QuadPolyQ.neg, QuadPolyQ.ofAffine, QuadPolyQ.valueVar,
    GradAffineQ.const]

/-- The remaining explicit finite-sum obligation for the gradient-linear
coefficient family. -/
def gdGradientCoefficientIdentityQ (N : ℕ) : Prop :=
  ∀ r : Fin (N + 1),
    gdStarWeightQ N r + gdGradientSquareSumQ N r = 0

/-- Equality of every generated and target gradient-linear coefficient is
precisely the pointwise finite-sum identity exposed above. -/
theorem gdCertificate_gradCoefficients_eq_target_iff
    (N : ℕ) :
    (∀ r : Fin (N + 1),
      (certificateRhsPolyQ (gdUpperCertQ N)).gradCoeff r =
        (upperTargetPolyQ
          (gdBoundQ N)
          (gdObjective N)).gradCoeff r) ↔
      gdGradientCoefficientIdentityQ N := by
  simp [gdGradientCoefficientIdentityQ,
    gdCertificateRhs_gradCoeff_eq_gradientSumQ]

/-- The full polynomial identity implies the reduced gradient-linear family. -/
theorem gdGradientCoefficientIdentityQ_of_identity
    (N : ℕ) (hidentity : gdCertificateIdentityQ N) :
    gdGradientCoefficientIdentityQ N := by
  apply (gdCertificate_gradCoefficients_eq_target_iff N).1
  intro r
  change
    certificateRhsPolyQ (gdUpperCertQ N) =
      upperTargetPolyQ (gdBoundQ N) (gdObjective N) at hidentity
  exact congrArg (fun p : QuadPolyQ N => p.gradCoeff r) hidentity

/-- Concrete checker-verified regressions remain compatible with the
pointwise gradient-linear reduction. -/
theorem gdGradientCoefficientIdentityQ_0 :
    gdGradientCoefficientIdentityQ 0 :=
  gdGradientCoefficientIdentityQ_of_identity 0 gdCertificateIdentityQ_0

theorem gdGradientCoefficientIdentityQ_4 :
    gdGradientCoefficientIdentityQ 4 :=
  gdGradientCoefficientIdentityQ_of_identity 4 gdCertificateIdentityQ_4

theorem gdGradientCoefficientIdentityQ_8 :
    gdGradientCoefficientIdentityQ 8 :=
  gdGradientCoefficientIdentityQ_of_identity 8 gdCertificateIdentityQ_8

end ParametricUpper
end FiniteGD
end Toy
end LeanPEP
