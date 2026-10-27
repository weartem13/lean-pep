import LeanPEP.Toy.FiniteGD.ParametricUpperGradientCancellation
import Mathlib.Algebra.BigOperators.Fin

/-!
# Ordered gradient-quadratic coefficient reduction

The function-value, constant, and gradient-linear coefficient families of the
closed-form finite-GD certificate are already closed for every trajectory
length.  This module isolates the final coefficient family: the ordered
quadratic coefficients in the sampled gradients.

It projects interpolation slacks and affine-square terms to one ordered matrix
entry, defines the two resulting exact finite rational sums, and proves that
the generated certificate matches the target in the quadratic channel exactly
when those pointwise sums vanish.

This slice is a structural reduction.  It does not yet prove the resulting
finite sums vanish for every ordered pair.  In particular, universal checker
acceptance is not claimed here.
-/

namespace LeanPEP
namespace Toy
namespace FiniteGD
namespace ParametricUpper

open scoped BigOperators

/-- Symbolic point-value variables carry no sampled-gradient-quadratic
coefficient. -/
@[simp] theorem pointValuePolyQ_quadCoeff
    {N : ℕ} (i : Point N) (r s : Fin (N + 1)) :
    (pointValuePolyQ i).quadCoeff r s = 0 := by
  cases i <;> rfl

/-- Ordered sampled-gradient-quadratic projection of one interpolation slack. -/
theorem slackPolyQ_quadCoeff
    {N : ℕ} (i j : Point N) (r s : Fin (N + 1)) :
    (slackPolyQ i j).quadCoeff r s =
      -symOuterQ
          (gradAffineQ j).gradCoeff
          (GradAffineQ.sub (xAffineQ i) (xAffineQ j)).gradCoeff r s -
        ((1 : ℚ) / 2) *
          symOuterQ
            (GradAffineQ.sub
              (gradAffineQ i)
              (gradAffineQ j)).gradCoeff
            (GradAffineQ.sub
              (gradAffineQ i)
              (gradAffineQ j)).gradCoeff r s := by
  simp [slackPolyQ, QuadPolyQ.sub, QuadPolyQ.add, QuadPolyQ.neg,
    QuadPolyQ.scale, QuadPolyQ.square, QuadPolyQ.mulAffine,
    pointValuePolyQ_quadCoeff] <;> ring

/-- Projecting a weighted interpolation list to one ordered quadratic
coefficient produces the corresponding scalar list sum. -/
theorem interpPolySumQ_quadCoeff
    {N : ℕ} (terms : List (InterpTermQ N))
    (r s : Fin (N + 1)) :
    (interpPolySumQ terms).quadCoeff r s =
      (terms.map (fun t =>
        t.weight * (slackPolyQ t.i t.j).quadCoeff r s)).sum := by
  induction terms with
  | nil =>
      rfl
  | cons t ts ih =>
      simp [interpPolySumQ, QuadPolyQ.add, QuadPolyQ.scale, ih]

/-- Ordered quadratic projection commutes with concatenating interpolation
term lists. -/
theorem interpPolySumQ_append_quadCoeff
    {N : ℕ} (left right : List (InterpTermQ N))
    (r s : Fin (N + 1)) :
    (interpPolySumQ (left ++ right)).quadCoeff r s =
      (interpPolySumQ left).quadCoeff r s +
        (interpPolySumQ right).quadCoeff r s := by
  rw [interpPolySumQ_quadCoeff, interpPolySumQ_quadCoeff,
    interpPolySumQ_quadCoeff]
  simp

/-- Projecting a weighted affine-square list to one ordered quadratic
coefficient produces the sum of products of the two gradient coefficients. -/
theorem squarePolySumQ_quadCoeff
    {N : ℕ} (terms : List (SquareTermQ N))
    (r s : Fin (N + 1)) :
    (squarePolySumQ terms).quadCoeff r s =
      (terms.map (fun t =>
        t.weight * (t.form.gradCoeff r * t.form.gradCoeff s))).sum := by
  induction terms with
  | nil =>
      rfl
  | cons t ts ih =>
      change
        t.weight *
              ((t.form.gradCoeff r * t.form.gradCoeff s +
                t.form.gradCoeff r * t.form.gradCoeff s) / 2) +
            (squarePolySumQ ts).quadCoeff r s =
          t.weight * (t.form.gradCoeff r * t.form.gradCoeff s) +
            (ts.map (fun t =>
              t.weight *
                (t.form.gradCoeff r * t.form.gradCoeff s))).sum
      rw [ih]
      ring

/-- Complete ordered quadratic contribution of the generated interpolation
term list. -/
def gdQuadraticInterpSumQ
    (N : ℕ) (r s : Fin (N + 1)) : ℚ :=
  ((gdInterpTermsQ N).map (fun t =>
    t.weight * (slackPolyQ t.i t.j).quadCoeff r s)).sum

/-- Ordered quadratic contribution of one generated affine-square term. -/
def gdQuadraticSquareContributionQ
    (N : ℕ) (r s k : Fin (N + 1)) : ℚ :=
  gdSquareWeightQ N k *
    ((gdSquareFormQ N k).gradCoeff r *
      (gdSquareFormQ N k).gradCoeff s)

/-- Complete ordered quadratic contribution of the generated affine-square
term list. -/
def gdQuadraticSquareSumQ
    (N : ℕ) (r s : Fin (N + 1)) : ℚ :=
  ((List.finRange (N + 1)).map
    (gdQuadraticSquareContributionQ N r s)).sum

/-- The generated interpolation list projects to the explicit ordered
quadratic finite sum above. -/
theorem gdInterpTermsQ_quadCoeff
    (N : ℕ) (r s : Fin (N + 1)) :
    (interpPolySumQ (gdInterpTermsQ N)).quadCoeff r s =
      gdQuadraticInterpSumQ N r s := by
  rw [interpPolySumQ_quadCoeff]
  rfl

/-- The generated affine-square list projects to the explicit ordered
quadratic finite sum above. -/
theorem gdSquareTermsQ_quadCoeff
    (N : ℕ) (r s : Fin (N + 1)) :
    (squarePolySumQ (gdSquareTermsQ N)).quadCoeff r s =
      gdQuadraticSquareSumQ N r s := by
  rw [squarePolySumQ_quadCoeff]
  unfold gdSquareTermsQ gdQuadraticSquareSumQ
    gdQuadraticSquareContributionQ
  rw [List.map_map]
  rfl

/-- Closed structural formula for one ordered quadratic coefficient of the
complete generated certificate. -/
theorem gdCertificateRhs_quadCoeff_eq_quadraticSumsQ
    (N : ℕ) (r s : Fin (N + 1)) :
    (certificateRhsPolyQ (gdUpperCertQ N)).quadCoeff r s =
      gdQuadraticInterpSumQ N r s +
        gdQuadraticSquareSumQ N r s := by
  simp [certificateRhsPolyQ, gdUpperCertQ, QuadPolyQ.add,
    gdInterpTermsQ_quadCoeff, gdSquareTermsQ_quadCoeff]

/-- The target `bound - f_N` contains no sampled-gradient-quadratic term. -/
@[simp] theorem upperTargetPolyQ_quadCoeff
    {N : ℕ} (bound : ℚ) (objective r s : Fin (N + 1)) :
    (upperTargetPolyQ bound objective).quadCoeff r s = 0 := by
  simp [upperTargetPolyQ, QuadPolyQ.sub, QuadPolyQ.add,
    QuadPolyQ.neg, QuadPolyQ.ofAffine, QuadPolyQ.valueVar,
    GradAffineQ.const]

/-- The sole remaining ordered quadratic coefficient obligation after the
preceding coefficient families have been closed. -/
def gdQuadraticCoefficientIdentityQ (N : ℕ) : Prop :=
  ∀ r s : Fin (N + 1),
    gdQuadraticInterpSumQ N r s +
      gdQuadraticSquareSumQ N r s = 0

/-- Equality of every generated and target ordered quadratic coefficient is
precisely the pointwise finite-sum identity exposed above. -/
theorem gdCertificate_quadCoefficients_eq_target_iff
    (N : ℕ) :
    (∀ r s : Fin (N + 1),
      (certificateRhsPolyQ (gdUpperCertQ N)).quadCoeff r s =
        (upperTargetPolyQ
          (gdBoundQ N)
          (gdObjective N)).quadCoeff r s) ↔
      gdQuadraticCoefficientIdentityQ N := by
  unfold gdQuadraticCoefficientIdentityQ
  constructor
  · intro h r s
    rw [← gdCertificateRhs_quadCoeff_eq_quadraticSumsQ]
    simpa using h r s
  · intro h r s
    rw [gdCertificateRhs_quadCoeff_eq_quadraticSumsQ,
      upperTargetPolyQ_quadCoeff]
    exact h r s

/-- The full polynomial identity implies the reduced ordered quadratic
coefficient family. -/
theorem gdQuadraticCoefficientIdentityQ_of_identity
    (N : ℕ) (hidentity : gdCertificateIdentityQ N) :
    gdQuadraticCoefficientIdentityQ N := by
  apply (gdCertificate_quadCoefficients_eq_target_iff N).1
  intro r s
  change
    certificateRhsPolyQ (gdUpperCertQ N) =
      upperTargetPolyQ (gdBoundQ N) (gdObjective N) at hidentity
  exact congrArg (fun p : QuadPolyQ N => p.quadCoeff r s) hidentity

/-- Concrete checker-verified regressions remain compatible with the ordered
quadratic reduction. -/
theorem gdQuadraticCoefficientIdentityQ_0 :
    gdQuadraticCoefficientIdentityQ 0 :=
  gdQuadraticCoefficientIdentityQ_of_identity 0 gdCertificateIdentityQ_0

theorem gdQuadraticCoefficientIdentityQ_4 :
    gdQuadraticCoefficientIdentityQ 4 :=
  gdQuadraticCoefficientIdentityQ_of_identity 4 gdCertificateIdentityQ_4

theorem gdQuadraticCoefficientIdentityQ_8 :
    gdQuadraticCoefficientIdentityQ 8 :=
  gdQuadraticCoefficientIdentityQ_of_identity 8 gdCertificateIdentityQ_8

end ParametricUpper
end FiniteGD
end Toy
end LeanPEP
