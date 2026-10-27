import LeanPEP.Toy.FiniteGD.ParametricUpperValueCoefficients

/-!
# Constant-coefficient reduction for the arbitrary-length GD certificate

The function-value channel of the closed-form certificate is already closed in
`ParametricUpperValueCoefficients`.  This module isolates the next coefficient
channel.

It proves that interpolation slacks contribute no constant coefficient, that
the constant coefficient of the generated affine-square factor at index `k` is

`-1 / (2 * N - k + 1)`,

and that the complete certificate constant coefficient is one explicit finite
rational sum of the generated square contributions.  Consequently the constant
channel is equivalent to a single scalar summation identity.  This slice does
not yet prove that summation identity for every `N`.
-/

namespace LeanPEP
namespace Toy
namespace FiniteGD
namespace ParametricUpper

open scoped BigOperators

/-- Symbolic point values have no constant term. -/
@[simp] theorem pointValuePolyQ_constCoeff
    {N : ℕ} (i : Point N) :
    (pointValuePolyQ i).constCoeff = 0 := by
  cases i <;> rfl

/-- Symbolic point gradients have no affine constant term. -/
@[simp] theorem gradAffineQ_constCoeff
    {N : ℕ} (i : Point N) :
    (gradAffineQ i).constCoeff = 0 := by
  cases i <;> rfl

/-- Every symbolic interpolation slack has zero constant coefficient. -/
@[simp] theorem slackPolyQ_constCoeff
    {N : ℕ} (i j : Point N) :
    (slackPolyQ i j).constCoeff = 0 := by
  simp [slackPolyQ, QuadPolyQ.sub, QuadPolyQ.add, QuadPolyQ.neg,
    QuadPolyQ.scale, QuadPolyQ.square, QuadPolyQ.mulAffine,
    GradAffineQ.sub, GradAffineQ.add, GradAffineQ.neg]

/-- Any weighted interpolation sum has zero constant coefficient. -/
@[simp] theorem interpPolySumQ_constCoeff
    {N : ℕ} (terms : List (InterpTermQ N)) :
    (interpPolySumQ terms).constCoeff = 0 := by
  induction terms with
  | nil =>
      rfl
  | cons t ts ih =>
      simp [interpPolySumQ, QuadPolyQ.add, QuadPolyQ.scale, ih]

/-- Projecting the constant coefficient through a weighted affine-square list
produces the corresponding scalar sum. -/
theorem squarePolySumQ_constCoeff
    {N : ℕ} (terms : List (SquareTermQ N)) :
    (squarePolySumQ terms).constCoeff =
      (terms.map (fun t => t.weight * t.form.constCoeff ^ 2)).sum := by
  induction terms with
  | nil =>
      rfl
  | cons t ts ih =>
      simp [squarePolySumQ, QuadPolyQ.add, QuadPolyQ.scale,
        QuadPolyQ.square, QuadPolyQ.mulAffine, ih, pow_two]

/-- The certificate constant coefficient comes entirely from its square terms. -/
theorem certificateRhsPolyQ_constCoeff
    {N : ℕ} (c : UpperCertQ N) :
    (certificateRhsPolyQ c).constCoeff =
      (squarePolySumQ c.squareTerms).constCoeff := by
  simp [certificateRhsPolyQ, QuadPolyQ.add]

/-- The target polynomial has constant coefficient equal to its bound. -/
@[simp] theorem upperTargetPolyQ_constCoeff
    {N : ℕ} (bound : ℚ) (objective : Fin (N + 1)) :
    (upperTargetPolyQ bound objective).constCoeff = bound := by
  simp [upperTargetPolyQ, QuadPolyQ.sub, QuadPolyQ.add, QuadPolyQ.neg,
    QuadPolyQ.ofAffine, QuadPolyQ.valueVar, GradAffineQ.const]

/-- Every prefix of sampled gradient variables has affine constant term zero. -/
theorem prefixAffine_constCoeff
    {N : ℕ} :
    ∀ (k : ℕ) (hk : k ≤ N + 1),
      (GradAffineQ.prefixAffine k hk).constCoeff = 0 := by
  intro k
  induction k with
  | zero =>
      intro hk
      rfl
  | succ k ih =>
      intro hk
      change
        (GradAffineQ.prefixAffine k
              (Nat.le_trans (Nat.le_succ k) hk)).constCoeff + 0 = 0
      rw [ih (Nat.le_trans (Nat.le_succ k) hk)]
      simp

/-- The centered sampled gradient has constant term `-q`. -/
theorem gdCenteredGradQ_constCoeff
    (N : ℕ) (k : Fin (N + 1)) :
    (gdCenteredGradQ N k).constCoeff = -gdCenterQ N := by
  simp [gdCenteredGradQ, GradAffineQ.sub, GradAffineQ.add,
    GradAffineQ.neg, GradAffineQ.basis, GradAffineQ.const]

/-- The centered gradient prefix has constant term `-kq`. -/
theorem gdCenteredPrefixQ_constCoeff
    (N : ℕ) (k : Fin (N + 1)) :
    (gdCenteredPrefixQ N k).constCoeff =
      -(((k.val : ℕ) : ℚ) * gdCenterQ N) := by
  simp [gdCenteredPrefixQ, GradAffineQ.sub, GradAffineQ.add,
    GradAffineQ.neg, GradAffineQ.const, prefixAffine_constCoeff]

/-- Closed form of the affine constant in the `k`-th reverse-LDL square
factor. -/
theorem gdSquareFormQ_constCoeff
    (N : ℕ) (k : Fin (N + 1)) :
    (gdSquareFormQ N k).constCoeff =
      -((1 : ℚ) / (((2 * N - k.val + 1 : ℕ) : ℚ))) := by
  have hsumNat :
      (2 * N - k.val + 1) + k.val = 2 * N + 1 := by
    omega
  have hsumQ :
      (((2 * N - k.val + 1 : ℕ) : ℚ)) + ((k.val : ℕ) : ℚ) =
        (((2 * N + 1 : ℕ) : ℚ)) := by
    exact_mod_cast hsumNat
  have hden : (((2 * N - k.val + 1 : ℕ) : ℚ)) ≠ 0 := by
    positivity
  have hsumDen :
      (((2 * N - k.val + 1 : ℕ) : ℚ)) + ((k.val : ℕ) : ℚ) ≠ 0 := by
    positivity
  change
    (gdCenteredGradQ N k).constCoeff +
        ((1 : ℚ) / (((2 * N - k.val + 1 : ℕ) : ℚ))) *
          (gdCenteredPrefixQ N k).constCoeff =
      -((1 : ℚ) / (((2 * N - k.val + 1 : ℕ) : ℚ)))
  rw [gdCenteredGradQ_constCoeff, gdCenteredPrefixQ_constCoeff]
  unfold gdCenterQ
  rw [← hsumQ]
  field_simp [hden, hsumDen]
  ring

/-- Constant contribution of one generated square term. -/
def gdConstantContributionQ
    (N : ℕ) (k : Fin (N + 1)) : ℚ :=
  gdSquareWeightQ N k * (gdSquareFormQ N k).constCoeff ^ 2

/-- Complete constant contribution of the generated square-term list. -/
def gdConstantSumQ (N : ℕ) : ℚ :=
  ((List.finRange (N + 1)).map (gdConstantContributionQ N)).sum

/-- The one-term constant contribution has an explicit reciprocal-square
form. -/
theorem gdConstantContributionQ_closed
    (N : ℕ) (k : Fin (N + 1)) :
    gdConstantContributionQ N k =
      gdSquareWeightQ N k *
        (((1 : ℚ) / (((2 * N - k.val + 1 : ℕ) : ℚ))) ^ 2) := by
  unfold gdConstantContributionQ
  rw [gdSquareFormQ_constCoeff]
  ring

/-- The complete generated certificate constant coefficient is exactly the
explicit finite square-contribution sum. -/
theorem gdCertificateRhs_constCoeff_eq_constantSumQ
    (N : ℕ) :
    (certificateRhsPolyQ (gdUpperCertQ N)).constCoeff =
      gdConstantSumQ N := by
  rw [certificateRhsPolyQ_constCoeff, squarePolySumQ_constCoeff]
  unfold gdUpperCertQ gdSquareTermsQ gdConstantSumQ gdConstantContributionQ
  rw [List.map_map]
  rfl

/-- The remaining scalar summation obligation for the constant channel. -/
def gdConstantCoefficientIdentityQ (N : ℕ) : Prop :=
  gdConstantSumQ N = gdBoundQ N

/-- Exact equality of the certificate and target constant coefficients is
precisely the scalar summation identity exposed above. -/
theorem gdCertificate_constCoeff_eq_target_iff
    (N : ℕ) :
    (certificateRhsPolyQ (gdUpperCertQ N)).constCoeff =
        (upperTargetPolyQ (gdBoundQ N) (gdObjective N)).constCoeff ↔
      gdConstantCoefficientIdentityQ N := by
  simp [gdCertificateRhs_constCoeff_eq_constantSumQ,
    gdConstantCoefficientIdentityQ]

/-- The full polynomial identity implies the reduced constant-channel
identity. -/
theorem gdConstantCoefficientIdentityQ_of_identity
    (N : ℕ) (hidentity : gdCertificateIdentityQ N) :
    gdConstantCoefficientIdentityQ N := by
  change
    certificateRhsPolyQ (gdUpperCertQ N) =
      upperTargetPolyQ (gdBoundQ N) (gdObjective N) at hidentity
  exact (gdCertificate_constCoeff_eq_target_iff N).1
    (congrArg QuadPolyQ.constCoeff hidentity)

/-- Concrete B2/B3 regressions remain compatible with the constant-channel
reduction. -/
theorem gdConstantCoefficientIdentityQ_0 :
    gdConstantCoefficientIdentityQ 0 :=
  gdConstantCoefficientIdentityQ_of_identity 0 gdCertificateIdentityQ_0

theorem gdConstantCoefficientIdentityQ_4 :
    gdConstantCoefficientIdentityQ 4 :=
  gdConstantCoefficientIdentityQ_of_identity 4 gdCertificateIdentityQ_4

theorem gdConstantCoefficientIdentityQ_8 :
    gdConstantCoefficientIdentityQ 8 :=
  gdConstantCoefficientIdentityQ_of_identity 8 gdCertificateIdentityQ_8

end ParametricUpper
end FiniteGD
end Toy
end LeanPEP
