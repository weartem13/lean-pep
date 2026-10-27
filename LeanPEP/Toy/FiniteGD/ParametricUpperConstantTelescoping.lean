import LeanPEP.Toy.FiniteGD.ParametricUpperConstantCoefficients

/-!
# Arbitrary-`N` constant-coefficient telescope

`ParametricUpperConstantCoefficients` reduced the constant channel of the
closed-form gradient-descent certificate to the scalar identity

`gdConstantSumQ N = gdBoundQ N`.

This module proves that identity for every natural `N`.  Each nonfinal square
contribution is the difference of two adjacent rational tail potentials, while
the final contribution is the last tail potential.  The finite sum therefore
telescopes to the initial tail, which is exactly `1 / (4 * N + 2)`.

No certificate data, checker, interpolation multiplier, or square factor is
changed here.
-/

namespace LeanPEP
namespace Toy
namespace FiniteGD
namespace ParametricUpper

open scoped BigOperators

/-- Rational tail potential for the reverse-order constant-coefficient
factorization. -/
def gdConstantTailQ (N k : ℕ) : ℚ :=
  (2 * (N : ℚ) - 2 * (k : ℚ) + 1) /
    (2 * (2 * (N : ℚ) - (k : ℚ) + 1) ^ 2)

/-- Pure rational identity behind one nonfinal adjacent tail difference. -/
private theorem gdConstantTail_step_algebra
    (n r : ℚ)
    (hden0 : 2 * n - r ≠ 0)
    (hden1 : 2 * n - r + 1 ≠ 0) :
    ((2 * r * (2 * n - r) + 2 * n + 1) /
        (2 * (2 * n - r) ^ 2)) *
        (-((1 : ℚ) / (2 * n - r + 1))) ^ 2 =
      (2 * n - 2 * r + 1) /
          (2 * (2 * n - r + 1) ^ 2) -
        (2 * n - 2 * (r + 1) + 1) /
          (2 * (2 * n - (r + 1) + 1) ^ 2) := by
  have hden2 : 2 * n - (r + 1) + 1 ≠ 0 := by
    convert hden0 using 1 <;> ring
  field_simp [hden0, hden1, hden2]
  ring

/-- Every nonfinal generated square contribution is one adjacent tail
difference. -/
theorem gdConstantContributionQ_castSucc
    (N : ℕ) (k : Fin N) :
    gdConstantContributionQ N k.castSucc =
      gdConstantTailQ N k.val - gdConstantTailQ N (k.val + 1) := by
  have hne : k.val ≠ N := Nat.ne_of_lt k.isLt
  have hk2N : k.val ≤ 2 * N := by omega
  have hden0 : 2 * (N : ℚ) - (k.val : ℚ) ≠ 0 := by
    have hpos : 0 < 2 * N - k.val := by omega
    have hcast :
        (((2 * N - k.val : ℕ) : ℚ)) =
          2 * (N : ℚ) - (k.val : ℚ) := by
      rw [Nat.cast_sub hk2N]
      push_cast
      rfl
    rw [← hcast]
    positivity
  have hden1 : 2 * (N : ℚ) - (k.val : ℚ) + 1 ≠ 0 := by
    have hcast :
        (((2 * N - k.val + 1 : ℕ) : ℚ)) =
          2 * (N : ℚ) - (k.val : ℚ) + 1 := by
      rw [Nat.cast_add, Nat.cast_sub hk2N]
      push_cast
      rfl
    rw [← hcast]
    positivity
  unfold gdConstantContributionQ gdConstantTailQ
  rw [gdSquareFormQ_constCoeff]
  unfold gdSquareWeightQ
  simp only [Fin.val_castSucc, if_neg hne]
  push_cast [Nat.cast_sub hk2N]
  simpa using
    gdConstantTail_step_algebra
      (N : ℚ) (k.val : ℚ) hden0 hden1

/-- The final generated square contribution is the final tail potential. -/
theorem gdConstantContributionQ_last
    (N : ℕ) :
    gdConstantContributionQ N (Fin.last N) =
      gdConstantTailQ N N := by
  have hdenNat : 2 * N - N + 1 = N + 1 := by omega
  have hden : (N : ℚ) + 1 ≠ 0 := by positivity
  have hdenCast : (((N + 1 : ℕ) : ℚ)) ≠ 0 := by positivity
  unfold gdConstantContributionQ gdConstantTailQ
  rw [gdSquareFormQ_constCoeff]
  unfold gdSquareWeightQ
  simp only [Fin.val_last, if_pos rfl, hdenNat]
  field_simp [hden, hdenCast]
  push_cast
  ring

/-- The initial tail potential is the target upper bound. -/
theorem gdConstantTailQ_zero_eq_bound
    (N : ℕ) :
    gdConstantTailQ N 0 = gdBoundQ N := by
  have hcenter : 2 * (N : ℚ) + 1 ≠ 0 := by positivity
  have hbound : (((4 * N + 2 : ℕ) : ℚ)) ≠ 0 := by positivity
  unfold gdConstantTailQ gdBoundQ
  field_simp [hcenter, hbound]
  push_cast
  ring

/-- The list-defined scalar constant sum is the corresponding `Fin` sum. -/
theorem gdConstantSumQ_eq_fin_sum
    (N : ℕ) :
    gdConstantSumQ N =
      ∑ k : Fin (N + 1), gdConstantContributionQ N k := by
  unfold gdConstantSumQ
  symm
  exact Fin.sum_univ_def (gdConstantContributionQ N)

/-- The complete reverse-order constant contribution telescopes to the target
bound. -/
theorem gdConstantContributions_sum
    (N : ℕ) :
    (∑ k : Fin (N + 1), gdConstantContributionQ N k) =
      gdBoundQ N := by
  rw [Fin.sum_univ_castSucc]
  have hprefix :
      (∑ k : Fin N, gdConstantContributionQ N k.castSucc) =
        ∑ k : Fin N,
          (gdConstantTailQ N k.val -
            gdConstantTailQ N (k.val + 1)) := by
    apply Finset.sum_congr rfl
    intro k _hk
    exact gdConstantContributionQ_castSucc N k
  rw [hprefix, gdConstantContributionQ_last]
  calc
    (∑ k : Fin N,
          (gdConstantTailQ N k.val -
            gdConstantTailQ N (k.val + 1))) +
        gdConstantTailQ N N =
      (∑ k ∈ Finset.range N,
          (gdConstantTailQ N k -
            gdConstantTailQ N (k + 1))) +
        gdConstantTailQ N N := by
      rw [Finset.sum_range]
    _ = (gdConstantTailQ N 0 - gdConstantTailQ N N) +
          gdConstantTailQ N N := by
      rw [Finset.sum_range_sub']
    _ = gdConstantTailQ N 0 := by ring
    _ = gdBoundQ N := gdConstantTailQ_zero_eq_bound N

/-- The reduced constant-channel scalar identity holds for every trajectory
length. -/
theorem gdConstantCoefficientIdentityQ_all
    (N : ℕ) :
    gdConstantCoefficientIdentityQ N := by
  unfold gdConstantCoefficientIdentityQ
  rw [gdConstantSumQ_eq_fin_sum, gdConstantContributions_sum]

/-- The constant coefficient of the arbitrary-length generated certificate
matches the target polynomial. -/
theorem gdCertificate_constCoeff
    (N : ℕ) :
    (certificateRhsPolyQ (gdUpperCertQ N)).constCoeff =
      (upperTargetPolyQ
        (gdBoundQ N)
        (gdObjective N)).constCoeff :=
  (gdCertificate_constCoeff_eq_target_iff N).2
    (gdConstantCoefficientIdentityQ_all N)

end ParametricUpper
end FiniteGD
end Toy
end LeanPEP
