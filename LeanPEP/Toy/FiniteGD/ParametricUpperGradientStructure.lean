import LeanPEP.Toy.FiniteGD.ParametricUpperGradientCoefficients
import Mathlib.Algebra.BigOperators.Fin

/-!
# Local gradient-factor structure and suffix reduction

The preceding gradient-linear slice reduced the coefficient at sampled
gradient index `r` to

`gdStarWeightQ N r + gdGradientSquareSumQ N r`.

This module exposes the exact support pattern of every generated reverse-LDL
square factor.  The factor at index `k` has gradient coefficient

* `1` at `r = k`;
* `1 / (2 * N - k + 1)` when `r < k`; and
* `0` when `k < r`.

Consequently, the complete square contribution at `r` is the diagonal
contribution at `k = r` minus twice the suffix of the already verified
constant-square contributions with indices `k > r`.

The remaining arbitrary-`N` gradient-linear identity is therefore reduced to
one diagonal rational term and one strict suffix sum.  This module does not yet
close that suffix; the next slice will reuse the constant-tail telescope from
`ParametricUpperConstantTelescoping`.
-/

namespace LeanPEP
namespace Toy
namespace FiniteGD
namespace ParametricUpper

open scoped BigOperators

/-- Coefficient of one sampled gradient in a symbolic prefix. -/
theorem prefixAffine_gradCoeff
    {N : ℕ} :
    ∀ (k : ℕ) (hk : k ≤ N + 1) (r : Fin (N + 1)),
      (GradAffineQ.prefixAffine k hk).gradCoeff r =
        if r.val < k then 1 else 0 := by
  intro k
  induction k with
  | zero =>
      intro hk r
      simp [GradAffineQ.prefixAffine, GradAffineQ.zero]
  | succ k ih =>
      intro hk r
      change
        (GradAffineQ.prefixAffine k
              (Nat.le_trans (Nat.le_succ k) hk)).gradCoeff r +
            unitCoeff ⟨k, Nat.lt_of_succ_le hk⟩ r =
          if r.val < k + 1 then 1 else 0
      rw [ih (Nat.le_trans (Nat.le_succ k) hk) r]
      by_cases hlt : r.val < k
      · have hltSucc : r.val < k + 1 := by omega
        have hne : r ≠ (⟨k, Nat.lt_of_succ_le hk⟩ : Fin (N + 1)) := by
          intro h
          have hval : r.val = k := by
            simpa using
              congrArg (fun z : Fin (N + 1) => z.val) h
          omega
        simp [unitCoeff, hlt, hltSucc, hne]
      · by_cases heq : r.val = k
        · have hr : r = (⟨k, Nat.lt_of_succ_le hk⟩ : Fin (N + 1)) := by
            apply Fin.ext
            exact heq
          rw [hr]
          simp [unitCoeff]
        · have hnotSucc : ¬r.val < k + 1 := by omega
          have hne : r ≠ (⟨k, Nat.lt_of_succ_le hk⟩ : Fin (N + 1)) := by
            intro h
            have hval : r.val = k := by
              simpa using
                congrArg (fun z : Fin (N + 1) => z.val) h
            exact heq hval
          simp [unitCoeff, hlt, hnotSucc, hne]

/-- Centering a gradient prefix changes only its affine constant. -/
theorem gdCenteredPrefixQ_gradCoeff
    (N : ℕ) (k r : Fin (N + 1)) :
    (gdCenteredPrefixQ N k).gradCoeff r =
      if r.val < k.val then 1 else 0 := by
  simp [gdCenteredPrefixQ, GradAffineQ.sub, GradAffineQ.add,
    GradAffineQ.neg, GradAffineQ.const, prefixAffine_gradCoeff]

/-- Centering one sampled gradient changes only its affine constant. -/
theorem gdCenteredGradQ_gradCoeff
    (N : ℕ) (k r : Fin (N + 1)) :
    (gdCenteredGradQ N k).gradCoeff r = unitCoeff k r := by
  simp [gdCenteredGradQ, GradAffineQ.sub, GradAffineQ.add,
    GradAffineQ.neg, GradAffineQ.basis, GradAffineQ.const]

/-- Closed gradient-coefficient formula for one generated square factor. -/
theorem gdSquareFormQ_gradCoeff
    (N : ℕ) (k r : Fin (N + 1)) :
    (gdSquareFormQ N k).gradCoeff r =
      unitCoeff k r +
        ((1 : ℚ) / (((2 * N - k.val + 1 : ℕ) : ℚ))) *
          (if r.val < k.val then 1 else 0) := by
  simp [gdSquareFormQ, GradAffineQ.add, GradAffineQ.scale,
    gdCenteredGradQ_gradCoeff, gdCenteredPrefixQ_gradCoeff]

/-- A generated square factor has coefficient `1` at its own sampled
gradient index. -/
@[simp] theorem gdSquareFormQ_gradCoeff_self
    (N : ℕ) (r : Fin (N + 1)) :
    (gdSquareFormQ N r).gradCoeff r = 1 := by
  rw [gdSquareFormQ_gradCoeff]
  simp [unitCoeff]

/-- Earlier sampled gradients enter a later square factor with the reciprocal
prefix coefficient. -/
theorem gdSquareFormQ_gradCoeff_of_lt
    (N : ℕ) (r k : Fin (N + 1))
    (hrk : r.val < k.val) :
    (gdSquareFormQ N k).gradCoeff r =
      (1 : ℚ) / (((2 * N - k.val + 1 : ℕ) : ℚ)) := by
  have hne : r ≠ k := by
    intro h
    have hval := congrArg Fin.val h
    omega
  rw [gdSquareFormQ_gradCoeff]
  simp [unitCoeff, hrk, hne]

/-- Later sampled gradients do not enter an earlier square factor. -/
theorem gdSquareFormQ_gradCoeff_of_gt
    (N : ℕ) (r k : Fin (N + 1))
    (hkr : k.val < r.val) :
    (gdSquareFormQ N k).gradCoeff r = 0 := by
  have hne : r ≠ k := by
    intro h
    have hval := congrArg Fin.val h
    omega
  have hnot : ¬r.val < k.val := by omega
  rw [gdSquareFormQ_gradCoeff]
  simp [unitCoeff, hnot, hne]

/-- The diagonal linear contribution of the square at index `r`. -/
theorem gdGradientSquareContributionQ_self
    (N : ℕ) (r : Fin (N + 1)) :
    gdGradientSquareContributionQ N r r =
      -2 * gdSquareWeightQ N r *
        ((1 : ℚ) / (((2 * N - r.val + 1 : ℕ) : ℚ))) := by
  unfold gdGradientSquareContributionQ
  rw [gdSquareFormQ_constCoeff, gdSquareFormQ_gradCoeff_self]
  ring

/-- Every strictly later square contributes minus twice its constant-square
contribution to the gradient-linear coefficient at `r`. -/
theorem gdGradientSquareContributionQ_of_lt
    (N : ℕ) (r k : Fin (N + 1))
    (hrk : r.val < k.val) :
    gdGradientSquareContributionQ N r k =
      -2 * gdConstantContributionQ N k := by
  unfold gdGradientSquareContributionQ gdConstantContributionQ
  rw [gdSquareFormQ_constCoeff,
    gdSquareFormQ_gradCoeff_of_lt N r k hrk]
  ring

/-- Every strictly earlier square contributes zero at the later gradient
index `r`. -/
theorem gdGradientSquareContributionQ_of_gt
    (N : ℕ) (r k : Fin (N + 1))
    (hkr : k.val < r.val) :
    gdGradientSquareContributionQ N r k = 0 := by
  unfold gdGradientSquareContributionQ
  rw [gdSquareFormQ_gradCoeff_of_gt N r k hkr]
  ring

/-- Pointwise decomposition into the diagonal term and the strict constant
suffix. -/
theorem gdGradientSquareContributionQ_decompose
    (N : ℕ) (r k : Fin (N + 1)) :
    gdGradientSquareContributionQ N r k =
      (if k = r then gdGradientSquareContributionQ N r r else 0) -
        2 * (if r.val < k.val then gdConstantContributionQ N k else 0) := by
  by_cases hkr : k = r
  · subst k
    simp
  · by_cases hrk : r.val < k.val
    · rw [gdGradientSquareContributionQ_of_lt N r k hrk]
      simp [hkr, hrk]
    · have hvalne : k.val ≠ r.val := by
        intro hval
        apply hkr
        apply Fin.ext
        exact hval
      have hktr : k.val < r.val := by omega
      rw [gdGradientSquareContributionQ_of_gt N r k hktr]
      simp [hkr, hrk]

/-- Strict suffix of the already verified constant-square contributions. -/
def gdGradientConstantSuffixQ
    (N : ℕ) (r : Fin (N + 1)) : ℚ :=
  ∑ k : Fin (N + 1),
    if r.val < k.val then gdConstantContributionQ N k else 0

/-- The list-defined gradient-square sum is the corresponding `Fin` sum. -/
theorem gdGradientSquareSumQ_eq_fin_sum
    (N : ℕ) (r : Fin (N + 1)) :
    gdGradientSquareSumQ N r =
      ∑ k : Fin (N + 1), gdGradientSquareContributionQ N r k := by
  unfold gdGradientSquareSumQ
  symm
  exact Fin.sum_univ_def (gdGradientSquareContributionQ N r)

/-- The complete square contribution is its diagonal part minus twice the
strict suffix of constant-square contributions. -/
theorem gdGradientSquareSumQ_decompose
    (N : ℕ) (r : Fin (N + 1)) :
    gdGradientSquareSumQ N r =
      gdGradientSquareContributionQ N r r -
        2 * gdGradientConstantSuffixQ N r := by
  classical
  rw [gdGradientSquareSumQ_eq_fin_sum]
  calc
    (∑ k : Fin (N + 1), gdGradientSquareContributionQ N r k) =
        ∑ k : Fin (N + 1),
          ((if k = r then gdGradientSquareContributionQ N r r else 0) -
            2 * (if r.val < k.val then gdConstantContributionQ N k else 0)) := by
      apply Finset.sum_congr rfl
      intro k _hk
      exact gdGradientSquareContributionQ_decompose N r k
    _ =
        (∑ k : Fin (N + 1),
          if k = r then gdGradientSquareContributionQ N r r else 0) -
          ∑ k : Fin (N + 1),
            2 * (if r.val < k.val then gdConstantContributionQ N k else 0) := by
      rw [Finset.sum_sub_distrib]
    _ =
        (∑ k : Fin (N + 1),
          if k = r then gdGradientSquareContributionQ N r r else 0) -
          2 * (∑ k : Fin (N + 1),
            if r.val < k.val then gdConstantContributionQ N k else 0) := by
      rw [← Finset.mul_sum]
    _ = gdGradientSquareContributionQ N r r -
          2 * gdGradientConstantSuffixQ N r := by
      have hsingle :
          (∑ k : Fin (N + 1),
            if k = r then gdGradientSquareContributionQ N r r else 0) =
              gdGradientSquareContributionQ N r r := by
        rw [Fintype.sum_eq_single r (by
          intro k hkr
          simp [hkr])]
        simp
      rw [hsingle]
      rfl

/-- The strict constant suffix is empty at the final sampled-gradient index. -/
@[simp] theorem gdGradientConstantSuffixQ_last
    (N : ℕ) :
    gdGradientConstantSuffixQ N (Fin.last N) = 0 := by
  unfold gdGradientConstantSuffixQ
  apply Finset.sum_eq_zero
  intro k _hk
  have hnot : ¬(Fin.last N).val < k.val := by
    simpa only [Fin.val_last] using
      (not_lt_of_ge (Nat.le_of_lt_succ k.isLt))
  rw [if_neg hnot]

/-- The final star weight cancels the final diagonal square contribution. -/
theorem gdGradientFinalCancellationQ
    (N : ℕ) :
    gdStarWeightQ N (Fin.last N) +
        gdGradientSquareContributionQ N (Fin.last N) (Fin.last N) = 0 := by
  have hstar :
      gdStarWeightQ N (Fin.last N) =
        (1 : ℚ) / (((N + 1 : ℕ) : ℚ)) := by
    simp [gdStarWeightQ]
  have hweight :
      gdSquareWeightQ N (Fin.last N) = (1 : ℚ) / 2 := by
    simp [gdSquareWeightQ]
  have hdenNat : 2 * N - N + 1 = N + 1 := by omega
  rw [gdGradientSquareContributionQ_self, hstar, hweight]
  simp only [Fin.val_last, hdenNat]
  ring

/-- The remaining pointwise gradient-linear identity after exposing the strict
constant suffix. -/
def gdGradientSuffixIdentityQ (N : ℕ) : Prop :=
  ∀ r : Fin (N + 1),
    gdStarWeightQ N r +
      (gdGradientSquareContributionQ N r r -
        2 * gdGradientConstantSuffixQ N r) = 0

/-- The B8 finite-sum identity is equivalent to the diagonal-plus-suffix
identity exposed in this module. -/
theorem gdGradientCoefficientIdentityQ_iff_suffix
    (N : ℕ) :
    gdGradientCoefficientIdentityQ N ↔
      gdGradientSuffixIdentityQ N := by
  unfold gdGradientCoefficientIdentityQ gdGradientSuffixIdentityQ
  constructor
  · intro h r
    simpa [gdGradientSquareSumQ_decompose] using h r
  · intro h r
    simpa [gdGradientSquareSumQ_decompose] using h r

/-- The suffix identity is already closed at the final index. -/
theorem gdGradientSuffixIdentityQ_last
    (N : ℕ) :
    gdStarWeightQ N (Fin.last N) +
      (gdGradientSquareContributionQ N (Fin.last N) (Fin.last N) -
        2 * gdGradientConstantSuffixQ N (Fin.last N)) = 0 := by
  rw [gdGradientConstantSuffixQ_last]
  simpa using gdGradientFinalCancellationQ N

/-- Existing checker-verified regressions remain compatible with the suffix
reduction. -/
theorem gdGradientSuffixIdentityQ_0 :
    gdGradientSuffixIdentityQ 0 :=
  (gdGradientCoefficientIdentityQ_iff_suffix 0).1
    gdGradientCoefficientIdentityQ_0

theorem gdGradientSuffixIdentityQ_4 :
    gdGradientSuffixIdentityQ 4 :=
  (gdGradientCoefficientIdentityQ_iff_suffix 4).1
    gdGradientCoefficientIdentityQ_4

theorem gdGradientSuffixIdentityQ_8 :
    gdGradientSuffixIdentityQ 8 :=
  (gdGradientCoefficientIdentityQ_iff_suffix 8).1
    gdGradientCoefficientIdentityQ_8

end ParametricUpper
end FiniteGD
end Toy
end LeanPEP
