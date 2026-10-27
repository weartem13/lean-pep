import LeanPEP.Toy.FiniteGD.ParametricUpperGradientStructure

/-!
# Arbitrary-`N` gradient-linear cancellation

The preceding slice reduced the generated certificate's gradient-linear
coefficient at sampled index `r` to

`gdStarWeightQ N r + gdGradientSquareContributionQ N r r
  - 2 * gdGradientConstantSuffixQ N r`.

This module closes that channel for every trajectory length.  For each
nonfinal index, the strict suffix of constant-square contributions is the
constant tail potential at `r + 1`.  The remaining local rational expression
then vanishes exactly.  The final index was already closed in
`ParametricUpperGradientStructure`.

No certificate data, interpolation multiplier, square weight, square factor,
or checker is changed here.
-/

namespace LeanPEP
namespace Toy
namespace FiniteGD
namespace ParametricUpper

open scoped BigOperators

/-- A finite sum of adjacent differences, restricted to the strict suffix
`r < k`, telescopes to the first retained value minus the final value. -/
private theorem sum_range_strict_tail_sub
    (f : ℕ → ℚ) :
    ∀ (m r : ℕ), r < m →
      (∑ k ∈ Finset.range m,
        if r < k then f k - f (k + 1) else 0) =
        f (r + 1) - f m := by
  intro m
  induction m with
  | zero =>
      intro r hr
      omega
  | succ m ih =>
      intro r hr
      rw [Finset.sum_range_succ]
      by_cases hlt : r < m
      · rw [if_pos hlt, ih r hlt]
        ring
      · have hre : r = m := by omega
        subst r
        have hzero :
            (∑ k ∈ Finset.range m,
              if m < k then f k - f (k + 1) else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro k hk
          have hklt : k < m := Finset.mem_range.mp hk
          rw [if_neg (not_lt_of_ge (Nat.le_of_lt hklt))]
        rw [hzero, if_neg (by omega)]
        ring

/-- For every nonfinal sampled-gradient index, the strict suffix of generated
constant-square contributions is exactly the next constant tail potential. -/
theorem gdGradientConstantSuffixQ_eq_tail_of_lt
    (N : ℕ) (r : Fin (N + 1))
    (hr : r.val < N) :
    gdGradientConstantSuffixQ N r =
      gdConstantTailQ N (r.val + 1) := by
  unfold gdGradientConstantSuffixQ
  rw [Fin.sum_univ_castSucc]
  calc
    (∑ k : Fin N,
          if r.val < k.castSucc.val then
            gdConstantContributionQ N k.castSucc
          else 0) +
        (if r.val < (Fin.last N).val then
          gdConstantContributionQ N (Fin.last N)
        else 0) =
      (∑ k : Fin N,
          if r.val < k.val then
            gdConstantTailQ N k.val -
              gdConstantTailQ N (k.val + 1)
          else 0) +
        gdConstantTailQ N N := by
      have hsum :
          (∑ k : Fin N,
              if r.val < k.castSucc.val then
                gdConstantContributionQ N k.castSucc
              else 0) =
            ∑ k : Fin N,
              if r.val < k.val then
                gdConstantTailQ N k.val -
                  gdConstantTailQ N (k.val + 1)
              else 0 := by
        apply Finset.sum_congr rfl
        intro k _hk
        simp only [Fin.val_castSucc]
        by_cases h : r.val < k.val
        · rw [if_pos h, if_pos h,
            gdConstantContributionQ_castSucc]
        · rw [if_neg h, if_neg h]
      have hlast :
          (if r.val < (Fin.last N).val then
              gdConstantContributionQ N (Fin.last N)
            else 0) =
            gdConstantTailQ N N := by
        rw [if_pos]
        · exact gdConstantContributionQ_last N
        · simpa only [Fin.val_last] using hr
      rw [hsum, hlast]
    _ =
      (∑ k ∈ Finset.range N,
          if r.val < k then
            gdConstantTailQ N k -
              gdConstantTailQ N (k + 1)
          else 0) +
        gdConstantTailQ N N := by
      rw [Finset.sum_range]
    _ =
      (gdConstantTailQ N (r.val + 1) -
          gdConstantTailQ N N) +
        gdConstantTailQ N N := by
      rw [sum_range_strict_tail_sub
        (gdConstantTailQ N) N r.val hr]
    _ = gdConstantTailQ N (r.val + 1) := by
      ring

/-- The nonfinal star weight, diagonal square contribution, and strict suffix
cancel by one exact rational identity. -/
theorem gdGradientSuffixIdentityQ_of_lt
    (N : ℕ) (r : Fin (N + 1))
    (hr : r.val < N) :
    gdStarWeightQ N r +
      (gdGradientSquareContributionQ N r r -
        2 * gdGradientConstantSuffixQ N r) = 0 := by
  rw [gdGradientConstantSuffixQ_eq_tail_of_lt N r hr,
    gdGradientSquareContributionQ_self]
  have hne : r.val ≠ N := Nat.ne_of_lt hr
  have hr2N : r.val ≤ 2 * N := by omega
  have hden0 : 2 * (N : ℚ) - (r.val : ℚ) ≠ 0 := by
    have hpos : 0 < 2 * N - r.val := by omega
    have hcast :
        (((2 * N - r.val : ℕ) : ℚ)) =
          2 * (N : ℚ) - (r.val : ℚ) := by
      rw [Nat.cast_sub hr2N]
      push_cast
      rfl
    rw [← hcast]
    positivity
  have hden1 : 2 * (N : ℚ) - (r.val : ℚ) + 1 ≠ 0 := by
    have hcast :
        (((2 * N - r.val + 1 : ℕ) : ℚ)) =
          2 * (N : ℚ) - (r.val : ℚ) + 1 := by
      rw [Nat.cast_add, Nat.cast_sub hr2N]
      push_cast
      rfl
    rw [← hcast]
    positivity
  have hdenTail :
      2 * (N : ℚ) - ((r.val : ℚ) + 1) + 1 ≠ 0 := by
    rw [show
      2 * (N : ℚ) - ((r.val : ℚ) + 1) + 1 =
        2 * (N : ℚ) - (r.val : ℚ) by ring]
    exact hden0
  unfold gdStarWeightQ gdSquareWeightQ gdConstantTailQ
  simp only [if_neg hne]
  push_cast [Nat.cast_sub hr2N]
  field_simp [hden0, hden1, hdenTail]
  ring

/-- The diagonal-plus-suffix gradient-linear identity holds at every sampled
index and every trajectory length. -/
theorem gdGradientSuffixIdentityQ_all
    (N : ℕ) :
    gdGradientSuffixIdentityQ N := by
  intro r
  by_cases hr : r.val < N
  · exact gdGradientSuffixIdentityQ_of_lt N r hr
  · have hrLast : r = Fin.last N := by
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    rw [hrLast]
    exact gdGradientSuffixIdentityQ_last N

/-- The reduced gradient-linear finite-sum identity holds for every trajectory
length. -/
theorem gdGradientCoefficientIdentityQ_all
    (N : ℕ) :
    gdGradientCoefficientIdentityQ N :=
  (gdGradientCoefficientIdentityQ_iff_suffix N).2
    (gdGradientSuffixIdentityQ_all N)

/-- Every sampled-gradient-linear coefficient of the generated certificate
matches the target polynomial. -/
theorem gdCertificate_gradCoeff
    (N : ℕ) (r : Fin (N + 1)) :
    (certificateRhsPolyQ (gdUpperCertQ N)).gradCoeff r =
      (upperTargetPolyQ
        (gdBoundQ N)
        (gdObjective N)).gradCoeff r :=
  ((gdCertificate_gradCoefficients_eq_target_iff N).2
    (gdGradientCoefficientIdentityQ_all N)) r

/-- Pointwise gradient-linear coefficient equality, packaged as one family. -/
theorem gdCertificate_gradCoefficients
    (N : ℕ) :
    ∀ r : Fin (N + 1),
      (certificateRhsPolyQ (gdUpperCertQ N)).gradCoeff r =
        (upperTargetPolyQ
          (gdBoundQ N)
          (gdObjective N)).gradCoeff r :=
  (gdCertificate_gradCoefficients_eq_target_iff N).2
    (gdGradientCoefficientIdentityQ_all N)

end ParametricUpper
end FiniteGD
end Toy
end LeanPEP
