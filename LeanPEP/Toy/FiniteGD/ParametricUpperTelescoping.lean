import LeanPEP.Toy.FiniteGD.ParametricUpperProof

/-!
# Exact interpolation-flow telescoping identities

This module proves the closed-form rational recurrences behind the
function-value part of the arbitrary-length gradient-descent certificate.

For positive `N`, write

`c_k = (k + 1) / (2N - k)` for `k < N`.

The generated star weights are exactly the increments of this flow:

* the first star weight is `c_0`;
* every interior star weight is `c_k - c_{k-1}`; and
* the final star weight is `1 - c_{N-1}`.

These identities are the algebraic input needed to telescope all intermediate
function-value coefficients in the universal certificate identity.  This slice
does not yet prove the full coefficient equality.
-/

namespace LeanPEP
namespace Toy
namespace FiniteGD
namespace ParametricUpper

/-- The target bound is one half of the centered witness gradient. -/
theorem gdBoundQ_eq_half_centerQ (N : ℕ) :
    gdBoundQ N = ((1 : ℚ) / 2) * gdCenterQ N := by
  have hcenter : (((2 * N + 1 : ℕ) : ℚ)) ≠ 0 := by positivity
  have hbound : (((4 * N + 2 : ℕ) : ℚ)) ≠ 0 := by positivity
  unfold gdBoundQ gdCenterQ
  field_simp [hcenter, hbound]
  push_cast
  ring

/-- In the zero-step case the unique star weight is `1`. -/
@[simp] theorem gdStarWeightQ_zero_zero :
    gdStarWeightQ 0 ⟨0, by omega⟩ = 1 := by
  norm_num [gdStarWeightQ]

/-- For a positive trajectory length, the first star weight equals the first
consecutive-pair flow weight. -/
theorem gdStarWeightQ_zero_eq_chainWeightQ_zero
    (N : ℕ) (hN : 0 < N) :
    gdStarWeightQ N ⟨0, by omega⟩ =
      gdChainWeightQ N ⟨0, hN⟩ := by
  have hzero : (0 : ℕ) ≠ N := by omega
  have htwoN : (((2 * N : ℕ) : ℚ)) ≠ 0 := by positivity
  have htwoNOne : (((2 * N + 1 : ℕ) : ℚ)) ≠ 0 := by positivity
  unfold gdStarWeightQ gdChainWeightQ
  simp only [Fin.val_mk]
  rw [if_neg hzero]
  simp only [Nat.sub_zero]
  field_simp [htwoN, htwoNOne]
  push_cast
  ring

/-- Every interior star weight is the increment of the consecutive-pair flow. -/
theorem gdStarWeightQ_succ_eq_chainWeightQ_sub
    (N k : ℕ) (hk : k + 1 < N) :
    gdStarWeightQ N ⟨k + 1, by omega⟩ =
      gdChainWeightQ N ⟨k + 1, by omega⟩ -
        gdChainWeightQ N ⟨k, by omega⟩ := by
  have hne : k + 1 ≠ N := by omega
  have htpos : 0 < 2 * N - (k + 1) := by omega
  have hden :
      2 * N - k = (2 * N - (k + 1)) + 1 := by
    omega
  have hnum :
      2 * N + 1 = (2 * N - (k + 1)) + (k + 2) := by
    omega
  unfold gdStarWeightQ gdChainWeightQ
  simp only [Fin.val_mk]
  rw [if_neg hne, hden, hnum]
  have ht : (0 : ℚ) < ((2 * N - (k + 1) : ℕ) : ℚ) := by
    exact_mod_cast htpos
  have ht0 : (((2 * N - (k + 1) : ℕ) : ℚ)) ≠ 0 := ne_of_gt ht
  have ht1 : ((((2 * N - (k + 1)) + 1 : ℕ) : ℚ)) ≠ 0 := by
    positivity
  field_simp [ht0, ht1]
  push_cast
  ring

/-- The final star weight closes the interpolation flow at total mass `1`. -/
theorem gdStarWeightQ_last_eq_one_sub_chainWeightQ_last
    (N : ℕ) (hN : 0 < N) :
    gdStarWeightQ N ⟨N, by omega⟩ =
      1 - gdChainWeightQ N ⟨N - 1, by omega⟩ := by
  have hden : 2 * N - (N - 1) = N + 1 := by omega
  have hnum : (N - 1) + 1 = N := by omega
  unfold gdStarWeightQ gdChainWeightQ
  simp only [if_true]
  rw [hden, hnum]
  have hNOne : (((N + 1 : ℕ) : ℚ)) ≠ 0 := by positivity
  field_simp [hNOne]
  push_cast
  ring

end ParametricUpper
end FiniteGD
end Toy
end LeanPEP
