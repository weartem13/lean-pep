import LeanPEP.Toy.FiniteGD.ParametricUpperQuadraticOffDiagonal

/-!
# Arbitrary-`N` diagonal quadratic cancellation and universal certificate identity

The preceding slice closes every ordered off-diagonal sampled-gradient
quadratic coefficient of the generated finite-GD certificate.  This module
closes the remaining diagonal entries.

For a sampled-gradient index `r`, the interpolation contribution is

* `-gdChainWeightQ N r` when `r < N`; and
* `-1/2` at the final index.

The reverse-LDL square contribution is

* `gdChainWeightQ N r` when `r < N`; and
* `1/2` at the final index.

The two channels therefore cancel pointwise.  Together with the already
verified off-diagonal family, this proves every ordered quadratic coefficient.
The module then assembles the previously verified constant, gradient-linear,
function-value, and quadratic coefficient families into the full polynomial
identity, proves arbitrary-`N` checker acceptance, and derives the normalized
finite-GD upper theorem.

No certificate data, interpolation multiplier, square weight, square factor,
checker, or finite-GD semantics is changed here.
-/

namespace LeanPEP
namespace Toy
namespace FiniteGD
namespace ParametricUpper

open scoped BigOperators

/-- A star-to-iterate interpolation slack contributes `-1/2` on the diagonal
of its own sampled-gradient index and zero on every other diagonal entry. -/
theorem slackPolyQ_star_iter_quadCoeff_self
    (N : ℕ) (k r : Fin (N + 1)) :
    (slackPolyQ (Point.star : Point N) (Point.iter k)).quadCoeff r r =
      -((1 : ℚ) / 2) * unitCoeff k r := by
  have hx :
      (GradAffineQ.sub
        (xAffineQ (Point.star : Point N))
        (xAffineQ (Point.iter k))).gradCoeff =
          fun t => if t.val < k.val then 1 else 0 := by
    funext t
    exact xAffineQ_star_sub_iter_gradCoeff N k t
  have hg :
      (GradAffineQ.sub
        (gradAffineQ (Point.star : Point N))
        (gradAffineQ (Point.iter k))).gradCoeff =
          fun t => -unitCoeff k t := by
    funext t
    exact gradAffineQ_star_sub_iter_gradCoeff N k t
  rw [slackPolyQ_quadCoeff, hx, hg]
  simp only [gradAffineQ, GradAffineQ.basis]
  unfold symOuterQ
  by_cases hrk : r = k
  · subst r
    simp [unitCoeff] <;> ring
  · simp [unitCoeff, hrk]

/-- A consecutive-iterate interpolation slack contributes `-1/2` at each of
its two incident sampled-gradient diagonal entries and zero elsewhere. -/
theorem slackPolyQ_consecutive_quadCoeff_self
    (N : ℕ) (k : Fin N) (r : Fin (N + 1)) :
    (slackPolyQ
      (Point.iter (⟨k.val, by omega⟩ : Fin (N + 1)))
      (Point.iter (⟨k.val + 1, by omega⟩ : Fin (N + 1)))).quadCoeff r r =
        -((1 : ℚ) / 2) *
          (unitCoeff (⟨k.val, by omega⟩ : Fin (N + 1)) r +
            unitCoeff (⟨k.val + 1, by omega⟩ : Fin (N + 1)) r) := by
  let a : Fin (N + 1) := ⟨k.val, by omega⟩
  let b : Fin (N + 1) := ⟨k.val + 1, by omega⟩
  change
    (slackPolyQ (Point.iter a) (Point.iter b)).quadCoeff r r =
      -((1 : ℚ) / 2) * (unitCoeff a r + unitCoeff b r)
  have hab : a ≠ b := by
    intro h
    have hval : a.val = b.val := by
      simpa using congrArg (fun z : Fin (N + 1) => z.val) h
    dsimp [a, b] at hval
    omega
  have hx :
      (GradAffineQ.sub
        (xAffineQ (Point.iter a))
        (xAffineQ (Point.iter b))).gradCoeff = unitCoeff a := by
    funext t
    simpa [a, b] using xAffineQ_consecutive_sub_gradCoeff N k t
  have hg :
      (GradAffineQ.sub
        (gradAffineQ (Point.iter a))
        (gradAffineQ (Point.iter b))).gradCoeff =
          fun t => unitCoeff a t - unitCoeff b t := by
    funext t
    simpa [a, b] using gradAffineQ_consecutive_sub_gradCoeff N k t
  rw [slackPolyQ_quadCoeff, hx, hg]
  simp only [gradAffineQ, GradAffineQ.basis]
  unfold symOuterQ
  by_cases hra : r = a
  · subst r
    simp [unitCoeff, hab, Ne.symm hab] <;> ring
  · by_cases hrb : r = b
    · subst r
      simp [unitCoeff, hra, hab, Ne.symm hab] <;> ring
    · simp [unitCoeff, hra, hrb] <;> ring

/-- The complete star interpolation list contributes `-gdStarWeightQ N r / 2`
at diagonal entry `(r,r)`. -/
theorem gdStarTermsQ_quadCoeff_self
    (N : ℕ) (r : Fin (N + 1)) :
    (interpPolySumQ (gdStarTermsQ N)).quadCoeff r r =
      -((1 : ℚ) / 2) * gdStarWeightQ N r := by
  classical
  rw [interpPolySumQ_quadCoeff]
  simp only [gdStarTermsQ, List.map_map, Function.comp_apply]
  rw [← Fin.sum_univ_def]
  rw [Fintype.sum_eq_single r (by
    intro k hkr
    simp only [Function.comp_apply]
    rw [slackPolyQ_star_iter_quadCoeff_self N k r]
    simp only [unitCoeff, if_neg (Ne.symm hkr), mul_zero])]
  simp only [Function.comp_apply]
  rw [slackPolyQ_star_iter_quadCoeff_self N r r]
  have hunit : unitCoeff r r = (1 : ℚ) := by
    simp [unitCoeff]
  rw [hunit]
  ring

/-- The complete consecutive-iterate interpolation list contributes minus one
half of the total incident chain flow at diagonal entry `(r,r)`. -/
theorem gdChainTermsQ_quadCoeff_self
    (N : ℕ) (r : Fin (N + 1)) :
    (interpPolySumQ (gdChainTermsQ N)).quadCoeff r r =
      -((1 : ℚ) / 2) *
        (gdChainSourceSumQ N r + gdChainTargetSumQ N r) := by
  rw [interpPolySumQ_quadCoeff]
  simp only [gdChainTermsQ, List.map_map, Function.comp_apply]
  rw [← Fin.sum_univ_def]
  unfold gdChainSourceSumQ gdChainTargetSumQ
  calc
    (∑ k : Fin N,
        gdChainWeightQ N k *
          (slackPolyQ
            (Point.iter (⟨k.val, by omega⟩ : Fin (N + 1)))
            (Point.iter (⟨k.val + 1, by omega⟩ : Fin (N + 1)))).quadCoeff r r) =
      ∑ k : Fin N,
        gdChainWeightQ N k *
          (-((1 : ℚ) / 2) *
            (unitCoeff (⟨k.val, by omega⟩ : Fin (N + 1)) r +
              unitCoeff (⟨k.val + 1, by omega⟩ : Fin (N + 1)) r)) := by
        apply Finset.sum_congr rfl
        intro k _hk
        simpa using
          congrArg (fun q : ℚ => gdChainWeightQ N k * q)
            (slackPolyQ_consecutive_quadCoeff_self N k r)
    _ =
      (∑ k : Fin N,
        -((1 : ℚ) / 2) *
          (gdChainWeightQ N k *
            unitCoeff (⟨k.val, by omega⟩ : Fin (N + 1)) r)) +
      (∑ k : Fin N,
        -((1 : ℚ) / 2) *
          (gdChainWeightQ N k *
            unitCoeff (⟨k.val + 1, by omega⟩ : Fin (N + 1)) r)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _hk
        ring
    _ = -((1 : ℚ) / 2) *
          ((∑ k : Fin N,
              gdChainWeightQ N k *
                unitCoeff (⟨k.val, by omega⟩ : Fin (N + 1)) r) +
            (∑ k : Fin N,
              gdChainWeightQ N k *
                unitCoeff (⟨k.val + 1, by omega⟩ : Fin (N + 1)) r)) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        ring

/-- Structural formula for the generated interpolation contribution at one
diagonal ordered quadratic entry. -/
theorem gdQuadraticInterpSumQ_self_flow
    (N : ℕ) (r : Fin (N + 1)) :
    gdQuadraticInterpSumQ N r r =
      -((1 : ℚ) / 2) *
        (gdStarWeightQ N r +
          gdChainSourceSumQ N r + gdChainTargetSumQ N r) := by
  calc
    gdQuadraticInterpSumQ N r r =
        (interpPolySumQ (gdInterpTermsQ N)).quadCoeff r r :=
      (gdInterpTermsQ_quadCoeff N r r).symm
    _ = (interpPolySumQ (gdStarTermsQ N)).quadCoeff r r +
          (interpPolySumQ (gdChainTermsQ N)).quadCoeff r r := by
      unfold gdInterpTermsQ
      exact interpPolySumQ_append_quadCoeff
        (gdStarTermsQ N) (gdChainTermsQ N) r r
    _ = -((1 : ℚ) / 2) *
          (gdStarWeightQ N r +
            gdChainSourceSumQ N r + gdChainTargetSumQ N r) := by
      rw [gdStarTermsQ_quadCoeff_self, gdChainTermsQ_quadCoeff_self]
      ring

/-- At every nonfinal diagonal entry, the interpolation contribution is the
negative outgoing chain-flow weight. -/
theorem gdQuadraticInterpSumQ_self_of_lt
    (N : ℕ) (r : Fin (N + 1)) (hr : r.val < N) :
    gdQuadraticInterpSumQ N r r =
      -gdChainWeightQ N ⟨r.val, hr⟩ := by
  have hobj : r ≠ gdObjective N := by
    intro h
    have hval : r.val = N := by
      simpa [gdObjective] using
        congrArg (fun z : Fin (N + 1) => z.val) h
    omega
  have hflow :
      -gdStarWeightQ N r +
          gdChainSourceSumQ N r - gdChainTargetSumQ N r = 0 := by
    calc
      -gdStarWeightQ N r +
            gdChainSourceSumQ N r - gdChainTargetSumQ N r =
          (certificateRhsPolyQ (gdUpperCertQ N)).valueCoeff r :=
        (gdCertificateRhs_valueCoeff_flow N r).symm
      _ = (upperTargetPolyQ
            (gdBoundQ N) (gdObjective N)).valueCoeff r :=
        gdCertificate_valueCoeff N r
      _ = 0 := by
        rw [upperTargetPolyQ_valueCoeff]
        simp only [unitCoeff, if_neg hobj, neg_zero]
  have hsum :
      gdStarWeightQ N r +
          gdChainSourceSumQ N r + gdChainTargetSumQ N r =
        2 * gdChainSourceSumQ N r := by
    linarith
  rw [gdQuadraticInterpSumQ_self_flow, hsum,
    gdChainSourceSumQ_eq N r hr]
  ring

/-- At the final sampled-gradient index, the interpolation diagonal
contribution is `-1/2`. -/
theorem gdQuadraticInterpSumQ_self_last
    (N : ℕ) :
    gdQuadraticInterpSumQ N (Fin.last N) (Fin.last N) =
      -((1 : ℚ) / 2) := by
  have hlastObj : Fin.last N = gdObjective N := by
    apply Fin.ext
    rfl
  have hlastCtor :
      Fin.last N = (⟨N, by omega⟩ : Fin (N + 1)) := by
    apply Fin.ext
    rfl
  have hsource : gdChainSourceSumQ N (Fin.last N) = 0 := by
    rw [hlastCtor]
    exact gdChainSourceSumQ_last N
  have hflow :
      -gdStarWeightQ N (Fin.last N) +
          gdChainSourceSumQ N (Fin.last N) -
            gdChainTargetSumQ N (Fin.last N) = -1 := by
    calc
      -gdStarWeightQ N (Fin.last N) +
            gdChainSourceSumQ N (Fin.last N) -
              gdChainTargetSumQ N (Fin.last N) =
          (certificateRhsPolyQ (gdUpperCertQ N)).valueCoeff (Fin.last N) :=
        (gdCertificateRhs_valueCoeff_flow N (Fin.last N)).symm
      _ = (upperTargetPolyQ
            (gdBoundQ N) (gdObjective N)).valueCoeff (Fin.last N) :=
        gdCertificate_valueCoeff N (Fin.last N)
      _ = -1 := by
        rw [upperTargetPolyQ_valueCoeff]
        simp only [unitCoeff, if_pos hlastObj]
  have hsum :
      gdStarWeightQ N (Fin.last N) +
          gdChainSourceSumQ N (Fin.last N) +
            gdChainTargetSumQ N (Fin.last N) = 1 := by
    rw [hsource]
    linarith
  rw [gdQuadraticInterpSumQ_self_flow, hsum]
  ring

/-- One generated square's diagonal quadratic contribution splits into its own
weight and, for strictly later factors, the already verified constant-square
contribution. -/
theorem gdQuadraticSquareContributionQ_self_decompose
    (N : ℕ) (r k : Fin (N + 1)) :
    gdQuadraticSquareContributionQ N r r k =
      (if k = r then gdSquareWeightQ N r else 0) +
        (if r.val < k.val then gdConstantContributionQ N k else 0) := by
  by_cases hkr : k = r
  · subst k
    unfold gdQuadraticSquareContributionQ
    rw [gdSquareFormQ_gradCoeff_self]
    simp
  · by_cases hrk : r.val < k.val
    · unfold gdQuadraticSquareContributionQ
      rw [gdSquareFormQ_gradCoeff_of_lt N r k hrk,
        gdConstantContributionQ_closed]
      simp only [if_neg hkr, if_pos hrk, zero_add]
      ring
    · have hvalne : k.val ≠ r.val := by
        intro hval
        apply hkr
        apply Fin.ext
        exact hval
      have hktr : k.val < r.val := by omega
      unfold gdQuadraticSquareContributionQ
      rw [gdSquareFormQ_gradCoeff_of_gt N r k hktr]
      simp [hkr, hrk]

/-- The complete generated square diagonal is its local square weight plus the
strict suffix of constant-square contributions. -/
theorem gdQuadraticSquareSumQ_self_decompose
    (N : ℕ) (r : Fin (N + 1)) :
    gdQuadraticSquareSumQ N r r =
      gdSquareWeightQ N r + gdGradientConstantSuffixQ N r := by
  classical
  rw [gdQuadraticSquareSumQ_eq_fin_sum]
  calc
    (∑ k : Fin (N + 1),
        gdQuadraticSquareContributionQ N r r k) =
      ∑ k : Fin (N + 1),
        ((if k = r then gdSquareWeightQ N r else 0) +
          (if r.val < k.val then gdConstantContributionQ N k else 0)) := by
        apply Finset.sum_congr rfl
        intro k _hk
        exact gdQuadraticSquareContributionQ_self_decompose N r k
    _ = (∑ k : Fin (N + 1),
            if k = r then gdSquareWeightQ N r else 0) +
          (∑ k : Fin (N + 1),
            if r.val < k.val then gdConstantContributionQ N k else 0) := by
        rw [Finset.sum_add_distrib]
    _ = gdSquareWeightQ N r + gdGradientConstantSuffixQ N r := by
        have hsingle :
            (∑ k : Fin (N + 1),
              if k = r then gdSquareWeightQ N r else 0) =
                gdSquareWeightQ N r := by
          rw [Fintype.sum_eq_single r (by
            intro k hkr
            simp [hkr])]
          simp
        rw [hsingle]
        rfl

/-- At a nonfinal sampled-gradient index, the local square weight plus the next
constant tail is exactly the outgoing chain-flow weight. -/
theorem gdSquareWeightQ_add_nextTail_eq_chainWeightQ
    (N : ℕ) (r : Fin (N + 1)) (hr : r.val < N) :
    gdSquareWeightQ N r + gdConstantTailQ N (r.val + 1) =
      gdChainWeightQ N ⟨r.val, hr⟩ := by
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
  have hdenTail :
      2 * (N : ℚ) - ((r.val : ℚ) + 1) + 1 ≠ 0 := by
    rw [show
      2 * (N : ℚ) - ((r.val : ℚ) + 1) + 1 =
        2 * (N : ℚ) - (r.val : ℚ) by ring]
    exact hden0
  unfold gdSquareWeightQ gdConstantTailQ gdChainWeightQ
  simp only [if_neg hne]
  push_cast [Nat.cast_sub hr2N]
  field_simp [hden0, hdenTail]
  ring

/-- At every nonfinal diagonal entry, the complete square contribution is the
outgoing chain-flow weight. -/
theorem gdQuadraticSquareSumQ_self_of_lt
    (N : ℕ) (r : Fin (N + 1)) (hr : r.val < N) :
    gdQuadraticSquareSumQ N r r =
      gdChainWeightQ N ⟨r.val, hr⟩ := by
  rw [gdQuadraticSquareSumQ_self_decompose,
    gdGradientConstantSuffixQ_eq_tail_of_lt N r hr,
    gdSquareWeightQ_add_nextTail_eq_chainWeightQ N r hr]

/-- At the final sampled-gradient index, the complete square diagonal
contribution is `1/2`. -/
theorem gdQuadraticSquareSumQ_self_last
    (N : ℕ) :
    gdQuadraticSquareSumQ N (Fin.last N) (Fin.last N) =
      (1 : ℚ) / 2 := by
  rw [gdQuadraticSquareSumQ_self_decompose,
    gdGradientConstantSuffixQ_last]
  simp [gdSquareWeightQ]

/-- Every nonfinal generated diagonal quadratic coefficient vanishes. -/
theorem gdQuadraticCoefficientIdentityQ_self_of_lt
    (N : ℕ) (r : Fin (N + 1)) (hr : r.val < N) :
    gdQuadraticInterpSumQ N r r +
      gdQuadraticSquareSumQ N r r = 0 := by
  rw [gdQuadraticInterpSumQ_self_of_lt N r hr,
    gdQuadraticSquareSumQ_self_of_lt N r hr]
  ring

/-- The final generated diagonal quadratic coefficient vanishes. -/
theorem gdQuadraticCoefficientIdentityQ_self_last
    (N : ℕ) :
    gdQuadraticInterpSumQ N (Fin.last N) (Fin.last N) +
      gdQuadraticSquareSumQ N (Fin.last N) (Fin.last N) = 0 := by
  rw [gdQuadraticInterpSumQ_self_last,
    gdQuadraticSquareSumQ_self_last]
  ring

/-- Every generated diagonal quadratic coefficient vanishes. -/
theorem gdQuadraticCoefficientIdentityQ_diagonal
    (N : ℕ) (r : Fin (N + 1)) :
    gdQuadraticInterpSumQ N r r +
      gdQuadraticSquareSumQ N r r = 0 := by
  by_cases hr : r.val < N
  · exact gdQuadraticCoefficientIdentityQ_self_of_lt N r hr
  · have hrLast : r = Fin.last N := by
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    rw [hrLast]
    exact gdQuadraticCoefficientIdentityQ_self_last N

/-- The complete ordered quadratic coefficient family vanishes for every
trajectory length. -/
theorem gdQuadraticCoefficientIdentityQ_all
    (N : ℕ) :
    gdQuadraticCoefficientIdentityQ N := by
  intro r s
  by_cases hrs : r = s
  · subst s
    exact gdQuadraticCoefficientIdentityQ_diagonal N r
  · exact gdQuadraticCoefficientIdentityQ_offDiagonal N r s hrs

/-- Every diagonal ordered quadratic coefficient of the generated certificate
matches the target polynomial. -/
theorem gdCertificate_quadCoeff_self
    (N : ℕ) (r : Fin (N + 1)) :
    (certificateRhsPolyQ (gdUpperCertQ N)).quadCoeff r r =
      (upperTargetPolyQ
        (gdBoundQ N)
        (gdObjective N)).quadCoeff r r := by
  rw [gdCertificateRhs_quadCoeff_eq_quadraticSumsQ,
    upperTargetPolyQ_quadCoeff]
  exact gdQuadraticCoefficientIdentityQ_diagonal N r

/-- Every ordered quadratic coefficient of the generated certificate matches
the target polynomial. -/
theorem gdCertificate_quadCoeff
    (N : ℕ) (r s : Fin (N + 1)) :
    (certificateRhsPolyQ (gdUpperCertQ N)).quadCoeff r s =
      (upperTargetPolyQ
        (gdBoundQ N)
        (gdObjective N)).quadCoeff r s := by
  by_cases hrs : r = s
  · subst s
    exact gdCertificate_quadCoeff_self N r
  · exact gdCertificate_quadCoeff_of_ne N r s hrs

/-- Pointwise ordered quadratic coefficient equality, packaged as one family. -/
theorem gdCertificate_quadCoefficients
    (N : ℕ) :
    ∀ r s : Fin (N + 1),
      (certificateRhsPolyQ (gdUpperCertQ N)).quadCoeff r s =
        (upperTargetPolyQ
          (gdBoundQ N)
          (gdObjective N)).quadCoeff r s :=
  gdCertificate_quadCoeff N

/-- The complete generated polynomial identity holds for every trajectory
length. -/
theorem gdCertificateIdentityQ_all
    (N : ℕ) :
    gdCertificateIdentityQ N := by
  unfold gdCertificateIdentityQ
  apply QuadPolyQ.ext
  · exact gdCertificate_constCoeff N
  · funext r
    exact gdCertificate_gradCoeff N r
  · funext r
    exact gdCertificate_valueCoeff N r
  · funext r s
    exact gdCertificate_quadCoeff N r s

/-- The generic exact checker accepts the closed-form generated certificate for
every trajectory length. -/
theorem gdUpperCertQ_check_all
    (N : ℕ) :
    checkUpperCertQ (gdUpperCertQ N) = true :=
  gdUpperCertQ_check_of_identity N (gdCertificateIdentityQ_all N)

/-- Universal normalized finite-GD upper theorem for the generated
closed-form certificate. -/
theorem gd_upper_all
    (N : ℕ) (d : DataR N) (hfeasible : Feasible d) :
    d.value (gdObjective N) ≤ (gdBoundQ N : ℝ) :=
  gd_upper_of_check N (gdUpperCertQ_check_all N) d hfeasible

end ParametricUpper
end FiniteGD
end Toy
end LeanPEP
