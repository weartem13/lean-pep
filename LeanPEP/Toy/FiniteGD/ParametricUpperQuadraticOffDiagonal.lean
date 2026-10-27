import LeanPEP.Toy.FiniteGD.ParametricUpperQuadraticCoefficients

/-!
# Arbitrary-`N` off-diagonal quadratic cancellation

The preceding slice reduced the final ordered sampled-gradient-quadratic
coefficient family to the sum of one interpolation contribution and one
reverse-LDL square contribution.

This module closes every strictly off-diagonal entry.  For `r < s`, the
interpolation contribution is `-gdStarWeightQ N s / 2`.  The square
contribution is `-1/2` times the already verified gradient-linear square sum
at index `s`.  The arbitrary-`N` gradient-linear cancellation theorem then
forces the two terms to cancel.  Symmetry closes the opposite ordered entry.

No certificate data, interpolation multiplier, square weight, square factor,
or checker is changed here.  Diagonal quadratic entries remain for the next
slice.
-/

namespace LeanPEP
namespace Toy
namespace FiniteGD
namespace ParametricUpper

open scoped BigOperators

private theorem unitCoeff_same_mul_eq_zero_of_ne
    {N : ℕ} (a r s : Fin (N + 1)) (hrs : r ≠ s) :
    unitCoeff a r * unitCoeff a s = 0 := by
  by_cases hra : r = a
  · subst r
    simp [unitCoeff, hrs, Ne.symm hrs]
  · simp [unitCoeff, hra]

/-- Every interpolation slack has a symmetric ordered quadratic coefficient
matrix. -/
theorem slackPolyQ_quadCoeff_swap
    {N : ℕ} (i j : Point N) (r s : Fin (N + 1)) :
    (slackPolyQ i j).quadCoeff r s =
      (slackPolyQ i j).quadCoeff s r := by
  rw [slackPolyQ_quadCoeff, slackPolyQ_quadCoeff]
  unfold symOuterQ
  ring

/-- A weighted interpolation list has a symmetric ordered quadratic
coefficient matrix. -/
theorem interpPolySumQ_quadCoeff_swap
    {N : ℕ} (terms : List (InterpTermQ N))
    (r s : Fin (N + 1)) :
    (interpPolySumQ terms).quadCoeff r s =
      (interpPolySumQ terms).quadCoeff s r := by
  induction terms with
  | nil =>
      rfl
  | cons t ts ih =>
      simp [interpPolySumQ, QuadPolyQ.add, QuadPolyQ.scale,
        slackPolyQ_quadCoeff_swap, ih]

/-- A weighted affine-square list has a symmetric ordered quadratic
coefficient matrix. -/
theorem squarePolySumQ_quadCoeff_swap
    {N : ℕ} (terms : List (SquareTermQ N))
    (r s : Fin (N + 1)) :
    (squarePolySumQ terms).quadCoeff r s =
      (squarePolySumQ terms).quadCoeff s r := by
  induction terms with
  | nil =>
      rfl
  | cons t ts ih =>
      change
        t.weight *
              ((t.form.gradCoeff r * t.form.gradCoeff s +
                t.form.gradCoeff r * t.form.gradCoeff s) / 2) +
            (squarePolySumQ ts).quadCoeff r s =
          t.weight *
              ((t.form.gradCoeff s * t.form.gradCoeff r +
                t.form.gradCoeff s * t.form.gradCoeff r) / 2) +
            (squarePolySumQ ts).quadCoeff s r
      rw [ih]
      ring

/-- The generated interpolation quadratic sum is symmetric in its ordered
indices. -/
theorem gdQuadraticInterpSumQ_swap
    (N : ℕ) (r s : Fin (N + 1)) :
    gdQuadraticInterpSumQ N r s =
      gdQuadraticInterpSumQ N s r := by
  calc
    gdQuadraticInterpSumQ N r s =
        (interpPolySumQ (gdInterpTermsQ N)).quadCoeff r s :=
      (gdInterpTermsQ_quadCoeff N r s).symm
    _ = (interpPolySumQ (gdInterpTermsQ N)).quadCoeff s r :=
      interpPolySumQ_quadCoeff_swap (gdInterpTermsQ N) r s
    _ = gdQuadraticInterpSumQ N s r :=
      gdInterpTermsQ_quadCoeff N s r

/-- The generated square quadratic sum is symmetric in its ordered indices. -/
theorem gdQuadraticSquareSumQ_swap
    (N : ℕ) (r s : Fin (N + 1)) :
    gdQuadraticSquareSumQ N r s =
      gdQuadraticSquareSumQ N s r := by
  calc
    gdQuadraticSquareSumQ N r s =
        (squarePolySumQ (gdSquareTermsQ N)).quadCoeff r s :=
      (gdSquareTermsQ_quadCoeff N r s).symm
    _ = (squarePolySumQ (gdSquareTermsQ N)).quadCoeff s r :=
      squarePolySumQ_quadCoeff_swap (gdSquareTermsQ N) r s
    _ = gdQuadraticSquareSumQ N s r :=
      gdSquareTermsQ_quadCoeff N s r

/-- Gradient coefficient of the symbolic displacement from the star point to
one iterate. -/
theorem xAffineQ_star_sub_iter_gradCoeff
    (N : ℕ) (k r : Fin (N + 1)) :
    (GradAffineQ.sub
      (xAffineQ (Point.star : Point N))
      (xAffineQ (Point.iter k))).gradCoeff r =
        if r.val < k.val then 1 else 0 := by
  simp [xAffineQ, GradAffineQ.sub, GradAffineQ.add,
    GradAffineQ.neg, GradAffineQ.zero, GradAffineQ.const,
    prefixAffine_gradCoeff]

/-- Gradient coefficient of the symbolic gradient difference from the star
point to one iterate. -/
theorem gradAffineQ_star_sub_iter_gradCoeff
    (N : ℕ) (k r : Fin (N + 1)) :
    (GradAffineQ.sub
      (gradAffineQ (Point.star : Point N))
      (gradAffineQ (Point.iter k))).gradCoeff r =
        -unitCoeff k r := by
  simp [gradAffineQ, GradAffineQ.sub, GradAffineQ.add,
    GradAffineQ.neg, GradAffineQ.zero, GradAffineQ.basis]

/-- For `r < s`, one star-to-iterate slack contributes `-1/2` exactly when
its iterate index is `s`. -/
theorem slackPolyQ_star_iter_quadCoeff_of_lt
    (N : ℕ) (r s k : Fin (N + 1))
    (hrs : r.val < s.val) :
    (slackPolyQ (Point.star : Point N) (Point.iter k)).quadCoeff r s =
      -((1 : ℚ) / 2) * unitCoeff k s := by
  have hrsne : r ≠ s := by
    intro h
    have hval : r.val = s.val := by
      simpa using congrArg (fun z : Fin (N + 1) => z.val) h
    omega
  have hdiag : unitCoeff k r * unitCoeff k s = 0 :=
    unitCoeff_same_mul_eq_zero_of_ne k r s hrsne
  have hnegdiag :
      (-unitCoeff k r) * (-unitCoeff k s) = 0 := by
    simpa using hdiag
  have hleft :
      unitCoeff k r * (if s.val < k.val then 1 else 0) = 0 := by
    by_cases hrk : r = k
    · subst r
      have hnot : ¬s.val < k.val := by omega
      simp [unitCoeff, hnot]
    · simp [unitCoeff, hrk]
  have hright :
      (if r.val < k.val then 1 else 0) * unitCoeff k s =
        unitCoeff k s := by
    by_cases hsk : s = k
    · subst s
      simp [unitCoeff, hrs]
    · simp [unitCoeff, hsk, Ne.symm hsk]
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
  rw [hleft, hright, hnegdiag]
  ring

/-- The symbolic displacement between two consecutive generated iterates is
the current gradient basis vector. -/
theorem xAffineQ_consecutive_sub_gradCoeff
    (N : ℕ) (k : Fin N) (r : Fin (N + 1)) :
    (GradAffineQ.sub
      (xAffineQ (Point.iter (⟨k.val, by omega⟩ : Fin (N + 1))))
      (xAffineQ (Point.iter (⟨k.val + 1, by omega⟩ : Fin (N + 1))))).gradCoeff r =
        unitCoeff (⟨k.val, by omega⟩ : Fin (N + 1)) r := by
  by_cases hlt : r.val < k.val
  · have hltSucc : r.val < k.val + 1 := by omega
    have hle : r.val ≤ k.val := Nat.le_of_lt hlt
    have hne : r ≠ (⟨k.val, by omega⟩ : Fin (N + 1)) := by
      intro h
      have hval : r.val = k.val := by
        simpa using congrArg (fun z : Fin (N + 1) => z.val) h
      omega
    simp [GradAffineQ.sub, GradAffineQ.add, GradAffineQ.neg,
      xAffineQ, GradAffineQ.const, prefixAffine_gradCoeff,
      unitCoeff, hlt, hltSucc, hle, hne]
  · by_cases heq : r.val = k.val
    · have hr : r = (⟨k.val, by omega⟩ : Fin (N + 1)) := by
        apply Fin.ext
        exact heq
      rw [hr]
      simp [GradAffineQ.sub, GradAffineQ.add, GradAffineQ.neg,
        xAffineQ, GradAffineQ.const, prefixAffine_gradCoeff,
        unitCoeff]
    · have hle : k.val ≤ r.val := Nat.le_of_not_gt hlt
      have hkr : k.val < r.val := lt_of_le_of_ne hle (Ne.symm heq)
      have hnotSucc : ¬r.val < k.val + 1 := by omega
      have hne : r ≠ (⟨k.val, by omega⟩ : Fin (N + 1)) := by
        intro h
        have hval : r.val = k.val := by
          simpa using congrArg (fun z : Fin (N + 1) => z.val) h
        exact heq hval
      simp [GradAffineQ.sub, GradAffineQ.add, GradAffineQ.neg,
        xAffineQ, GradAffineQ.const, prefixAffine_gradCoeff,
        unitCoeff, hlt, hnotSucc, hkr, hne]

/-- Gradient difference between two consecutive generated iterates. -/
theorem gradAffineQ_consecutive_sub_gradCoeff
    (N : ℕ) (k : Fin N) (r : Fin (N + 1)) :
    (GradAffineQ.sub
      (gradAffineQ (Point.iter (⟨k.val, by omega⟩ : Fin (N + 1))))
      (gradAffineQ (Point.iter (⟨k.val + 1, by omega⟩ : Fin (N + 1))))).gradCoeff r =
        unitCoeff (⟨k.val, by omega⟩ : Fin (N + 1)) r -
          unitCoeff (⟨k.val + 1, by omega⟩ : Fin (N + 1)) r := by
  simp [gradAffineQ, GradAffineQ.sub, GradAffineQ.add,
    GradAffineQ.neg, GradAffineQ.basis] <;> ring

/-- Consecutive-iterate interpolation slacks have no strictly off-diagonal
sampled-gradient-quadratic coefficient. -/
theorem slackPolyQ_consecutive_quadCoeff_of_ne
    (N : ℕ) (k : Fin N) (r s : Fin (N + 1))
    (hrs : r ≠ s) :
    (slackPolyQ
      (Point.iter (⟨k.val, by omega⟩ : Fin (N + 1)))
      (Point.iter (⟨k.val + 1, by omega⟩ : Fin (N + 1)))).quadCoeff r s = 0 := by
  let a : Fin (N + 1) := ⟨k.val, by omega⟩
  let b : Fin (N + 1) := ⟨k.val + 1, by omega⟩
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
  have haa : unitCoeff a r * unitCoeff a s = 0 :=
    unitCoeff_same_mul_eq_zero_of_ne a r s hrs
  have hbb : unitCoeff b r * unitCoeff b s = 0 :=
    unitCoeff_same_mul_eq_zero_of_ne b r s hrs
  rw [slackPolyQ_quadCoeff, hx, hg]
  simp only [gradAffineQ, GradAffineQ.basis]
  unfold symOuterQ
  calc
    -((unitCoeff b r * unitCoeff a s +
          unitCoeff a r * unitCoeff b s) / 2) -
        (1 / 2) *
          (((unitCoeff a r - unitCoeff b r) *
                (unitCoeff a s - unitCoeff b s) +
              (unitCoeff a r - unitCoeff b r) *
                (unitCoeff a s - unitCoeff b s)) / 2) =
      -((unitCoeff a r * unitCoeff a s +
          unitCoeff b r * unitCoeff b s) / 2) := by
        ring
    _ = 0 := by
      rw [haa, hbb]
      ring

/-- The generated star interpolation list contributes exactly
`-gdStarWeightQ N s / 2` at a strict upper-triangular entry `(r,s)`. -/
theorem gdStarTermsQ_quadCoeff_of_lt
    (N : ℕ) (r s : Fin (N + 1))
    (hrs : r.val < s.val) :
    (interpPolySumQ (gdStarTermsQ N)).quadCoeff r s =
      -((1 : ℚ) / 2) * gdStarWeightQ N s := by
  classical
  rw [interpPolySumQ_quadCoeff]
  simp only [gdStarTermsQ, List.map_map, Function.comp_apply]
  rw [← Fin.sum_univ_def]
  rw [Fintype.sum_eq_single s (by
    intro k hks
    simp only [Function.comp_apply]
    rw [slackPolyQ_star_iter_quadCoeff_of_lt N r s k hrs]
    simp [unitCoeff, hks, Ne.symm hks])]
  simp only [Function.comp_apply]
  rw [slackPolyQ_star_iter_quadCoeff_of_lt N r s s hrs]
  simp [unitCoeff] <;> ring

/-- The generated consecutive-iterate interpolation list contributes zero at
all strictly off-diagonal entries. -/
theorem gdChainTermsQ_quadCoeff_of_ne
    (N : ℕ) (r s : Fin (N + 1))
    (hrs : r ≠ s) :
    (interpPolySumQ (gdChainTermsQ N)).quadCoeff r s = 0 := by
  rw [interpPolySumQ_quadCoeff]
  simp only [gdChainTermsQ, List.map_map]
  rw [← Fin.sum_univ_def]
  apply Finset.sum_eq_zero
  intro k hk
  simp only [Function.comp_apply,
    slackPolyQ_consecutive_quadCoeff_of_ne N k r s hrs, mul_zero]

/-- For `r < s`, the complete generated interpolation contribution is
`-gdStarWeightQ N s / 2`. -/
theorem gdQuadraticInterpSumQ_of_lt
    (N : ℕ) (r s : Fin (N + 1))
    (hrs : r.val < s.val) :
    gdQuadraticInterpSumQ N r s =
      -((1 : ℚ) / 2) * gdStarWeightQ N s := by
  have hrsne : r ≠ s := by
    intro h
    have hval : r.val = s.val := by
      simpa using congrArg (fun z : Fin (N + 1) => z.val) h
    omega
  calc
    gdQuadraticInterpSumQ N r s =
        (interpPolySumQ (gdInterpTermsQ N)).quadCoeff r s :=
      (gdInterpTermsQ_quadCoeff N r s).symm
    _ = (interpPolySumQ (gdStarTermsQ N)).quadCoeff r s +
          (interpPolySumQ (gdChainTermsQ N)).quadCoeff r s := by
      unfold gdInterpTermsQ
      exact interpPolySumQ_append_quadCoeff
        (gdStarTermsQ N) (gdChainTermsQ N) r s
    _ = -((1 : ℚ) / 2) * gdStarWeightQ N s := by
      rw [gdStarTermsQ_quadCoeff_of_lt N r s hrs,
        gdChainTermsQ_quadCoeff_of_ne N r s hrsne]
      ring

/-- One square contribution at `(r,s)` with `r < s` is `-1/2` times the
same square's gradient-linear contribution at `s`. -/
theorem gdQuadraticSquareContributionQ_eq_neg_half_gradient_of_lt
    (N : ℕ) (r s k : Fin (N + 1))
    (hrs : r.val < s.val) :
    gdQuadraticSquareContributionQ N r s k =
      -((1 : ℚ) / 2) * gdGradientSquareContributionQ N s k := by
  by_cases hks : k = s
  · subst k
    rw [gdGradientSquareContributionQ_self]
    unfold gdQuadraticSquareContributionQ
    rw [gdSquareFormQ_gradCoeff_of_lt N r s hrs,
      gdSquareFormQ_gradCoeff_self]
    ring
  · by_cases hsk : s.val < k.val
    · rw [gdGradientSquareContributionQ_of_lt N s k hsk,
        gdConstantContributionQ_closed]
      unfold gdQuadraticSquareContributionQ
      rw [gdSquareFormQ_gradCoeff_of_lt N r k (lt_trans hrs hsk),
        gdSquareFormQ_gradCoeff_of_lt N s k hsk]
      ring
    · have hvalne : k.val ≠ s.val := by
        intro hval
        apply hks
        apply Fin.ext
        exact hval
      have hkslt : k.val < s.val := by omega
      rw [gdGradientSquareContributionQ_of_gt N s k hkslt]
      unfold gdQuadraticSquareContributionQ
      rw [gdSquareFormQ_gradCoeff_of_gt N s k hkslt]
      ring

/-- The list-defined ordered square contribution is the corresponding `Fin`
sum. -/
theorem gdQuadraticSquareSumQ_eq_fin_sum
    (N : ℕ) (r s : Fin (N + 1)) :
    gdQuadraticSquareSumQ N r s =
      ∑ k : Fin (N + 1),
        gdQuadraticSquareContributionQ N r s k := by
  unfold gdQuadraticSquareSumQ
  symm
  exact Fin.sum_univ_def (gdQuadraticSquareContributionQ N r s)

/-- For `r < s`, the complete generated square contribution is `-1/2` times
the already closed gradient-linear square sum at `s`. -/
theorem gdQuadraticSquareSumQ_eq_neg_half_gradient_of_lt
    (N : ℕ) (r s : Fin (N + 1))
    (hrs : r.val < s.val) :
    gdQuadraticSquareSumQ N r s =
      -((1 : ℚ) / 2) * gdGradientSquareSumQ N s := by
  rw [gdQuadraticSquareSumQ_eq_fin_sum,
    gdGradientSquareSumQ_eq_fin_sum]
  calc
    (∑ k : Fin (N + 1),
        gdQuadraticSquareContributionQ N r s k) =
      ∑ k : Fin (N + 1),
        -((1 : ℚ) / 2) * gdGradientSquareContributionQ N s k := by
      apply Finset.sum_congr rfl
      intro k hk
      exact gdQuadraticSquareContributionQ_eq_neg_half_gradient_of_lt
        N r s k hrs
    _ = -((1 : ℚ) / 2) *
          (∑ k : Fin (N + 1),
            gdGradientSquareContributionQ N s k) := by
      rw [Finset.mul_sum]

/-- Every strict upper-triangular generated quadratic coefficient vanishes. -/
theorem gdQuadraticCoefficientIdentityQ_of_lt
    (N : ℕ) (r s : Fin (N + 1))
    (hrs : r.val < s.val) :
    gdQuadraticInterpSumQ N r s +
      gdQuadraticSquareSumQ N r s = 0 := by
  rw [gdQuadraticInterpSumQ_of_lt N r s hrs,
    gdQuadraticSquareSumQ_eq_neg_half_gradient_of_lt N r s hrs]
  have hcancel := gdGradientCoefficientIdentityQ_all N s
  calc
    -((1 : ℚ) / 2) * gdStarWeightQ N s +
        -((1 : ℚ) / 2) * gdGradientSquareSumQ N s =
      -((1 : ℚ) / 2) *
        (gdStarWeightQ N s + gdGradientSquareSumQ N s) := by
      ring
    _ = 0 := by
      rw [hcancel]
      ring

/-- Every ordered off-diagonal generated quadratic coefficient vanishes. -/
theorem gdQuadraticCoefficientIdentityQ_offDiagonal
    (N : ℕ) (r s : Fin (N + 1))
    (hrs : r ≠ s) :
    gdQuadraticInterpSumQ N r s +
      gdQuadraticSquareSumQ N r s = 0 := by
  have hvalne : r.val ≠ s.val := by
    intro hval
    apply hrs
    apply Fin.ext
    exact hval
  by_cases hlt : r.val < s.val
  · exact gdQuadraticCoefficientIdentityQ_of_lt N r s hlt
  · have hgt : s.val < r.val := by omega
    calc
      gdQuadraticInterpSumQ N r s +
          gdQuadraticSquareSumQ N r s =
        gdQuadraticInterpSumQ N s r +
          gdQuadraticSquareSumQ N s r := by
        rw [gdQuadraticInterpSumQ_swap, gdQuadraticSquareSumQ_swap]
      _ = 0 := gdQuadraticCoefficientIdentityQ_of_lt N s r hgt

/-- Every off-diagonal ordered quadratic coefficient of the generated
certificate matches the target polynomial. -/
theorem gdCertificate_quadCoeff_of_ne
    (N : ℕ) (r s : Fin (N + 1))
    (hrs : r ≠ s) :
    (certificateRhsPolyQ (gdUpperCertQ N)).quadCoeff r s =
      (upperTargetPolyQ
        (gdBoundQ N)
        (gdObjective N)).quadCoeff r s := by
  rw [gdCertificateRhs_quadCoeff_eq_quadraticSumsQ,
    upperTargetPolyQ_quadCoeff]
  exact gdQuadraticCoefficientIdentityQ_offDiagonal N r s hrs

/-- Off-diagonal coefficient equality packaged as one ordered family. -/
theorem gdCertificate_quadCoefficients_offDiagonal
    (N : ℕ) :
    ∀ r s : Fin (N + 1), r ≠ s →
      (certificateRhsPolyQ (gdUpperCertQ N)).quadCoeff r s =
        (upperTargetPolyQ
          (gdBoundQ N)
          (gdObjective N)).quadCoeff r s := by
  intro r s hrs
  exact gdCertificate_quadCoeff_of_ne N r s hrs

end ParametricUpper
end FiniteGD
end Toy
end LeanPEP
