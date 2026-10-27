import LeanPEP.Toy.FiniteGD.ParametricUpperTelescoping
import Mathlib.Algebra.BigOperators.Fin

/-!
# Exact function-value coefficients of the arbitrary-length GD certificate

This module folds the interpolation-flow recurrences from v0.12B4 through the
actual generated interpolation-term lists.  It proves that the complete
certificate right-hand side has function-value coefficient `0` at every
intermediate iterate and coefficient `-1` at the final iterate, exactly matching
`bound - f_N`.

Only the function-value channel of the universal polynomial identity is closed
here.  Constant, gradient-linear, and gradient-quadratic coefficients remain
separate proof obligations.
-/

namespace LeanPEP
namespace Toy
namespace FiniteGD
namespace ParametricUpper

open scoped BigOperators

/-- Function-value coefficients of one interpolation slack depend only on its
two sampled function values. -/
@[simp] theorem slackPolyQ_valueCoeff
    {N : ℕ} (i j : Point N) (r : Fin (N + 1)) :
    (slackPolyQ i j).valueCoeff r =
      (pointValuePolyQ i).valueCoeff r -
        (pointValuePolyQ j).valueCoeff r := by
  simp [slackPolyQ, QuadPolyQ.sub, QuadPolyQ.add, QuadPolyQ.neg,
    QuadPolyQ.scale, QuadPolyQ.mulAffine, QuadPolyQ.square] <;> ring

/-- Projecting a weighted interpolation sum to one function-value coefficient
is the ordinary list sum of the projected terms. -/
theorem interpPolySumQ_valueCoeff
    {N : ℕ} (terms : List (InterpTermQ N)) (r : Fin (N + 1)) :
    (interpPolySumQ terms).valueCoeff r =
      (terms.map (fun t =>
        t.weight *
          ((pointValuePolyQ t.i).valueCoeff r -
            (pointValuePolyQ t.j).valueCoeff r))).sum := by
  induction terms with
  | nil =>
      simp [interpPolySumQ, QuadPolyQ.zero]
  | cons t ts ih =>
      simp [interpPolySumQ, QuadPolyQ.add, QuadPolyQ.scale, ih]

/-- Function-value projection commutes with concatenating interpolation-term
lists. -/
theorem interpPolySumQ_append_valueCoeff
    {N : ℕ} (left right : List (InterpTermQ N))
    (r : Fin (N + 1)) :
    (interpPolySumQ (left ++ right)).valueCoeff r =
      (interpPolySumQ left).valueCoeff r +
        (interpPolySumQ right).valueCoeff r := by
  rw [interpPolySumQ_valueCoeff, interpPolySumQ_valueCoeff,
    interpPolySumQ_valueCoeff]
  simp

/-- Affine-square terms never contain function-value variables. -/
@[simp] theorem squarePolySumQ_valueCoeff
    {N : ℕ} (terms : List (SquareTermQ N)) (r : Fin (N + 1)) :
    (squarePolySumQ terms).valueCoeff r = 0 := by
  induction terms with
  | nil =>
      simp [squarePolySumQ, QuadPolyQ.zero]
  | cons t ts ih =>
      simp [squarePolySumQ, QuadPolyQ.add, QuadPolyQ.scale,
        QuadPolyQ.square, QuadPolyQ.mulAffine, ih]

/-- The star-to-iterate list contributes exactly minus the corresponding star
weight to `f_r`. -/
theorem gdStarTermsQ_valueCoeff
    (N : ℕ) (r : Fin (N + 1)) :
    (interpPolySumQ (gdStarTermsQ N)).valueCoeff r =
      -gdStarWeightQ N r := by
  classical
  rw [interpPolySumQ_valueCoeff]
  simp only [gdStarTermsQ, List.map_map, Function.comp_apply,
    pointValuePolyQ, QuadPolyQ.zero, QuadPolyQ.valueVar, zero_sub]
  rw [← Fin.sum_univ_def]
  rw [Fintype.sum_eq_single r (by
    intro k hkr
    simp [unitCoeff, hkr, Ne.symm hkr])]
  simp [unitCoeff]

/-- Positive flow leaving a function-value index through a consecutive-pair
interpolation term. -/
def gdChainSourceSumQ
    (N : ℕ) (r : Fin (N + 1)) : ℚ :=
  ∑ k : Fin N,
    gdChainWeightQ N k *
      unitCoeff (⟨k.val, by omega⟩ : Fin (N + 1)) r

/-- Negative flow entering a function-value index through a consecutive-pair
interpolation term. -/
def gdChainTargetSumQ
    (N : ℕ) (r : Fin (N + 1)) : ℚ :=
  ∑ k : Fin N,
    gdChainWeightQ N k *
      unitCoeff (⟨k.val + 1, by omega⟩ : Fin (N + 1)) r

/-- The consecutive-pair list contributes outgoing flow minus incoming flow. -/
theorem gdChainTermsQ_valueCoeff
    (N : ℕ) (r : Fin (N + 1)) :
    (interpPolySumQ (gdChainTermsQ N)).valueCoeff r =
      gdChainSourceSumQ N r - gdChainTargetSumQ N r := by
  rw [interpPolySumQ_valueCoeff]
  simp only [gdChainTermsQ, List.map_map, Function.comp_apply,
    pointValuePolyQ, QuadPolyQ.valueVar]
  rw [← Fin.sum_univ_def]
  unfold gdChainSourceSumQ gdChainTargetSumQ
  simp only [Function.comp_apply]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]

/-- At every nonfinal index, the outgoing-flow sum selects the unique
consecutive-pair weight with that source. -/
theorem gdChainSourceSumQ_eq
    (N : ℕ) (r : Fin (N + 1)) (hr : r.val < N) :
    gdChainSourceSumQ N r =
      gdChainWeightQ N ⟨r.val, hr⟩ := by
  classical
  let k0 : Fin N := ⟨r.val, hr⟩
  unfold gdChainSourceSumQ
  rw [Fintype.sum_eq_single k0 (by
    intro k hkk0
    have hne :
        (⟨k.val, by omega⟩ : Fin (N + 1)) ≠ r := by
      intro hEq
      apply hkk0
      apply Fin.ext
      simpa using congrArg (fun z : Fin (N + 1) => z.val) hEq
    simp only [unitCoeff, if_neg (Ne.symm hne), mul_zero])]
  have heq :
      (⟨k0.val, by omega⟩ : Fin (N + 1)) = r := by
    apply Fin.ext
    rfl
  calc
    gdChainWeightQ N k0 *
          unitCoeff (⟨k0.val, by omega⟩ : Fin (N + 1)) r =
        gdChainWeightQ N k0 * unitCoeff r r := by rw [heq]
    _ = gdChainWeightQ N k0 := by simp [unitCoeff]
    _ = gdChainWeightQ N ⟨r.val, hr⟩ := by rfl

/-- No consecutive-pair term leaves the final function-value index. -/
theorem gdChainSourceSumQ_last
    (N : ℕ) :
    gdChainSourceSumQ N ⟨N, by omega⟩ = 0 := by
  classical
  unfold gdChainSourceSumQ
  apply Finset.sum_eq_zero
  intro k _hk
  have hne :
      (⟨k.val, by omega⟩ : Fin (N + 1)) ≠
        (⟨N, by omega⟩ : Fin (N + 1)) := by
    intro hEq
    have hval : k.val = N := by
      simpa using congrArg (fun z : Fin (N + 1) => z.val) hEq
    exact (Nat.ne_of_lt k.isLt) hval
  simp only [unitCoeff, if_neg (Ne.symm hne), mul_zero]

/-- At every positive index, the incoming-flow sum selects the unique
consecutive-pair weight whose target is that index. -/
theorem gdChainTargetSumQ_eq
    (N : ℕ) (r : Fin (N + 1)) (hr : 0 < r.val) :
    gdChainTargetSumQ N r =
      gdChainWeightQ N ⟨r.val - 1, by omega⟩ := by
  classical
  let k0 : Fin N := ⟨r.val - 1, by omega⟩
  unfold gdChainTargetSumQ
  rw [Fintype.sum_eq_single k0 (by
    intro k hkk0
    have hne :
        (⟨k.val + 1, by omega⟩ : Fin (N + 1)) ≠ r := by
      intro hEq
      apply hkk0
      apply Fin.ext
      show k.val = r.val - 1
      have hval : k.val + 1 = r.val := by
        simpa using congrArg (fun z : Fin (N + 1) => z.val) hEq
      omega
    simp only [unitCoeff, if_neg (Ne.symm hne), mul_zero])]
  have heq :
      (⟨k0.val + 1, by omega⟩ : Fin (N + 1)) = r := by
    apply Fin.ext
    show k0.val + 1 = r.val
    dsimp [k0]
    omega
  calc
    gdChainWeightQ N k0 *
          unitCoeff (⟨k0.val + 1, by omega⟩ : Fin (N + 1)) r =
        gdChainWeightQ N k0 * unitCoeff r r := by rw [heq]
    _ = gdChainWeightQ N k0 := by simp [unitCoeff]
    _ = gdChainWeightQ N ⟨r.val - 1, by omega⟩ := by rfl

/-- No consecutive-pair term enters the initial function-value index. -/
theorem gdChainTargetSumQ_zero
    (N : ℕ) :
    gdChainTargetSumQ N ⟨0, by omega⟩ = 0 := by
  classical
  unfold gdChainTargetSumQ
  apply Finset.sum_eq_zero
  intro k _hk
  have hne :
      (⟨k.val + 1, by omega⟩ : Fin (N + 1)) ≠
        (⟨0, by omega⟩ : Fin (N + 1)) := by
    intro hEq
    have hval : k.val + 1 = 0 := by
      simpa using congrArg (fun z : Fin (N + 1) => z.val) hEq
    omega
  simp only [unitCoeff, if_neg (Ne.symm hne), mul_zero]

/-- Closed formula for the complete generated certificate's function-value
coefficient before applying the local flow recurrences. -/
theorem gdCertificateRhs_valueCoeff_flow
    (N : ℕ) (r : Fin (N + 1)) :
    (certificateRhsPolyQ (gdUpperCertQ N)).valueCoeff r =
      -gdStarWeightQ N r +
        gdChainSourceSumQ N r - gdChainTargetSumQ N r := by
  simp [certificateRhsPolyQ, gdUpperCertQ, gdInterpTermsQ,
    QuadPolyQ.add, interpPolySumQ_append_valueCoeff,
    gdStarTermsQ_valueCoeff, gdChainTermsQ_valueCoeff] <;> ring

/-- Function-value coefficients of the target polynomial are `-1` at the
objective index and zero elsewhere. -/
@[simp] theorem upperTargetPolyQ_valueCoeff
    {N : ℕ} (bound : ℚ) (objective r : Fin (N + 1)) :
    (upperTargetPolyQ bound objective).valueCoeff r =
      -unitCoeff objective r := by
  simp [upperTargetPolyQ, QuadPolyQ.sub, QuadPolyQ.add, QuadPolyQ.neg,
    QuadPolyQ.ofAffine, QuadPolyQ.valueVar]

/-- The generated certificate has exactly the target function-value
coefficient at every sampled index. -/
theorem gdCertificate_valueCoeff
    (N : ℕ) (r : Fin (N + 1)) :
    (certificateRhsPolyQ (gdUpperCertQ N)).valueCoeff r =
      (upperTargetPolyQ (gdBoundQ N) (gdObjective N)).valueCoeff r := by
  rw [gdCertificateRhs_valueCoeff_flow, upperTargetPolyQ_valueCoeff]
  by_cases hN : N = 0
  · subst N
    fin_cases r
    simp [gdChainSourceSumQ, gdChainTargetSumQ, gdObjective,
      gdStarWeightQ, unitCoeff]
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    by_cases hr0 : r.val = 0
    · have hr : r = (⟨0, by omega⟩ : Fin (N + 1)) := by
        apply Fin.ext
        exact hr0
      rw [hr]
      have hobj :
          (⟨0, by omega⟩ : Fin (N + 1)) ≠ gdObjective N := by
        intro hEq
        have hval : 0 = N := by
          simpa [gdObjective] using congrArg (fun z : Fin (N + 1) => z.val) hEq
        omega
      calc
        -gdStarWeightQ N (⟨0, by omega⟩ : Fin (N + 1)) +
              gdChainSourceSumQ N (⟨0, by omega⟩ : Fin (N + 1)) -
                gdChainTargetSumQ N (⟨0, by omega⟩ : Fin (N + 1)) =
            -gdChainWeightQ N (⟨0, hNpos⟩ : Fin N) +
              gdChainWeightQ N (⟨0, hNpos⟩ : Fin N) - 0 := by
          rw [gdChainSourceSumQ_eq N ⟨0, by omega⟩ hNpos,
            gdChainTargetSumQ_zero,
            gdStarWeightQ_zero_eq_chainWeightQ_zero N hNpos]
        _ = 0 := by ring
        _ = -unitCoeff (gdObjective N) (⟨0, by omega⟩ : Fin (N + 1)) := by
          simp only [unitCoeff, if_neg hobj, neg_zero]
    · by_cases hrN : r.val = N
      · have hr : r = (⟨N, by omega⟩ : Fin (N + 1)) := by
          apply Fin.ext
          exact hrN
        rw [hr]
        have htarget :
            gdChainTargetSumQ N ⟨N, by omega⟩ =
              gdChainWeightQ N ⟨N - 1, by omega⟩ := by
          simpa using
            (gdChainTargetSumQ_eq N ⟨N, by omega⟩ hNpos)
        rw [gdChainSourceSumQ_last, htarget,
          gdStarWeightQ_last_eq_one_sub_chainWeightQ_last N hNpos]
        simp [gdObjective, unitCoeff] <;> ring
      · have hrpos : 0 < r.val := by omega
        have hrlt : r.val < N := by omega
        let k : ℕ := r.val - 1
        have hk : k + 1 < N := by
          dsimp [k]
          omega
        have hr : r = (⟨k + 1, by omega⟩ : Fin (N + 1)) := by
          apply Fin.ext
          dsimp [k]
          omega
        rw [hr]
        have htarget :
            gdChainTargetSumQ N ⟨k + 1, by omega⟩ =
              gdChainWeightQ N ⟨k, by omega⟩ := by
          simpa using
            (gdChainTargetSumQ_eq N ⟨k + 1, by omega⟩ (by omega))
        rw [gdChainSourceSumQ_eq N ⟨k + 1, by omega⟩ hk,
          htarget,
          gdStarWeightQ_succ_eq_chainWeightQ_sub N k hk]
        have hobj :
            (⟨k + 1, by omega⟩ : Fin (N + 1)) ≠ gdObjective N := by
          intro hEq
          have hval : k + 1 = N := by
            simpa [gdObjective] using congrArg (fun z : Fin (N + 1) => z.val) hEq
          omega
        simp [unitCoeff, hobj] <;> ring

/-- The function-value channel of the arbitrary-`N` certificate identity is
fully closed. -/
theorem gdCertificate_valueCoefficients
    (N : ℕ) :
    ∀ r : Fin (N + 1),
      (certificateRhsPolyQ (gdUpperCertQ N)).valueCoeff r =
        (upperTargetPolyQ (gdBoundQ N) (gdObjective N)).valueCoeff r :=
  gdCertificate_valueCoeff N

end ParametricUpper
end FiniteGD
end Toy
end LeanPEP
