import LeanPEP.GramPEP.RationalBridge
import LeanPEP.GramPEP.PSDFactorization

/-!
# Rational PSD factor certificates imply real Gram PSD

The exact PSD checker operates on rational target matrices and rational
weighted rank-one factors.  External exact bundles are ultimately interpreted
in the real Gram semantics, so this module proves that an accepted rational
factorization also certifies the entrywise real cast of the target.

No density argument is used.  The proof reinterprets the same exact factors as
real weighted squares and checks nonnegativity directly for every real test
vector.
-/

namespace LeanPEP
namespace GramPEP

open scoped BigOperators

/-- Dot product of a real test vector with one rational factor vector. -/
def vecDotQR {m : ℕ} (u : VecExpr m ℝ) (v : VecExpr m ℚ) : ℝ :=
  ∑ i, u i * (v i : ℝ)

@[simp] theorem castGramQ_zero {m : ℕ} :
    castGramQ (0 : Gram m ℚ) = (0 : Gram m ℝ) := by
  funext i j
  simp [castGramQ]

@[simp] theorem castGramQ_add {m : ℕ} (G H : Gram m ℚ) :
    castGramQ (G + H) = castGramQ G + castGramQ H := by
  funext i j
  simp [castGramQ]

/-- Real Gram squared norm is additive in the matrix argument. -/
@[simp] theorem gramNormSq_add_gram_real
    {m : ℕ} (G H : Gram m ℝ) (u : VecExpr m ℝ) :
    gramNormSq (G + H) u = gramNormSq G u + gramNormSq H u := by
  simp [gramNormSq, gramInner, mul_add, add_mul, Finset.sum_add_distrib]

/-- One rational weighted rank-one factor becomes the same weighted real
square after entrywise casting. -/
theorem gramNormSq_cast_weightedOuterQ
    {m : ℕ} (t : RankOneFactorQ m) (u : VecExpr m ℝ) :
    gramNormSq (castGramQ (weightedOuterQ t)) u =
      (t.weight : ℝ) * (vecDotQR u t.vector)^2 := by
  calc
    gramNormSq (castGramQ (weightedOuterQ t)) u =
        ∑ i, ((t.weight : ℝ) * u i * (t.vector i : ℝ)) *
          (∑ j, u j * (t.vector j : ℝ)) := by
      unfold gramNormSq gramInner castGramQ weightedOuterQ
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      push_cast
      ring
    _ = (∑ i, (t.weight : ℝ) * u i * (t.vector i : ℝ)) *
          (∑ j, u j * (t.vector j : ℝ)) := by
      rw [Finset.sum_mul]
    _ = (t.weight : ℝ) * (∑ i, u i * (t.vector i : ℝ)) *
          (∑ j, u j * (t.vector j : ℝ)) := by
      have hfactor :
          (∑ i, (t.weight : ℝ) * u i * (t.vector i : ℝ)) =
            (t.weight : ℝ) * (∑ i, u i * (t.vector i : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [hfactor]
    _ = (t.weight : ℝ) * (vecDotQR u t.vector)^2 := by
      simp [vecDotQR, pow_two, mul_assoc]

/-- Nonnegative rational factor weights imply nonnegativity of the represented
real quadratic form. -/
theorem factorGramQ_cast_norm_nonneg
    {m : ℕ}
    (factors : List (RankOneFactorQ m))
    (hweights : ∀ t ∈ factors, 0 ≤ t.weight)
    (u : VecExpr m ℝ) :
    0 ≤ gramNormSq (castGramQ (factorGramQ factors)) u := by
  revert hweights
  induction factors with
  | nil =>
      intro hweights
      simp [factorGramQ, castGramQ, gramNormSq, gramInner]
  | cons t ts ih =>
      intro hweights
      have hweight : 0 ≤ t.weight := hweights t (by simp)
      have hrest : ∀ s ∈ ts, 0 ≤ s.weight := by
        intro s hs
        exact hweights s (by simp [hs])
      simp only [factorGramQ, castGramQ_add, gramNormSq_add_gram_real,
        gramNormSq_cast_weightedOuterQ]
      exact add_nonneg
        (mul_nonneg (Rat.cast_nonneg.mpr hweight)
          (sq_nonneg (vecDotQR u t.vector)))
        (ih hrest)

/-- Symmetry is preserved by entrywise rational-to-real casting. -/
theorem castGramQ_symmetric
    {m : ℕ} (G : Gram m ℚ) (hG : IsGramSymmetric G) :
    IsGramSymmetric (castGramQ G) := by
  intro i j
  change (G i j : ℝ) = (G j i : ℝ)
  exact congrArg (fun q : ℚ => (q : ℝ)) (hG i j)

/-- A nonnegative rational factorization is PSD after casting to reals. -/
theorem factorGramQ_cast_posSemidef
    {m : ℕ}
    (factors : List (RankOneFactorQ m))
    (hweights : ∀ t ∈ factors, 0 ≤ t.weight) :
    IsGramPosSemidef (castGramQ (factorGramQ factors)) := by
  exact ⟨castGramQ_symmetric _ (factorGramQ_symmetric factors),
    factorGramQ_cast_norm_nonneg factors hweights⟩

/-- Proposition-level rational factor validity proves real PSD of the cast
target matrix. -/
theorem psdFactorValidQ_sound_real
    {m : ℕ} (G : Gram m ℚ) (c : PSDFactorCertQ m)
    (h : PSDFactorValidQ G c) :
    IsGramPosSemidef (castGramQ G) := by
  rw [← h.identity]
  exact factorGramQ_cast_posSemidef c.factors h.weights

/-- An accepted exact rational factor certificate proves real PSD of the cast
target matrix. -/
theorem checkPSDFactorQ_sound_real
    {m : ℕ} (G : Gram m ℚ) (c : PSDFactorCertQ m)
    (h : checkPSDFactorQ G c = true) :
    IsGramPosSemidef (castGramQ G) :=
  psdFactorValidQ_sound_real G c
    ((checkPSDFactorQ_eq_true_iff G c).mp h)

end GramPEP
end LeanPEP
