import LeanPEP.Profiles.ProximalGradientMigration

/-!
# Closed-form positive-horizon proximal-gradient certificate candidates

`n` still means T = n+1 steps of the EXISTING compiler. There are no new
model, interpolation, PSD, or coefficient checkers in this module.

C3A proves all-horizon multiplier/factor nonnegativity and reduces acceptance
to ONE exact coefficient identity. That identity is kernel-decided below for
T = 1,2,3,4 only. The unrestricted identity is deliberately not claimed here.
The factors are explicit rational formulas, not numerical LDL output.
-/

namespace LeanPEP.Profiles.ProximalGradientCertificate

open LeanPEP.GramPEP
open LeanPEP.Profiles.ProximalGradient

def boundQ (n : ℕ) : ℚ := 1 / (4 * ((n : ℚ) + 1))

@[simp] theorem boundQ_cast (n : ℕ) :
    (boundQ n : ℝ) = 1 / (4 * ((n : ℝ) + 1)) := by
  norm_num [boundQ]

def smoothStarWeightQ (n : ℕ) (i : Fin (n + 2)) : ℚ :=
  if i.val = 0 then 1 / (2 * ((n : ℚ) + 1))
  else if i.val = n + 1 then 1 / ((n : ℚ) + 2)
  else (2 * ((n : ℚ) + 1) + 1) /
    ((2 * ((n : ℚ) + 1) - i.val) * (2 * ((n : ℚ) + 1) - i.val + 1))

def smoothChainWeightQ (n : ℕ) (i : Fin (n + 1)) : ℚ :=
  ((i.val : ℚ) + 1) / (2 * ((n : ℚ) + 1) - i.val)

/-- Residual index j means the sample at x_(j+1). -/
def nonsmoothStarWeightQ (n : ℕ) (j : Fin (n + 1)) : ℚ :=
  (2 * ((n : ℚ) + 1)) /
    ((2 * ((n : ℚ) + 1) - j.val - 1) * (2 * ((n : ℚ) + 1) - j.val))

def nonsmoothChainWeightQ (n : ℕ) (j : Fin n) : ℚ :=
  ((j.val : ℚ) + 1) / (2 * ((n : ℚ) + 1) - j.val - 1)

/-- D_i = T + i (2T-i-1), positive on i = 0,...,T-1. -/
def pivotNumeratorQ (n : ℕ) (i : Fin (n + 1)) : ℚ :=
  ((n : ℚ) + 1) + i.val * (2 * ((n : ℚ) + 1) - i.val - 1)

def mixedWeightQ (n : ℕ) (i : Fin (n + 1)) : ℚ :=
  pivotNumeratorQ n i / (2 * ((n : ℚ) + 1) - i.val) ^ 2

def mixedRatioQ (n : ℕ) (i : Fin (n + 1)) : ℚ :=
  (2 * ((n : ℚ) + 1) - i.val) / (2 * ((n : ℚ) + 1) - i.val - 1)

def mixedGradientQ (n : ℕ) (i : Fin (n + 1)) : ℚ :=
  (((i.val : ℚ) + 1) * (2 * ((n : ℚ) + 1) - i.val)) /
    (2 * pivotNumeratorQ n i)

def gradientDifferenceWeightQ (n : ℕ) (i : Fin (n + 1)) : ℚ :=
  (i.val * ((i.val : ℚ) + 1) * (2 * ((n : ℚ) + 1) - i.val - 1)) /
    (4 * pivotNumeratorQ n i * (2 * ((n : ℚ) + 1) - i.val))

private theorem gradient_den_pos (n : ℕ) (i : Fin (n + 2)) :
    (0 : ℚ) < 2 * ((n : ℚ) + 1) - i.val := by
  have hi : (i.val : ℚ) ≤ (n : ℚ) + 1 := by
    exact_mod_cast (Nat.le_of_lt_succ i.isLt)
  have hn : (0 : ℚ) ≤ n := by positivity
  linarith

private theorem step_den_pos (n : ℕ) (i : Fin (n + 1)) :
    (0 : ℚ) < 2 * ((n : ℚ) + 1) - i.val - 1 := by
  have hi : (i.val : ℚ) ≤ (n : ℚ) := by
    exact_mod_cast (Nat.le_of_lt_succ i.isLt)
  have hn : (0 : ℚ) ≤ n := by positivity
  linarith

theorem boundQ_pos (n : ℕ) : 0 < boundQ n := by
  unfold boundQ
  positivity

theorem smoothStarWeightQ_nonneg (n : ℕ) (i : Fin (n + 2)) :
    0 ≤ smoothStarWeightQ n i := by
  have hd := gradient_den_pos n i
  unfold smoothStarWeightQ
  split_ifs <;> positivity

theorem smoothChainWeightQ_nonneg (n : ℕ) (i : Fin (n + 1)) :
    0 ≤ smoothChainWeightQ n i := by
  have hd := gradient_den_pos n i.castSucc
  change (0 : ℚ) < 2 * ((n : ℚ) + 1) - i.val at hd
  unfold smoothChainWeightQ
  positivity

theorem nonsmoothStarWeightQ_nonneg (n : ℕ) (j : Fin (n + 1)) :
    0 ≤ nonsmoothStarWeightQ n j := by
  have hd := step_den_pos n j
  have hd' : (0 : ℚ) < 2 * ((n : ℚ) + 1) - j.val := by linarith
  unfold nonsmoothStarWeightQ
  positivity

theorem nonsmoothChainWeightQ_nonneg (n : ℕ) (j : Fin n) :
    0 ≤ nonsmoothChainWeightQ n j := by
  have hd := step_den_pos n j.castSucc
  change (0 : ℚ) < 2 * ((n : ℚ) + 1) - j.val - 1 at hd
  unfold nonsmoothChainWeightQ
  positivity

theorem pivotNumeratorQ_pos (n : ℕ) (i : Fin (n + 1)) :
    0 < pivotNumeratorQ n i := by
  have hd := step_den_pos n i
  unfold pivotNumeratorQ
  positivity

theorem mixedWeightQ_nonneg (n : ℕ) (i : Fin (n + 1)) :
    0 ≤ mixedWeightQ n i := by
  have hd := pivotNumeratorQ_pos n i
  exact div_nonneg (le_of_lt hd) (sq_nonneg _)

theorem gradientDifferenceWeightQ_nonneg (n : ℕ) (i : Fin (n + 1)) :
    0 ≤ gradientDifferenceWeightQ n i := by
  have hp := pivotNumeratorQ_pos n i
  have hd := step_den_pos n i
  have hd' : (0 : ℚ) < 2 * ((n : ℚ) + 1) - i.val := by linarith
  unfold gradientDifferenceWeightQ
  positivity

private theorem rowMajor_lt {k : ℕ} (i j : Fin k) :
    i.val * k + j.val < k ^ 2 := by
  have hi : i.val + 1 ≤ k := by omega
  have hm := Nat.mul_le_mul_right k hi
  have hj := j.isLt
  nlinarith

/-- Row-major source constraint indices, with the original two-block order. -/
def smoothIndex (n : ℕ) (i j : Fin (n + 3)) : Fin (modelQ n).assumptions.length :=
  ⟨i.val * (n + 3) + j.val, by
    rw [modelQ_constraint_count]
    have h := rowMajor_lt i j
    omega⟩

def nonsmoothIndex (n : ℕ) (i j : Fin (n + 2)) : Fin (modelQ n).assumptions.length :=
  ⟨(n + 3) ^ 2 + i.val * (n + 2) + j.val, by
    rw [modelQ_constraint_count]
    have h := rowMajor_lt i j
    omega⟩

def radiusIndex (n : ℕ) : Fin (modelQ n).assumptions.length :=
  ⟨(n + 3) ^ 2 + (n + 2) ^ 2, by rw [modelQ_constraint_count]; omega⟩

def smoothStarTermQ (n : ℕ) (i : Fin (n + 2)) : AssumptionTermQ (modelQ n) :=
  { weight := smoothStarWeightQ n i, index := smoothIndex n 0 i.succ }

def smoothChainTermQ (n : ℕ) (i : Fin (n + 1)) : AssumptionTermQ (modelQ n) :=
  { weight := smoothChainWeightQ n i
    index := smoothIndex n i.castSucc.succ i.succ.succ }

def nonsmoothStarTermQ (n : ℕ) (j : Fin (n + 1)) : AssumptionTermQ (modelQ n) :=
  { weight := nonsmoothStarWeightQ n j, index := nonsmoothIndex n 0 j.succ }

def nonsmoothChainTermQ (n : ℕ) (j : Fin n) : AssumptionTermQ (modelQ n) :=
  { weight := nonsmoothChainWeightQ n j
    index := nonsmoothIndex n j.castSucc.succ j.succ.succ }

def assumptionTermsQ (n : ℕ) : List (AssumptionTermQ (modelQ n)) :=
  (List.finRange (n + 2)).map (smoothStarTermQ n) ++
  (List.finRange (n + 1)).map (smoothChainTermQ n) ++
  (List.finRange (n + 1)).map (nonsmoothStarTermQ n) ++
  (List.finRange n).map (nonsmoothChainTermQ n) ++
  [{ weight := boundQ n, index := radiusIndex n }]

def mixedFactorQ (n : ℕ) (i : Fin (n + 1)) : RankOneFactorQ (basisCount n) :=
  { weight := mixedWeightQ n i
    vector := positionVecQ n i.val - mixedRatioQ n i • positionVecQ n (i.val + 1) -
      mixedGradientQ n i • (gradientVecQ i.castSucc - gradientVecQ i.succ) }

def starGradientFactorQ (n : ℕ) (i : Fin (n + 2)) : RankOneFactorQ (basisCount n) :=
  { weight := smoothStarWeightQ n i / 2
    vector := gradientVecQ i - starGradientQ n }

def gradientDifferenceFactorQ (n : ℕ) (i : Fin (n + 1)) : RankOneFactorQ (basisCount n) :=
  { weight := gradientDifferenceWeightQ n i
    vector := gradientVecQ i.castSucc - gradientVecQ i.succ }

/-- The i=0 difference factor has zero weight; it is kept for uniform indexing. -/
def dualFactorsQ (n : ℕ) : List (RankOneFactorQ (basisCount n)) :=
  (List.finRange (n + 1)).map (mixedFactorQ n) ++
  (List.finRange (n + 2)).map (starGradientFactorQ n) ++
  (List.finRange (n + 1)).map (gradientDifferenceFactorQ n)

theorem assumptionTermsQ_nonneg (n : ℕ) :
    ∀ t ∈ assumptionTermsQ n, 0 ≤ t.weight := by
  intro t ht
  simp only [assumptionTermsQ, List.mem_append, List.mem_map,
    List.mem_singleton, or_assoc] at ht
  rcases ht with ⟨i, _, rfl⟩ | ⟨i, _, rfl⟩ | ⟨i, _, rfl⟩ | ⟨i, _, rfl⟩ | rfl
  · exact smoothStarWeightQ_nonneg n i
  · exact smoothChainWeightQ_nonneg n i
  · exact nonsmoothStarWeightQ_nonneg n i
  · exact nonsmoothChainWeightQ_nonneg n i
  · exact le_of_lt (boundQ_pos n)

theorem dualFactorsQ_nonneg (n : ℕ) :
    ∀ t ∈ dualFactorsQ n, 0 ≤ t.weight := by
  intro t ht
  simp only [dualFactorsQ, List.mem_append, List.mem_map, or_assoc] at ht
  rcases ht with ⟨i, _, rfl⟩ | ⟨i, _, rfl⟩ | ⟨i, _, rfl⟩
  · exact mixedWeightQ_nonneg n i
  · exact div_nonneg (smoothStarWeightQ_nonneg n i) (by norm_num)
  · exact gradientDifferenceWeightQ_nonneg n i

theorem dualFactorsQ_count (n : ℕ) : (dualFactorsQ n).length = 3 * (n + 1) + 1 := by
  simp only [dualFactorsQ, List.length_append, List.length_map, List.length_finRange]
  omega

theorem assumptionTermsQ_count (n : ℕ) : (assumptionTermsQ n).length = 4 * (n + 1) + 1 := by
  simp only [assumptionTermsQ, List.length_append, List.length_map,
    List.length_finRange, List.length_singleton]
  omega

/-- A candidate is not asserted to be accepted merely by being defined. -/
def upperCertQ (n : ℕ) : UpperCertQ (modelQ n) :=
  { bound := boundQ n
    objective := objectiveQ n
    interpTerms := []
    assumptionTerms := assumptionTermsQ n
    dualMatrix := factorGramQ (dualFactorsQ n)
    dualFactor := { factors := dualFactorsQ n } }

theorem dualValidQ_all (n : ℕ) :
    PSDFactorValidQ (upperCertQ n).dualMatrix (upperCertQ n).dualFactor := by
  exact ⟨factorGramQ_symmetric _, dualFactorsQ_nonneg n, rfl⟩

/-- This is the sole remaining unrestricted certificate obligation in C3A. -/
def CertificateIdentityQ (n : ℕ) : Prop :=
  certificateRhsExprQ (upperCertQ n) = upperTargetExprQ (boundQ n) (objectiveQ n)

theorem upperCertQ_check_iff_identity (n : ℕ) :
    checkUpperCertQ (upperCertQ n) = true ↔ CertificateIdentityQ n := by
  constructor
  · intro hc
    exact (checkUpperCertQ_sound _ hc).identity
  · intro hi
    apply checkUpperCertQ_complete
    exact ⟨by simp [upperCertQ], assumptionTermsQ_nonneg n, dualValidQ_all n, hi⟩

-- These checks evaluate the ORIGINAL general checker on the ORIGINAL C2 model.
-- They do not replace it with a precomputed Boolean or a native-evaluation axiom.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem upperCertQ_check_one : checkUpperCertQ (upperCertQ 0) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem upperCertQ_check_two : checkUpperCertQ (upperCertQ 1) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem upperCertQ_check_three : checkUpperCertQ (upperCertQ 2) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem upperCertQ_check_four : checkUpperCertQ (upperCertQ 3) = true := by
  decide +kernel

theorem upperCertQ_check_small (n : ℕ) (hn : n ≤ 3) :
    checkUpperCertQ (upperCertQ n) = true := by
  interval_cases n
  · exact upperCertQ_check_one
  · exact upperCertQ_check_two
  · exact upperCertQ_check_three
  · exact upperCertQ_check_four

/-- Mutations leave the original factors/weights in place: they must be rejected. -/
def wrongTwoStepBoundQ : UpperCertQ (modelQ 1) :=
  { upperCertQ 1 with bound := 1/9 }

def wrongTwoStepObjectiveQ : UpperCertQ (modelQ 1) :=
  { upperCertQ 1 with
    objective := LinearExprQ.sub
      (LinearExprQ.valueVar (smoothValueIndex (Fin.last 3)))
      (LinearExprQ.valueVar (smoothValueIndex (0 : Fin 4))) }

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem wrongTwoStepBoundQ_rejected : checkUpperCertQ wrongTwoStepBoundQ = false := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem wrongTwoStepObjectiveQ_rejected : checkUpperCertQ wrongTwoStepObjectiveQ = false := by
  decide +kernel

end LeanPEP.Profiles.ProximalGradientCertificate
