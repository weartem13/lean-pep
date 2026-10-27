import LeanPEP.Profiles.ProximalGradientCertificate
import Mathlib.Algebra.BigOperators.Fin

/-!
# Exact multiplier flow for the existing proximal-gradient certificate

These are identities of the C3A rational formulas, for arbitrary `n`.
The parameter is unchanged: T = n+1 > 0.  The fluxes below are proof
bookkeeping, not new multipliers, a new model, or a new checker.
-/

namespace LeanPEP.Profiles.ProximalGradientCertificate

open scoped BigOperators

/-- The nonsmooth cumulative multiplier at node k. -/
def nodeFluxQ (n k : ℕ) : ℚ := (k : ℚ) / (2 * ((n : ℚ) + 1) - k)

/-- The smooth cumulative multiplier includes the final unit boundary. -/
def smoothFluxQ (n : ℕ) (i : Fin (n + 3)) : ℚ :=
  if i.val = n + 2 then 1
  else (i.val : ℚ) / (2 * ((n : ℚ) + 1) - i.val + 1)

/-- A node denominator is positive throughout the declared horizon. -/
theorem node_den_pos (n k : ℕ) (hk : k ≤ n + 1) :
    (0 : ℚ) < 2 * ((n : ℚ) + 1) - k := by
  have hkQ : (k : ℚ) ≤ (n : ℚ) + 1 := by exact_mod_cast hk
  have hn : (0 : ℚ) ≤ n := by positivity
  linarith

/-- The next-node denominator is also positive on each update edge. -/
theorem edge_den_pos (n : ℕ) (i : Fin (n + 1)) :
    (0 : ℚ) < 2 * ((n : ℚ) + 1) - i.val - 1 := by
  have hi : (i.val : ℚ) ≤ (n : ℚ) := by
    exact_mod_cast (Nat.le_of_lt_succ i.isLt)
  have hn : (0 : ℚ) ≤ n := by positivity
  linarith

@[simp] theorem nodeFluxQ_zero (n : ℕ) : nodeFluxQ n 0 = 0 := by
  simp [nodeFluxQ]

@[simp] theorem nodeFluxQ_last (n : ℕ) : nodeFluxQ n (n + 1) = 1 := by
  have hn : (0 : ℚ) < (n : ℚ) + 1 := by positivity
  unfold nodeFluxQ
  push_cast
  have he : 2 * ((n : ℚ) + 1) - ((n : ℚ) + 1) = (n : ℚ) + 1 := by ring
  rw [he, div_self (ne_of_gt hn)]

@[simp] theorem smoothFluxQ_zero (n : ℕ) : smoothFluxQ n 0 = 0 := by
  simp [smoothFluxQ]

@[simp] theorem smoothFluxQ_last (n : ℕ) :
    smoothFluxQ n (Fin.last (n + 2)) = 1 := by
  simp [smoothFluxQ]

/-- The old smooth chain multiplier is the interior cumulative flux. -/
theorem smoothFluxQ_edge (n : ℕ) (i : Fin (n + 1)) :
    smoothFluxQ n i.succ.castSucc = smoothChainWeightQ n i := by
  have hi : i.val + 1 ≠ n + 2 := by have := i.isLt; omega
  simp only [smoothFluxQ, Fin.val_castSucc, Fin.val_succ, if_neg hi,
    Nat.cast_add, Nat.cast_one, smoothChainWeightQ]
  congr 1 <;> ring

/-- Each smooth star multiplier is the exact difference of adjacent fluxes. -/
theorem smoothStarWeightQ_flow (n : ℕ) (i : Fin (n + 2)) :
    smoothStarWeightQ n i = smoothFluxQ n i.succ - smoothFluxQ n i.castSucc := by
  have hn : (0 : ℚ) < (n : ℚ) + 1 := by positivity
  have hn2 : (0 : ℚ) < (n : ℚ) + 2 := by positivity
  have hi : i.val ≠ n + 2 := by have := i.isLt; omega
  have hd := node_den_pos n i.val (Nat.le_of_lt_succ i.isLt)
  have hd' : (0 : ℚ) < 2 * ((n : ℚ) + 1) - i.val + 1 := by linarith
  by_cases hzero : i.val = 0
  · have hs : i.val + 1 ≠ n + 2 := by omega
    simp [smoothStarWeightQ, smoothFluxQ, hzero, hs]
  · by_cases hlast : i.val = n + 1
    · have hs : i.val + 1 = n + 2 := by omega
      simp only [smoothStarWeightQ, if_neg hzero, if_pos hlast, smoothFluxQ,
        Fin.val_succ, Fin.val_castSucc, if_pos hs, if_neg hi]
      simp only [hlast, Nat.cast_add, Nat.cast_one]
      have he : 2 * ((n : ℚ) + 1) - ((n : ℚ) + 1) + 1 = (n : ℚ) + 2 := by ring
      rw [he]
      field_simp [ne_of_gt hn2] <;> ring
    · have hs : i.val + 1 ≠ n + 2 := by omega
      simp only [smoothStarWeightQ, if_neg hzero, if_neg hlast, smoothFluxQ,
        Fin.val_succ, Fin.val_castSucc, if_neg hs, if_neg hi,
        Nat.cast_add, Nat.cast_one]
      have he : 2 * ((n : ℚ) + 1) - ((i.val : ℚ) + 1) + 1 =
          2 * ((n : ℚ) + 1) - i.val := by ring
      rw [he]
      field_simp [ne_of_gt hd, ne_of_gt hd'] <;> ring

/-- Each nonsmooth star multiplier is a difference of node fluxes. -/
theorem nonsmoothStarWeightQ_flow (n : ℕ) (i : Fin (n + 1)) :
    nonsmoothStarWeightQ n i = nodeFluxQ n (i.val + 1) - nodeFluxQ n i.val := by
  have hd := edge_den_pos n i
  have hd' : (0 : ℚ) < 2 * ((n : ℚ) + 1) - i.val := by linarith
  simp only [nonsmoothStarWeightQ, nodeFluxQ, Nat.cast_add, Nat.cast_one,
    sub_add_eq_sub_sub]
  field_simp [ne_of_gt hd, ne_of_gt hd'] <;> ring

@[simp] theorem nonsmoothChainWeightQ_flux (n : ℕ) (i : Fin n) :
    nonsmoothChainWeightQ n i = nodeFluxQ n (i.val + 1) := by
  simp only [nonsmoothChainWeightQ, nodeFluxQ, Nat.cast_add, Nat.cast_one,
    sub_add_eq_sub_sub]

/-- Discrete integration by parts, including BOTH endpoint terms.
It works in any rational module, including coefficient vectors. -/
theorem weighted_flux_sum {M : Type*} [AddCommGroup M] [Module ℚ M]
    (k : ℕ) (q : Fin (k + 2) → ℚ) (z : Fin (k + 1) → M)
    (hzero : q 0 = 0) (hlast : q (Fin.last (k + 1)) = 1) :
    (∑ i : Fin (k + 1), (q i.succ - q i.castSucc) • z i) =
      z (Fin.last k) +
        ∑ i : Fin k, q i.succ.castSucc • (z i.castSucc - z i.succ) := by
  simp only [sub_smul, Finset.sum_sub_distrib]
  rw [Fin.sum_univ_castSucc (fun i : Fin (k + 1) => q i.succ • z i)]
  rw [Fin.sum_univ_succ (fun i : Fin (k + 1) => q i.castSucc • z i)]
  simp only [Fin.castSucc_succ, Fin.succ_last, Fin.castSucc_zero,
    hzero, hlast, zero_smul, one_smul, zero_add, smul_sub,
    Finset.sum_sub_distrib]
  abel

/-- Arbitrary-horizon smooth value flow for arbitrary module-valued samples. -/
theorem smooth_weighted_sum {M : Type*} [AddCommGroup M] [Module ℚ M]
    (n : ℕ) (z : Fin (n + 2) → M) :
    (∑ i : Fin (n + 2), smoothStarWeightQ n i • z i) =
      z (Fin.last (n + 1)) +
        ∑ i : Fin (n + 1), smoothChainWeightQ n i • (z i.castSucc - z i.succ) := by
  simp_rw [smoothStarWeightQ_flow]
  rw [weighted_flux_sum (n + 1) (smoothFluxQ n) z
    (smoothFluxQ_zero n) (smoothFluxQ_last n)]
  simp only [smoothFluxQ_edge]

/-- Nonsmooth samples start at x_1; no h-value or subgradient at x_0 is used. -/
theorem nonsmooth_weighted_sum {M : Type*} [AddCommGroup M] [Module ℚ M]
    (n : ℕ) (z : Fin (n + 1) → M) :
    (∑ i : Fin (n + 1), nonsmoothStarWeightQ n i • z i) =
      z (Fin.last n) +
        ∑ i : Fin n, nonsmoothChainWeightQ n i • (z i.castSucc - z i.succ) := by
  simp_rw [nonsmoothStarWeightQ_flow]
  have h := weighted_flux_sum n (fun i : Fin (n + 2) => nodeFluxQ n i.val) z
    (nodeFluxQ_zero n) (nodeFluxQ_last n)
  simpa only [Fin.val_succ, Fin.val_castSucc, nonsmoothChainWeightQ_flux] using h

/-- The complete smooth function-value contribution has only two endpoints. -/
theorem smooth_value_balance (n : ℕ) (a : ℚ) (z : Fin (n + 2) → ℚ) :
    (∑ i : Fin (n + 2), smoothStarWeightQ n i * (a - z i)) +
      (∑ i : Fin (n + 1), smoothChainWeightQ n i * (z i.castSucc - z i.succ)) =
        a - z (Fin.last (n + 1)) := by
  have h := smooth_weighted_sum n (fun i => a - z i)
  simp only [smul_eq_mul] at h
  have he : (∑ i : Fin (n + 1), smoothChainWeightQ n i *
      ((a - z i.castSucc) - (a - z i.succ))) =
      -(∑ i : Fin (n + 1), smoothChainWeightQ n i * (z i.castSucc - z i.succ)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he] at h
  linarith

/-- The analogous cancellation is confined to the nonsmooth value block. -/
theorem nonsmooth_value_balance (n : ℕ) (a : ℚ) (z : Fin (n + 1) → ℚ) :
    (∑ i : Fin (n + 1), nonsmoothStarWeightQ n i * (a - z i)) +
      (∑ i : Fin n, nonsmoothChainWeightQ n i * (z i.castSucc - z i.succ)) =
        a - z (Fin.last n) := by
  have h := nonsmooth_weighted_sum n (fun i => a - z i)
  simp only [smul_eq_mul] at h
  have he : (∑ i : Fin n, nonsmoothChainWeightQ n i *
      ((a - z i.castSucc) - (a - z i.succ))) =
      -(∑ i : Fin n, nonsmoothChainWeightQ n i * (z i.castSucc - z i.succ)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he] at h
  linarith

end LeanPEP.Profiles.ProximalGradientCertificate
