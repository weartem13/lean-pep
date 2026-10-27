import LeanPEP.Profiles.ProximalGradientCertificateLocal

/-! # Finite coefficient-sum identities used to assemble the original certificate -/

namespace LeanPEP.Profiles.ProximalGradientCertificate

open scoped BigOperators

section Module
variable {M : Type*} [AddCommGroup M] [Module ℚ M]

/-- Cancel the smooth star squares before doing any finite reindexing. -/
theorem smooth_component_balance (n : ℕ) (F K D : Fin (n + 2) → M)
    (C E : Fin (n + 1) → M) (Fstar : M) :
    (∑ i : Fin (n + 2), smoothStarWeightQ n i •
      (Fstar - F i + K i - (1/2 : ℚ) • D i)) +
    (∑ i : Fin (n + 1), smoothChainWeightQ n i •
      (F i.castSucc - F i.succ - C i - (1/2 : ℚ) • E i)) +
    (∑ i : Fin (n + 2), (smoothStarWeightQ n i / 2) • D i) =
      Fstar - F (Fin.last (n + 1)) + K (Fin.last (n + 1)) +
      ∑ i : Fin (n + 1), smoothChainWeightQ n i •
        (K i.castSucc - K i.succ - C i - (1/2 : ℚ) • E i) := by
  have hcancel :
      (∑ i : Fin (n + 2), smoothStarWeightQ n i •
        (Fstar - F i + K i - (1/2 : ℚ) • D i)) +
      (∑ i : Fin (n + 2), (smoothStarWeightQ n i / 2) • D i) =
      ∑ i : Fin (n + 2), smoothStarWeightQ n i • (Fstar - F i + K i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [smul_sub, smul_smul, div_eq_mul_inv, one_mul]
    abel
  have hflow := smooth_weighted_sum n (fun i => Fstar - F i + K i)
  have hcombine :
      (∑ i : Fin (n + 1), smoothChainWeightQ n i •
        ((Fstar - F i.castSucc + K i.castSucc) - (Fstar - F i.succ + K i.succ))) +
      (∑ i : Fin (n + 1), smoothChainWeightQ n i •
        (F i.castSucc - F i.succ - C i - (1/2 : ℚ) • E i)) =
      ∑ i : Fin (n + 1), smoothChainWeightQ n i •
        (K i.castSucc - K i.succ - C i - (1/2 : ℚ) • E i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← smul_add]
    congr 1
    abel
  calc
    _ = ((∑ i : Fin (n + 2), smoothStarWeightQ n i •
        (Fstar - F i + K i - (1/2 : ℚ) • D i)) +
        (∑ i : Fin (n + 2), (smoothStarWeightQ n i / 2) • D i)) +
        (∑ i : Fin (n + 1), smoothChainWeightQ n i •
          (F i.castSucc - F i.succ - C i - (1/2 : ℚ) • E i)) := by abel
    _ = _ := by rw [hcancel, hflow, add_assoc, hcombine]

/-- Reindex the nonsmooth support terms to all edges, with q_0=0 and q_T=1. -/
theorem node_flux_edge_sum (n : ℕ) (A K : Fin (n + 1) → M) :
    (∑ i : Fin (n + 1),
      (nodeFluxQ n (i.val + 1) • K i - nodeFluxQ n i.val • A i)) =
      K (Fin.last n) + ∑ i : Fin n,
        nonsmoothChainWeightQ n i • (K i.castSucc - A i.succ) := by
  rw [Finset.sum_sub_distrib]
  rw [Fin.sum_univ_castSucc (fun i : Fin (n + 1) => nodeFluxQ n (i.val + 1) • K i)]
  rw [Fin.sum_univ_succ (fun i : Fin (n + 1) => nodeFluxQ n i.val • A i)]
  simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_last, Fin.val_zero,
    nodeFluxQ_zero, nodeFluxQ_last, zero_smul, one_smul, zero_add,
    nonsmoothChainWeightQ_flux, smul_sub, Finset.sum_sub_distrib]
  abel

/-- Nonsmooth value/support cancellation has no fictitious initial subgradient. -/
theorem nonsmooth_component_balance (n : ℕ) (H A K : Fin (n + 1) → M) (Hstar : M) :
    (∑ i : Fin (n + 1), nonsmoothStarWeightQ n i • (Hstar - H i + K i)) +
    (∑ i : Fin n, nonsmoothChainWeightQ n i •
      (H i.castSucc - H i.succ - (A i.succ - K i.succ))) =
      Hstar - H (Fin.last n) +
        ∑ i : Fin (n + 1),
          (nodeFluxQ n (i.val + 1) • K i - nodeFluxQ n i.val • A i) := by
  rw [nonsmooth_weighted_sum, node_flux_edge_sum]
  have hcombine :
      (∑ i : Fin n, nonsmoothChainWeightQ n i •
        ((Hstar - H i.castSucc + K i.castSucc) - (Hstar - H i.succ + K i.succ))) +
      (∑ i : Fin n, nonsmoothChainWeightQ n i •
        (H i.castSucc - H i.succ - (A i.succ - K i.succ))) =
      ∑ i : Fin n, nonsmoothChainWeightQ n i • (K i.castSucc - A i.succ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← smul_add]
    congr 1
    abel
  calc
    _ = Hstar - H (Fin.last n) + K (Fin.last n) +
        ((∑ i : Fin n, nonsmoothChainWeightQ n i •
          ((Hstar - H i.castSucc + K i.castSucc) - (Hstar - H i.succ + K i.succ))) +
        (∑ i : Fin n, nonsmoothChainWeightQ n i •
          (H i.castSucc - H i.succ - (A i.succ - K i.succ)))) := by abel
    _ = _ := by rw [hcombine]; abel

end Module

end LeanPEP.Profiles.ProximalGradientCertificate
