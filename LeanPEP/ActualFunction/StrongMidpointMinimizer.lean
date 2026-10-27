import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic

/-!
# Compact-free minimization from a quadratic midpoint gap

A continuous real-valued function on a complete real normed space attains its
infimum if its range is bounded below and it has a positive quadratic midpoint
gap. This is a minimizing-sequence argument, not a compactness argument. The
Cauchy estimate is proved separately and does not require continuity or
completeness. No finite-dimensionality or sequential compactness is assumed.
-/

noncomputable section
open Filter Set
open scoped Topology
namespace LeanPEP.ActualFunction.StrongMidpointMinimizer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Any sequence with objective error at most 1/(k+1) is Cauchy under a
positive quadratic midpoint gap. The lower bound must hold at every point,
in particular at the midpoint; it is not only a bound on sequence values. -/
theorem cauchySeq_of_midpoint_gap {Q : E → ℝ} {c m : ℝ}
    (hc : 0 < c) (hlower : ∀ x, m ≤ Q x)
    (hmid : ∀ x y, Q ((1/2 : ℝ) • x + (1/2 : ℝ) • y) ≤
      (Q x + Q y)/2 - c * ‖x-y‖^2)
    (u : ℕ → E) (hu : ∀ k, Q (u k) ≤ m + 1/((k : ℝ)+1)) :
    CauchySeq u := by
  apply cauchySeq_of_le_tendsto_0 (fun N : ℕ => Real.sqrt ((1/((N : ℝ)+1))/c))
  · intro p q N hp hq
    have hpQ : Q (u p) ≤ m + 1/((N : ℝ)+1) :=
      (hu p).trans (add_le_add (le_refl _) (Nat.one_div_le_one_div hp))
    have hqQ : Q (u q) ≤ m + 1/((N : ℝ)+1) :=
      (hu q).trans (add_le_add (le_refl _) (Nat.one_div_le_one_div hq))
    have hmiddle := (hlower _).trans (hmid (u p) (u q))
    have hgap : c * ‖u p-u q‖^2 ≤ 1/((N : ℝ)+1) := by
      linarith only [hpQ, hqQ, hmiddle]
    have hsq : ‖u p-u q‖^2 ≤ (1/((N : ℝ)+1))/c := by
      apply (le_div_iff₀ hc).mpr
      simpa only [mul_comm] using hgap
    have hnonneg : 0 ≤ (1/((N : ℝ)+1))/c := by positivity
    rw [dist_eq_norm]
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hnonneg]
    exact hsq
  · have hroot : Tendsto (fun t : ℝ => Real.sqrt (t/c)) (𝓝 0) (𝓝 0) :=
      Continuous.tendsto' (by fun_prop) _ _ (by simp)
    exact hroot.comp tendsto_one_div_add_atTop_nhds_zero_nat

/-- Bounded-below continuous objectives with a positive quadratic midpoint gap
attain their infimum in a complete space. No coercivity-to-compactness inference
is used; completeness is applied to the explicitly controlled minimizing sequence. -/
theorem exists_minimizer_of_midpoint_gap [CompleteSpace E]
    {Q : E → ℝ} {c : ℝ} (hc : 0 < c) (hQ : Continuous Q)
    (hbdd : BddBelow (Set.range Q))
    (hmid : ∀ x y, Q ((1/2 : ℝ) • x + (1/2 : ℝ) • y) ≤
      (Q x + Q y)/2 - c * ‖x-y‖^2) :
    ∃ z, ∀ y, Q z ≤ Q y := by
  classical
  let m : ℝ := ⨅ x : E, Q x
  have hm : ∀ x, m ≤ Q x := fun x => ciInf_le hbdd x
  have hchoose : ∀ k : ℕ, ∃ x : E, Q x < m + 1/((k : ℝ)+1) := by
    intro k
    apply exists_lt_of_ciInf_lt
    change m < m + 1/((k : ℝ)+1)
    exact lt_add_of_le_of_pos le_rfl Nat.one_div_pos_of_nat
  choose u hu using hchoose
  have huc : CauchySeq u := cauchySeq_of_midpoint_gap hc hm hmid u
    (fun k => (hu k).le)
  obtain ⟨z, huz⟩ := cauchySeq_tendsto_of_complete huc
  have hmconst : Tendsto (fun _ : ℕ => m) atTop (𝓝 m) := tendsto_const_nhds
  have hupper : Tendsto (fun k : ℕ => m + 1/((k : ℝ)+1)) atTop (𝓝 m) := by
    simpa only [add_zero] using hmconst.add tendsto_one_div_add_atTop_nhds_zero_nat
  have hvalues : Tendsto (fun k => Q (u k)) atTop (𝓝 m) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hmconst hupper
      (fun k => hm (u k)) (fun k => (hu k).le)
  have hzvalue : Tendsto (fun k => Q (u k)) atTop (𝓝 (Q z)) :=
    (hQ.tendsto z).comp huz
  have heq : Q z = m := tendsto_nhds_unique hzvalue hvalues
  exact ⟨z, fun y => (le_of_eq heq).trans (hm y)⟩

end LeanPEP.ActualFunction.StrongMidpointMinimizer
