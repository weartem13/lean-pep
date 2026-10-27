import LeanPEP.ActualFunction.SummablePerturbation
import LeanPEP.ActualFunction.WeakFejerConvergence
import LeanPEP.ActualFunction.FejerConvergence
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Weak convergence with convergent distances and summable orbit errors

This extends C10 without changing its proofs. The same weak Riesz compact
balls, nontrivial cluster filters, distance-square difference and bounded
demiclosedness are reused. Monotonicity is replaced by existence of every
fixed-point distance limit; summable perturbations supply these limits.
No weak continuity of a nonlinear nonexpansive map is assumed.
-/

noncomputable section
open Filter Metric
open scoped Topology BigOperators
namespace LeanPEP.ActualFunction.WeakQuasiFejerConvergence
open HilbertWeakTopology WeakFejerConvergence SummablePerturbation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Opial uniqueness only needs distance limits, not exact Fejer monotonicity.
Both cluster filters must be nontrivial and retain all sequence tails. -/
theorem inner_limits_eq_of_distance_limits {u : ℕ → E} {z w : E}
    {lz lw : Filter ℕ} [lz.NeBot] [lw.NeBot]
    (hlz : lz ≤ atTop) (hlw : lw ≤ atTop)
    (hz : ∀ v : E, Tendsto (fun n => inner ℝ (u n) v) lz (𝓝 (inner ℝ z v)))
    (hw : ∀ v : E, Tendsto (fun n => inner ℝ (u n) v) lw (𝓝 (inner ℝ w v)))
    (hdz : ∃ d : ℝ, Tendsto (fun n => ‖u n-z‖) atTop (𝓝 d))
    (hdw : ∃ d : ℝ, Tendsto (fun n => ‖u n-w‖) atTop (𝓝 d)) : z = w := by
  obtain ⟨dz, hdz⟩ := hdz
  obtain ⟨dw, hdw⟩ := hdw
  have hd := (hdz.pow 2).sub (hdw.pow 2)
  have hez := tendsto_nhds_unique (hd.mono_left hlz)
    (distance_sq_difference_tendsto hz z w)
  have hew := tendsto_nhds_unique (hd.mono_left hlw)
    (distance_sq_difference_tendsto hw z w)
  have he : ‖z-z‖^2-‖z-w‖^2 = ‖w-z‖^2-‖w-w‖^2 := hez.symm.trans hew
  simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
    zero_sub, sub_zero, norm_sub_rev w z] at he
  have hzero : ‖z-w‖^2 = 0 := by linarith only [he]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hzero))

theorem clusters_eq_of_distance_limits {u : ℕ → E} {z w : E}
    (hz : MapClusterPt (weakRiesz z) atTop (fun n => weakRiesz (u n)))
    (hw : MapClusterPt (weakRiesz w) atTop (fun n => weakRiesz (u n)))
    (hdz : ∃ d : ℝ, Tendsto (fun n => ‖u n-z‖) atTop (𝓝 d))
    (hdw : ∃ d : ℝ, Tendsto (fun n => ‖u n-w‖) atTop (𝓝 d)) : z = w := by
  obtain ⟨lz, hnz, hlz, hpz⟩ := inner_subfilter_of_weakRiesz_cluster hz
  obtain ⟨lw, hnw, hlw, hpw⟩ := inner_subfilter_of_weakRiesz_cluster hw
  letI : lz.NeBot := hnz
  letI : lw.NeBot := hnw
  exact inner_limits_eq_of_distance_limits hlz hlw hpz hpw hdz hdw

/-- General weak convergence criterion, with uniform boundedness and existence
of every fixed-point distance limit explicit. No sequence extraction or
separability assumption is used in this Hilbert theorem. -/
theorem exists_weak_tendsto_fixed_of_distance_limits [CompleteSpace E]
    {T : E → E} {u : ℕ → E} {center : E} {R : ℝ}
    (hT : ∀ x y, ‖T x-T y‖ ≤ ‖x-y‖)
    (hB : ∀ n, ‖u n-center‖ ≤ R)
    (hres : Tendsto (fun n => ‖T (u n)-u n‖) atTop (𝓝 0))
    (hdist : ∀ z, T z = z → ∃ d : ℝ, Tendsto (fun n => ‖u n-z‖) atTop (𝓝 d)) :
    ∃ z, T z = z ∧
      Tendsto (fun n => toWeakSpace ℝ E (u n)) atTop (𝓝 (toWeakSpace ℝ E z)) := by
  let K : Set (WeakDual ℝ E) := weakRiesz '' closedBall center R
  have hK : IsCompact K := isCompact_weakRiesz_closedBall center R
  have hmem (n : ℕ) : weakRiesz (u n) ∈ K :=
    ⟨u n, by simpa only [mem_closedBall, dist_eq_norm] using hB n, rfl⟩
  have hemem : ∀ᶠ n in atTop, weakRiesz (u n) ∈ K := Eventually.of_forall hmem
  have hmapmem : Filter.map (fun n => weakRiesz (u n)) atTop ≤ Filter.principal K :=
    Filter.le_principal_iff.mpr hemem
  obtain ⟨a, ha, hac⟩ := hK.exists_mapClusterPt hmapmem
  obtain ⟨z, _hzball, rfl⟩ := ha
  have hz : T z = z := fixed_of_weakRiesz_cluster hT hB hres hac
  have ht : Tendsto (fun n => weakRiesz (u n)) atTop (𝓝 (weakRiesz z)) := by
    apply hK.tendsto_nhds_of_unique_mapClusterPt hemem
    intro a ha hac'
    obtain ⟨w, _hwball, rfl⟩ := ha
    have hw : T w = w := fixed_of_weakRiesz_cluster hT hB hres hac'
    have hwz : w = z := clusters_eq_of_distance_limits hac' hac (hdist w hw) (hdist z hz)
    exact congrArg weakRiesz hwz
  exact ⟨z, hz, weakSpace_tendsto_iff_inner.mpr (weakRiesz_tendsto_iff_inner.mp ht)⟩

/-- Summable norm errors preserve weak convergence for a nonexpansive map
with a positive fixed-point energy margin. The map and its fixed set are
unchanged. The limit need not equal the exact orbit's limit. -/
theorem inexact_weak_tendsto [CompleteSpace E]
    {T : E → E} {u : ℕ → E} {eps : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c) (hT : ∀ x y, ‖T x-T y‖ ≤ ‖x-y‖)
    (henergy : ∀ p, T p = p → ∀ x, ‖T x-p‖^2 + c*‖T x-x‖^2 ≤ ‖x-p‖^2)
    (p : E) (hp : T p = p) (hs : Summable eps)
    (herr : ∀ n, ‖u (n+1)-T (u n)‖ ≤ eps n) :
    ∃ z, T z = z ∧
      Tendsto (fun n => toWeakSpace ℝ E (u n)) atTop (𝓝 (toWeakSpace ℝ E z)) :=
  exists_weak_tendsto_fixed_of_distance_limits hT (distance_le_budget hT hs herr hp)
    (residual_tendsto_zero hc hT hp (henergy p hp) hs herr)
    (fun z hz => distance_has_limit hT hs herr hz)

/-- A compact norm orbit gives strong convergence once all fixed-point distance
limits exist. This is NOT an inference from weak to strong convergence. -/
theorem exists_strong_tendsto_fixed_of_compact
    {T : E → E} {u : ℕ → E}
    (hT : ∀ x y, ‖T x-T y‖ ≤ ‖x-y‖)
    (hres : Tendsto (fun n => ‖T (u n)-u n‖) atTop (𝓝 0))
    (hdist : ∀ z, T z = z → ∃ d : ℝ, Tendsto (fun n => ‖u n-z‖) atTop (𝓝 d))
    {K : Set E} (hK : IsCompact K) (hmem : ∀ n, u n ∈ K) :
    ∃ z ∈ K, T z = z ∧ Tendsto u atTop (𝓝 z) := by
  have hTc : Continuous T := (LipschitzWith.mk_one (fun x y => by
    simpa only [dist_eq_norm] using hT x y)).continuous
  have hres' : Tendsto (fun n => dist (T (u n)) (u n)) atTop (𝓝 0) := by
    simpa only [dist_eq_norm] using hres
  obtain ⟨z, hzK, φ, hφ, hsub⟩ := hK.tendsto_subseq hmem
  have hz : T z = z := FejerConvergence.fixed_of_subsequence_of_residual
    hTc hres' hφ.tendsto_atTop hsub
  obtain ⟨d, hd⟩ := hdist z hz
  have hzero : Tendsto (fun n => ‖u (φ n)-z‖) atTop (𝓝 0) := by
    have hsub' : Tendsto (fun n : ℕ => u (φ n)) atTop (𝓝 z) := hsub
    simpa only [sub_self, norm_zero] using (hsub'.sub_const z).norm
  have hd0 : d = 0 := tendsto_nhds_unique (hd.comp hφ.tendsto_atTop) hzero
  rw [hd0] at hd
  refine ⟨z, hzK, hz, ?_⟩
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hd ε hε
  refine ⟨N, ?_⟩
  intro n hn
  have ht := hN n hn
  simpa only [dist_eq_norm, sub_zero, norm_norm] using ht

/-- Finite dimension supplies norm compactness of the error-enlarged Fejer
ball. Summable errors still do not determine which fixed point is reached. -/
theorem inexact_strong_tendsto_finiteDimensional [FiniteDimensional ℝ E]
    {T : E → E} {u : ℕ → E} {eps : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c) (hT : ∀ x y, ‖T x-T y‖ ≤ ‖x-y‖)
    (henergy : ∀ p, T p = p → ∀ x, ‖T x-p‖^2 + c*‖T x-x‖^2 ≤ ‖x-p‖^2)
    (p : E) (hp : T p = p) (hs : Summable eps)
    (herr : ∀ n, ‖u (n+1)-T (u n)‖ ≤ eps n) :
    ∃ z, T z = z ∧ Tendsto u atTop (𝓝 z) := by
  have hB := distance_le_budget hT hs herr hp
  obtain ⟨z, _, hz, ht⟩ := exists_strong_tendsto_fixed_of_compact hT
    (residual_tendsto_zero hc hT hp (henergy p hp) hs herr)
    (fun z hz => distance_has_limit hT hs herr hz)
    (isCompact_closedBall p (‖u 0-p‖ + ∑' k, eps k))
    (fun n => by simpa only [mem_closedBall, dist_eq_norm] using hB n)
  exact ⟨z, hz, ht⟩

end LeanPEP.ActualFunction.WeakQuasiFejerConvergence
