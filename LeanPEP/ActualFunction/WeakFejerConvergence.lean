import LeanPEP.ActualFunction.HilbertWeakTopology
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Bounded demiclosedness and weak Fejer convergence

The proof uses weak cluster FILTERS, not compactness-to-subsequence extraction.
Only the final existence theorem needs Hilbert completeness, via Riesz and
Banach-Alaoglu. Pairing limits never pass a nonlinear nonexpansive map through
a weak limit. Instead its residual is controlled by a scalar inequality.
This file is independent of PEP, convex objectives, and proximal algorithms.
-/

noncomputable section
open Filter Metric
open scoped Topology
namespace LeanPEP.ActualFunction.WeakFejerConvergence
open HilbertWeakTopology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The scalar defect estimate behind demiclosedness. It is valid pointwise;
no weak continuity of T is claimed. -/
theorem fixed_defect_bound {T : E → E}
    (hT : ∀ x y, ‖T x-T y‖ ≤ ‖x-y‖) (x z : E) {B : ℝ}
    (hB : ‖x-z‖ ≤ B) :
    ‖T z-z‖^2 ≤ 2*inner ℝ (x-z) (T z-z) +
      2*B*‖T x-x‖ + ‖T x-x‖^2 := by
  have htri := dist_triangle x (T x) (T z)
  simp only [dist_eq_norm, norm_sub_rev x (T x)] at htri
  have hnorm : ‖x-T z‖ ≤ ‖T x-x‖ + ‖x-z‖ :=
    htri.trans (add_le_add (le_refl _) (hT x z))
  have hsquare : ‖x-T z‖^2 ≤ (‖T x-x‖ + ‖x-z‖)^2 :=
    (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hnorm
  have heq : x-T z = (x-z)-(T z-z) := by abel
  rw [heq, norm_sub_sq_real] at hsquare
  have hprod : ‖T x-x‖*‖x-z‖ ≤ ‖T x-x‖*B :=
    mul_le_mul_of_nonneg_left hB (norm_nonneg _)
  nlinarith only [hsquare, hprod]

/-- Bounded demiclosedness at zero, for any nontrivial filter. Uniform boundedness
is an explicit premise here and is later supplied by the Fejer ball. -/
theorem fixed_of_inner_tendsto_of_residual {α : Type*} {l : Filter α} [l.NeBot]
    {T : E → E} {u : α → E} {z : E} {B : ℝ}
    (hT : ∀ x y, ‖T x-T y‖ ≤ ‖x-y‖)
    (hB : ∀ i, ‖u i-z‖ ≤ B)
    (hweak : ∀ v : E, Tendsto (fun i => inner ℝ (u i) v) l (𝓝 (inner ℝ z v)))
    (hres : Tendsto (fun i => ‖T (u i)-u i‖) l (𝓝 0)) : T z = z := by
  have hi : Tendsto (fun i => inner ℝ (u i-z) (T z-z)) l (𝓝 0) := by
    simpa only [inner_sub_left, sub_self] using
      (hweak (T z-z)).sub_const (inner ℝ z (T z-z))
  have hr : Tendsto (fun i => 2*inner ℝ (u i-z) (T z-z) +
      2*B*‖T (u i)-u i‖ + ‖T (u i)-u i‖^2) l (𝓝 0) := by
    simpa only [mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0)] using
      ((hi.const_mul 2).add (hres.const_mul (2*B))).add (hres.pow 2)
  have hz : ‖T z-z‖^2 ≤ 0 :=
    ge_of_tendsto' hr (fun i => fixed_defect_bound hT (u i) z (hB i))
  have hzero : ‖T z-z‖^2 = 0 := le_antisymm hz (sq_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hzero))

/-- Pairing convergence controls a DIFFERENCE of squared distances. It does
not imply convergence of either norm individually. -/
theorem distance_sq_difference (x z w : E) :
    ‖x-z‖^2-‖x-w‖^2 = 2*inner ℝ x (w-z) + (‖z‖^2-‖w‖^2) := by
  rw [norm_sub_sq_real x z, norm_sub_sq_real x w, inner_sub_right]
  ring

theorem distance_sq_difference_tendsto {α : Type*} {l : Filter α} {u : α → E} {a : E}
    (hweak : ∀ v : E, Tendsto (fun i => inner ℝ (u i) v) l (𝓝 (inner ℝ a v)))
    (z w : E) :
    Tendsto (fun i => ‖u i-z‖^2-‖u i-w‖^2) l (𝓝 (‖a-z‖^2-‖a-w‖^2)) := by
  have hfun : (fun i => ‖u i-z‖^2-‖u i-w‖^2) =
      (fun i => 2*inner ℝ (u i) (w-z) + (‖z‖^2-‖w‖^2)) := by
    funext i
    exact distance_sq_difference (u i) z w
  rw [hfun, distance_sq_difference a z w]
  exact ((hweak (w-z)).const_mul 2).add_const (‖z‖^2-‖w‖^2)

/-- Opial's uniqueness argument in a Hilbert space, expressed for two finer
filters. Both are required nontrivial and finer than atTop. -/
theorem inner_limits_eq_of_antitone {u : ℕ → E} {z w : E}
    {lz lw : Filter ℕ} [lz.NeBot] [lw.NeBot]
    (hlz : lz ≤ atTop) (hlw : lw ≤ atTop)
    (hz : ∀ v : E, Tendsto (fun n => inner ℝ (u n) v) lz (𝓝 (inner ℝ z v)))
    (hw : ∀ v : E, Tendsto (fun n => inner ℝ (u n) v) lw (𝓝 (inner ℝ w v)))
    (haz : Antitone (fun n => ‖u n-z‖))
    (haw : Antitone (fun n => ‖u n-w‖)) : z = w := by
  have hzb : BddBelow (Set.range (fun n => ‖u n-z‖)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact norm_nonneg _
  have hwb : BddBelow (Set.range (fun n => ‖u n-w‖)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact norm_nonneg _
  have hd := ((tendsto_atTop_ciInf haz hzb).pow 2).sub
    ((tendsto_atTop_ciInf haw hwb).pow 2)
  have hez := tendsto_nhds_unique (hd.mono_left hlz)
    (distance_sq_difference_tendsto hz z w)
  have hew := tendsto_nhds_unique (hd.mono_left hlw)
    (distance_sq_difference_tendsto hw z w)
  have he : ‖z-z‖^2-‖z-w‖^2 = ‖w-z‖^2-‖w-w‖^2 := hez.symm.trans hew
  simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
    zero_sub, sub_zero, norm_sub_rev w z] at he
  have hzero : ‖z-w‖^2 = 0 := by linarith only [he]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hzero))

/-- Every weak cluster point of a bounded asymptotically regular orbit is fixed.
The bound is centered at an arbitrary reference point, not the unknown limit. -/
theorem fixed_of_weakRiesz_cluster {T : E → E} {u : ℕ → E} {center z : E} {R : ℝ}
    (hT : ∀ x y, ‖T x-T y‖ ≤ ‖x-y‖)
    (hB : ∀ n, ‖u n-center‖ ≤ R)
    (hres : Tendsto (fun n => ‖T (u n)-u n‖) atTop (𝓝 0))
    (hz : MapClusterPt (weakRiesz z) atTop (fun n => weakRiesz (u n))) : T z = z := by
  obtain ⟨l, hne, hl, hw⟩ := inner_subfilter_of_weakRiesz_cluster hz
  letI : l.NeBot := hne
  have hb (n : ℕ) : ‖u n-z‖ ≤ R+‖center-z‖ := by
    have ht := dist_triangle (u n) center z
    simp only [dist_eq_norm] at ht
    exact ht.trans (add_le_add (hB n) (le_refl _))
  exact fixed_of_inner_tendsto_of_residual hT hb hw (hres.mono_left hl)

/-- Weak cluster uniqueness uses distances to BOTH limits, not only a single
reference minimizer. -/
theorem weakRiesz_clusters_eq {u : ℕ → E} {z w : E}
    (hz : MapClusterPt (weakRiesz z) atTop (fun n => weakRiesz (u n)))
    (hw : MapClusterPt (weakRiesz w) atTop (fun n => weakRiesz (u n)))
    (haz : Antitone (fun n => ‖u n-z‖))
    (haw : Antitone (fun n => ‖u n-w‖)) : z = w := by
  obtain ⟨lz, hnz, hlz, hpz⟩ := inner_subfilter_of_weakRiesz_cluster hz
  obtain ⟨lw, hnw, hlw, hpw⟩ := inner_subfilter_of_weakRiesz_cluster hw
  letI : lz.NeBot := hnz
  letI : lw.NeBot := hnw
  exact inner_limits_eq_of_antitone hlz hlw hpz hpw haz haw

/-- Weak convergence of a Fejer sequence for a nonexpansive map, assuming its
residual tends to zero and it has a fixed point. No finite-dimensionality,
separability, norm-compact orbit, or weak continuity of the map is required. -/
theorem exists_weak_tendsto_fixed [CompleteSpace E] {T : E → E} {u : ℕ → E}
    (hT : ∀ x y, ‖T x-T y‖ ≤ ‖x-y‖)
    (hres : Tendsto (fun n => ‖T (u n)-u n‖) atTop (𝓝 0))
    (hfejer : ∀ z, T z = z → Antitone (fun n => ‖u n-z‖))
    (p : E) (hp : T p = p) :
    ∃ z, T z = z ∧
      Tendsto (fun n => toWeakSpace ℝ E (u n)) atTop (𝓝 (toWeakSpace ℝ E z)) := by
  let K : Set (WeakDual ℝ E) := weakRiesz '' closedBall p ‖u 0-p‖
  have hK : IsCompact K := isCompact_weakRiesz_closedBall p ‖u 0-p‖
  have hB (n : ℕ) : ‖u n-p‖ ≤ ‖u 0-p‖ := hfejer p hp (Nat.zero_le n)
  have hmem (n : ℕ) : weakRiesz (u n) ∈ K :=
    ⟨u n, by simpa only [mem_closedBall, dist_eq_norm] using hB n, rfl⟩
  have hemem : ∀ᶠ n in atTop, weakRiesz (u n) ∈ K := Eventually.of_forall hmem
  have hmapmem : Filter.map (fun n => weakRiesz (u n)) atTop ≤ Filter.principal K :=
    Filter.le_principal_iff.mpr hemem
  obtain ⟨a, ha, hac⟩ := hK.exists_mapClusterPt hmapmem
  obtain ⟨z, _hzball, rfl⟩ := ha
  have hfixed : T z = z := fixed_of_weakRiesz_cluster hT hB hres hac
  have ht : Tendsto (fun n => weakRiesz (u n)) atTop (𝓝 (weakRiesz z)) := by
    apply hK.tendsto_nhds_of_unique_mapClusterPt hemem
    intro a ha hac'
    obtain ⟨w, _hwball, rfl⟩ := ha
    have hwfixed : T w = w := fixed_of_weakRiesz_cluster hT hB hres hac'
    have hwz : w = z := weakRiesz_clusters_eq hac' hac
      (hfejer w hwfixed) (hfejer z hfixed)
    exact congrArg weakRiesz hwz
  exact ⟨z, hfixed, weakSpace_tendsto_iff_inner.mpr
    (weakRiesz_tendsto_iff_inner.mp ht)⟩

/-- Norm and weak limits of the same sequence cannot disagree. This proves
compatibility of limits, not a converse from weak to strong convergence. -/
theorem eq_of_strong_and_weak_limits [CompleteSpace E] {u : ℕ → E} {z w : E}
    (hz : Tendsto u atTop (𝓝 z))
    (hw : Tendsto (fun n => toWeakSpace ℝ E (u n)) atTop (𝓝 (toWeakSpace ℝ E w))) :
    z = w := by
  have hzi := weakSpace_tendsto_iff_inner.mp (weakSpace_tendsto_of_tendsto hz)
  have hwi := weakSpace_tendsto_iff_inner.mp hw
  have hi := tendsto_nhds_unique (hzi (z-w)) (hwi (z-w))
  have hzero : ‖z-w‖^2 = 0 := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_left, hi, sub_self]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hzero))

end LeanPEP.ActualFunction.WeakFejerConvergence
