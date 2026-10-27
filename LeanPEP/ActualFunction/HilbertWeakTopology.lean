import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ClusterPt
import Mathlib.Tactic

/-!
# Hilbert weak convergence and compactness, using mathlib's topologies

No topology instance on E is replaced. Public weak limits use `toWeakSpace`.
The map to `WeakDual` is only a Riesz representation device: testing it at v
is exactly the original inner product with v. Completeness is used for Riesz
surjectivity and compactness, not for the elementary pairing statements.
Compactness is NOT sequential compactness and does not assume separability.
-/

noncomputable section
open Filter Metric
open scoped Topology
namespace LeanPEP.ActualFunction.HilbertWeakTopology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Riesz embedding, with the target carrying the weak-star topology. -/
def weakRiesz (x : E) : WeakDual ℝ E :=
  StrongDual.toWeakDual (InnerProductSpace.toDualMap ℝ E x)

@[simp] theorem weakRiesz_apply (x v : E) : weakRiesz x v = inner ℝ x v := rfl

theorem weakRiesz_injective : Function.Injective (weakRiesz (E := E)) := by
  intro x y hxy
  have h := congrArg (fun a : WeakDual ℝ E => a (x-y)) hxy
  change inner ℝ x (x-y) = inner ℝ y (x-y) at h
  have hz : ‖x-y‖^2 = 0 := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_left, h, sub_self]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

/-- Convergence in the existing weak-star topology is pointwise pairing
convergence. No norm-continuity of an unrelated nonlinear map is used. -/
theorem weakRiesz_tendsto_iff_inner {α : Type*} {l : Filter α} {u : α → E} {z : E} :
    Tendsto (fun i => weakRiesz (u i)) l (𝓝 (weakRiesz z)) ↔
      ∀ v : E, Tendsto (fun i => inner ℝ (u i) v) l (𝓝 (inner ℝ z v)) := by
  constructor
  · intro ht v
    exact ((WeakDual.eval_continuous v).tendsto (weakRiesz z)).comp ht
  · intro ht
    apply tendsto_iff_forall_eval_tendsto_topDualPairing.mpr
    intro v
    exact ht v

/-- Continuous linear functionals separate points of a real inner product space. -/
theorem dualPairing_injective : Function.Injective (topDualPairing ℝ E).flip := by
  intro x y hxy
  have h := congrArg (fun a : StrongDual ℝ E →ₗ[ℝ] ℝ =>
    a (InnerProductSpace.toDualMap ℝ E (x-y))) hxy
  change inner ℝ (x-y) x = inner ℝ (x-y) y at h
  have hz : ‖x-y‖^2 = 0 := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_right, h, sub_self]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

/-- Public weak convergence is mathlib's WeakSpace convergence, not convergence
in a replacement norm topology. -/
theorem weakSpace_tendsto_iff_dual {α : Type*} {l : Filter α} {u : α → E} {z : E} :
    Tendsto (fun i => toWeakSpace ℝ E (u i)) l (𝓝 (toWeakSpace ℝ E z)) ↔
      ∀ a : StrongDual ℝ E, Tendsto (fun i => a (u i)) l (𝓝 (a z)) := by
  exact WeakBilin.tendsto_iff_forall_eval_tendsto
    (topDualPairing ℝ E).flip dualPairing_injective

/-- Riesz representation identifies testing all inner products with testing
all continuous linear functionals. Completeness is explicit here. -/
theorem weakSpace_tendsto_iff_inner [CompleteSpace E]
    {α : Type*} {l : Filter α} {u : α → E} {z : E} :
    Tendsto (fun i => toWeakSpace ℝ E (u i)) l (𝓝 (toWeakSpace ℝ E z)) ↔
      ∀ v : E, Tendsto (fun i => inner ℝ (u i) v) l (𝓝 (inner ℝ z v)) := by
  rw [weakSpace_tendsto_iff_dual]
  constructor
  · intro ht v
    simpa only [InnerProductSpace.toDualMap_apply_apply, real_inner_comm v]
      using ht (InnerProductSpace.toDualMap ℝ E v)
  · intro ht a
    obtain ⟨v, rfl⟩ := (InnerProductSpace.toDual ℝ E).surjective a
    simpa only [InnerProductSpace.toDual_apply_apply, real_inner_comm v] using ht v

/-- Norm convergence implies convergence in the existing weak topology. -/
theorem weakSpace_tendsto_of_tendsto {α : Type*} {l : Filter α} {u : α → E} {z : E}
    (hu : Tendsto u l (𝓝 z)) :
    Tendsto (fun i => toWeakSpace ℝ E (u i)) l (𝓝 (toWeakSpace ℝ E z)) :=
  ((toWeakSpaceCLM ℝ E).continuous.tendsto z).comp hu

/-- Hilbert completeness makes the Riesz embedding onto the entire weak dual. -/
theorem weakRiesz_surjective [CompleteSpace E] :
    Function.Surjective (weakRiesz (E := E)) := by
  intro a
  refine ⟨(InnerProductSpace.toDual ℝ E).symm (WeakDual.toStrongDual a), ?_⟩
  apply (WeakDual.toStrongDual : WeakDual ℝ E ≃ₗ[ℝ] StrongDual ℝ E).injective
  change InnerProductSpace.toDual ℝ E
    ((InnerProductSpace.toDual ℝ E).symm (WeakDual.toStrongDual a)) = _
  exact (InnerProductSpace.toDual ℝ E).apply_symm_apply _

/-- Exact identification of the represented norm ball. No weak norm-continuity
is asserted; this is an equality of sets through an isometric representation. -/
theorem weakRiesz_closedBall_image [CompleteSpace E] (center : E) (R : ℝ) :
    weakRiesz '' closedBall center R =
      WeakDual.toStrongDual ⁻¹' closedBall (InnerProductSpace.toDual ℝ E center) R := by
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    change dist (InnerProductSpace.toDual ℝ E x)
      (InnerProductSpace.toDual ℝ E center) ≤ R
    rw [(InnerProductSpace.toDual ℝ E).dist_map]
    exact hx
  · intro ha
    obtain ⟨x, rfl⟩ := weakRiesz_surjective a
    refine ⟨x, ?_, rfl⟩
    change dist (InnerProductSpace.toDual ℝ E x)
      (InnerProductSpace.toDual ℝ E center) ≤ R at ha
    rw [(InnerProductSpace.toDual ℝ E).dist_map] at ha
    exact ha

/-- Banach-Alaoglu plus Riesz gives the required weak compactness, with neither
finite dimension nor separability. This is not norm compactness. -/
theorem isCompact_weakRiesz_closedBall [CompleteSpace E] (center : E) (R : ℝ) :
    IsCompact (weakRiesz '' closedBall center R) := by
  rw [weakRiesz_closedBall_image]
  exact WeakDual.isCompact_closedBall (InnerProductSpace.toDual ℝ E center) R

/-- A map cluster point supplies a nontrivial finer filter on the same index
type. This avoids any false extraction of a subsequence from mere compactness. -/
theorem inner_subfilter_of_weakRiesz_cluster {u : ℕ → E} {z : E}
    (hz : MapClusterPt (weakRiesz z) atTop (fun n => weakRiesz (u n))) :
    ∃ l : Filter ℕ, l.NeBot ∧ l ≤ atTop ∧
      ∀ v : E, Tendsto (fun n => inner ℝ (u n) v) l (𝓝 (inner ℝ z v)) := by
  let l : Filter ℕ := comap (fun n => weakRiesz (u n)) (𝓝 (weakRiesz z)) ⊓ atTop
  have hne : l.NeBot := Filter.neBot_inf_comap_iff_map'.mpr hz
  have ht : Tendsto (fun n => weakRiesz (u n)) l (𝓝 (weakRiesz z)) :=
    tendsto_comap.mono_left inf_le_left
  exact ⟨l, hne, inf_le_right, weakRiesz_tendsto_iff_inner.mp ht⟩

end LeanPEP.ActualFunction.HilbertWeakTopology
