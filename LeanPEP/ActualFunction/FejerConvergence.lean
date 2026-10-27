import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic

/-!
# From a convergent subsequence to convergence of a Fejer sequence

This is a metric-space lemma layer, independent of optimization, Gram data,
proximal maps, and finite dimension. A norm-convergent subsequence and vanishing
fixed-point residual identify a fixed point of a continuous map. If distances
to every fixed point are antitone, convergence of the whole sequence follows.
Compactness is an explicit hypothesis in the existence corollary, not an
assumption silently inferred from boundedness in an arbitrary Hilbert space.
-/

open Filter
open scoped Topology
namespace LeanPEP.ActualFunction.FejerConvergence

variable {X : Type*} [MetricSpace X]

/-- One subsequence approaching z suffices when the full distance to z is
antitone. Cofinality is not needed for this particular implication. -/
theorem tendsto_of_antitone_dist_of_subsequence {u : ℕ → X} {z : X} {φ : ℕ → ℕ}
    (hanti : Antitone (fun n => dist (u n) z))
    (hsub : Tendsto (u ∘ φ) atTop (𝓝 z)) : Tendsto u atTop (𝓝 z) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hsub ε hε
  refine ⟨φ K, ?_⟩
  intro n hn
  exact (hanti hn).trans_lt (hK K (le_refl K))

/-- A cluster limit is fixed if the map is continuous and the residual tends
to zero. Cofinality is required here to inherit the residual limit. -/
theorem fixed_of_subsequence_of_residual {T : X → X} {u : ℕ → X}
    (hT : Continuous T)
    (hres : Tendsto (fun n => dist (T (u n)) (u n)) atTop (𝓝 0))
    {z : X} {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    (hsub : Tendsto (u ∘ φ) atTop (𝓝 z)) : T z = z := by
  have hlim : Tendsto (fun k => dist (T (u (φ k))) (u (φ k)))
      atTop (𝓝 (dist (T z) z)) :=
    ((hT.tendsto z).comp hsub).dist hsub
  have hzero : Tendsto (fun k => dist (T (u (φ k))) (u (φ k)))
      atTop (𝓝 0) := hres.comp hφ
  exact dist_eq_zero.mp (tendsto_nhds_unique hlim hzero)

/-- Conditional strong convergence: compactness and finite dimension are not
needed once a cofinal convergent subsequence has been supplied. -/
theorem tendsto_fixed_of_subsequence {T : X → X} {u : ℕ → X}
    (hT : Continuous T)
    (hres : Tendsto (fun n => dist (T (u n)) (u n)) atTop (𝓝 0))
    (hfejer : ∀ z, T z = z → Antitone (fun n => dist (u n) z))
    {z : X} {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    (hsub : Tendsto (u ∘ φ) atTop (𝓝 z)) :
    T z = z ∧ Tendsto u atTop (𝓝 z) := by
  have hfixed := fixed_of_subsequence_of_residual hT hres hφ hsub
  exact ⟨hfixed, tendsto_of_antitone_dist_of_subsequence (hfejer z hfixed) hsub⟩

/-- Compact orbit containment supplies the only missing subsequence. -/
theorem exists_tendsto_fixed_of_compact {T : X → X} {u : ℕ → X}
    (hT : Continuous T)
    (hres : Tendsto (fun n => dist (T (u n)) (u n)) atTop (𝓝 0))
    (hfejer : ∀ z, T z = z → Antitone (fun n => dist (u n) z))
    {K : Set X} (hK : IsCompact K) (hu : ∀ n, u n ∈ K) :
    ∃ z ∈ K, T z = z ∧ Tendsto u atTop (𝓝 z) := by
  obtain ⟨z, hz, φ, hφ, hsub⟩ := hK.tendsto_subseq hu
  exact ⟨z, hz, tendsto_fixed_of_subsequence hT hres hfejer hφ.tendsto_atTop hsub⟩

end LeanPEP.ActualFunction.FejerConvergence
