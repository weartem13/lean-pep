import LeanPEP.ActualFunction.ProximalIteration
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Stability of the existing exact proximal map

The supporting-hyperplane predicate is monotone even without a separate
convexity assumption. C5 optimality then gives firm nonexpansiveness for any
two actual prox solutions. C6's selected map and its unscaled residual inherit
1-Lipschitz continuity. No new selector, existence axiom, finite dimension,
completeness or continuity assumption on h is introduced.
-/

noncomputable section
open scoped NNReal
namespace LeanPEP.ActualFunction

namespace OperatorEnergy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Inner-product form of firmness implies its two-square energy form. -/
theorem firm_energy_of_inner {a b : E} (h : ‖a‖^2 ≤ inner ℝ a b) :
    ‖a‖^2 + ‖b-a‖^2 ≤ ‖b‖^2 := by
  rw [norm_sub_sq_real b a, real_inner_comm a b]
  linarith only [h]

/-- Composition of two firm energy inequalities loses at most a factor two
on the residual term. This is a purely Hilbert-space identity. -/
theorem composition_energy {a b c : E}
    (hab : ‖b‖^2 + ‖a-b‖^2 ≤ ‖a‖^2)
    (hbc : ‖c‖^2 + ‖b-c‖^2 ≤ ‖b‖^2) :
    ‖c‖^2 + (1/2 : ℝ)*‖a-c‖^2 ≤ ‖a‖^2 := by
  have hsq := sq_nonneg ‖(a-b)-(b-c)‖
  rw [norm_sub_sq_real (a-b) (b-c)] at hsq
  have hsum : ‖(a-b)+(b-c)‖^2 ≤ 2*‖a-b‖^2 + 2*‖b-c‖^2 := by
    rw [norm_add_sq_real (a-b) (b-c)]
    linarith only [hsq]
  have heq : (a-b)+(b-c) = a-c := by abel
  rw [heq] at hsum
  linarith only [hab, hbc, hsum]

end OperatorEnergy

namespace Proximal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Monotonicity follows from two actual global support inequalities. -/
theorem subgradient_pair_monotone {h : E → ℝ} {s t x y : E}
    (hs : SubgradientAt h s x) (ht : SubgradientAt h t y) :
    0 ≤ inner ℝ (s-t) (x-y) := by
  have hxy := hs y
  have hyx := ht x
  have heq : y-x = -(x-y) := by abel
  rw [heq, inner_neg_right] at hxy
  rw [inner_sub_left]
  linarith only [hxy, hyx]

end Proximal

namespace ProximalScaling
open Proximal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Firmness for supplied solutions; it does not assert that solutions exist. -/
theorem isProxPoint_firm {L : ℝ≥0} {h : E → ℝ} {v w p q : E}
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h)
    (hp : IsProxPoint L h v p) (hq : IsProxPoint L h w q) :
    ‖p-q‖^2 ≤ inner ℝ (p-q) (v-w) := by
  have hm := subgradient_pair_monotone
    (subgradient_of_isProxPoint hL hh hp) (subgradient_of_isProxPoint hL hh hq)
  rw [← smul_sub, real_inner_smul_left] at hm
  have hm' : (L : ℝ)*0 ≤ (L : ℝ)*inner ℝ ((v-p)-(w-q)) (p-q) := by
    simpa only [mul_zero] using hm
  have hi := le_of_mul_le_mul_left hm' hL
  have heq : (v-p)-(w-q) = (v-w)-(p-q) := by abel
  rw [heq, inner_sub_left (v-w) (p-q) (p-q), real_inner_self_eq_norm_sq (p-q),
    real_inner_comm (p-q) (v-w)] at hi
  linarith only [hi]

/-- Energy form retains both the output and residual differences. -/
theorem isProxPoint_energy {L : ℝ≥0} {h : E → ℝ} {v w p q : E}
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h)
    (hp : IsProxPoint L h v p) (hq : IsProxPoint L h w q) :
    ‖p-q‖^2 + ‖(v-w)-(p-q)‖^2 ≤ ‖v-w‖^2 :=
  OperatorEnergy.firm_energy_of_inner (isProxPoint_firm hL hh hp hq)

theorem proxMap_firm {L : ℝ≥0} {h : E → ℝ} (hp : HasProx L h)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) (v w : E) :
    ‖proxMap hp v-proxMap hp w‖^2 ≤ inner ℝ (proxMap hp v-proxMap hp w) (v-w) :=
  isProxPoint_firm hL hh (proxMap_spec hp v) (proxMap_spec hp w)

theorem proxMap_energy {L : ℝ≥0} {h : E → ℝ} (hp : HasProx L h)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) (v w : E) :
    ‖proxMap hp v-proxMap hp w‖^2 + ‖(v-w)-(proxMap hp v-proxMap hp w)‖^2 ≤ ‖v-w‖^2 :=
  isProxPoint_energy hL hh (proxMap_spec hp v) (proxMap_spec hp w)

theorem proxMap_norm_sub_le {L : ℝ≥0} {h : E → ℝ} (hp : HasProx L h)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) (v w : E) :
    ‖proxMap hp v-proxMap hp w‖ ≤ ‖v-w‖ := by
  have he := proxMap_energy hp hL hh v w
  have hn := sq_nonneg ‖(v-w)-(proxMap hp v-proxMap hp w)‖
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  linarith only [he, hn]

theorem proxMap_lipschitz {L : ℝ≥0} {h : E → ℝ} (hp : HasProx L h)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) : LipschitzWith 1 (proxMap hp) := by
  apply LipschitzWith.mk_one
  intro v w
  simpa only [dist_eq_norm] using proxMap_norm_sub_le hp hL hh v w

theorem proxMap_continuous {L : ℝ≥0} {h : E → ℝ} (hp : HasProx L h)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) : Continuous (proxMap hp) :=
  (proxMap_lipschitz hp hL hh).continuous

/-- The unscaled residual I-prox is 1-Lipschitz too. This is not the physical
subgradient residual L*(I-prox), whose Lipschitz constant is L. -/
theorem proxResidual_lipschitz {L : ℝ≥0} {h : E → ℝ} (hp : HasProx L h)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) :
    LipschitzWith 1 (fun v => v-proxMap hp v) := by
  apply LipschitzWith.mk_one
  intro v w
  rw [dist_eq_norm, dist_eq_norm]
  have he := proxMap_energy hp hL hh v w
  have hn := sq_nonneg ‖proxMap hp v-proxMap hp w‖
  have heq : (v-proxMap hp v)-(w-proxMap hp w) = (v-w)-(proxMap hp v-proxMap hp w) := by
    abel
  rw [heq]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  linarith only [he, hn]

end ProximalScaling
end LeanPEP.ActualFunction
