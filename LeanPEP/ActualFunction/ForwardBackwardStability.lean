import LeanPEP.ActualFunction.ProximalStability
import LeanPEP.ActualFunction.ParametricGDScaling

/-!
# Energy and stability of one actual forward-backward step

The normalized gradient is firm by adding the two ordered interpolation
inequalities already proved in the project. Its complement is firm as well.
Composition with the existing exact prox map gives the two-point energy
inequality with residual coefficient 1/2 (the usual 2/3-averaged estimate).
This is a structural estimate, not a new tight PEP rate or a new checker.
-/

noncomputable section
open scoped NNReal
namespace LeanPEP.ActualFunction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace IsOneSmoothConvexFirstOrder

/-- Cocoercivity is derived from both ordered interpolation inequalities. -/
theorem gradient_cocoercive {f : E → ℝ} {g : E → E}
    (hf : IsOneSmoothConvexFirstOrder f g) (x y : E) :
    ‖g x-g y‖^2 ≤ inner ℝ (g x-g y) (x-y) := by
  have hxy := pairwise_interpolation hf x y
  have hyx := pairwise_interpolation hf y x
  have hp : y-x = -(x-y) := by abel
  have hg : g y-g x = -(g x-g y) := by abel
  rw [hp, hg] at hyx
  simp only [inner_neg_left, inner_neg_right, neg_neg] at hyx
  rw [← real_inner_self_eq_norm_sq (g x-g y), inner_sub_left (g x) (g y) (x-y)]
  linarith only [hxy, hyx]

end IsOneSmoothConvexFirstOrder

namespace ProximalGradientCanonical
open ProximalScaling

/-- The physical forward step, using the unchanged gradient normalization. -/
def forwardStep (L : ℝ≥0) (g : E → E) (x : E) : E :=
  x-ParametricGDScaling.normalizedGradient L g x

/-- A name for the right-hand side of C6's recursion, not a second algorithm. -/
def forwardBackwardStep {L : ℝ≥0} {h : E → ℝ} (hp : HasProx L h)
    (g : E → E) (x : E) : E := proxMap hp (forwardStep L g x)

theorem iterate_succ_eq_step {L : ℝ≥0} {h : E → ℝ} (hp : HasProx L h)
    (g : E → E) (x0 : E) (k : ℕ) :
    iterate hp g x0 (k+1) = forwardBackwardStep hp g (iterate hp g x0 k) := rfl

/-- The 1/L forward map is firm. Positive L is used by normalization only. -/
theorem forwardStep_energy {L : ℝ≥0} {f : E → ℝ} {g : E → E}
    (hf : IsSmoothConvexFirstOrder L f g) (hL : 0 < (L : ℝ)) (x y : E) :
    ‖forwardStep L g x-forwardStep L g y‖^2 +
      ‖(x-y)-(forwardStep L g x-forwardStep L g y)‖^2 ≤ ‖x-y‖^2 := by
  let G := ParametricGDScaling.normalizedGradient L g
  have hc : ‖G x-G y‖^2 ≤ inner ℝ (G x-G y) (x-y) :=
    (ParametricGDScaling.normalizedFirstOrder hf hL).gradient_cocoercive x y
  have he := OperatorEnergy.firm_energy_of_inner hc
  have hforward : forwardStep L g x-forwardStep L g y = (x-y)-(G x-G y) := by
    dsimp [forwardStep, G]
    abel
  have hres : (x-y)-((x-y)-(G x-G y)) = G x-G y := by abel
  rw [hforward, hres]
  linarith only [he]

/-- The full step is nonexpansive with an explicit residual-square margin.
No minimizer, continuity of h, or finite dimension is needed here. -/
theorem forwardBackwardStep_energy {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) (x y : E) :
    ‖forwardBackwardStep hp g x-forwardBackwardStep hp g y‖^2 +
      (1/2 : ℝ)*‖(x-y)-(forwardBackwardStep hp g x-forwardBackwardStep hp g y)‖^2 ≤
        ‖x-y‖^2 :=
  OperatorEnergy.composition_energy (forwardStep_energy hf hL x y)
    (proxMap_energy hp hL hh (forwardStep L g x) (forwardStep L g y))

theorem forwardBackwardStep_norm_sub_le {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) (x y : E) :
    ‖forwardBackwardStep hp g x-forwardBackwardStep hp g y‖ ≤ ‖x-y‖ := by
  have he := forwardBackwardStep_energy hp hf hL hh x y
  have hn := sq_nonneg ‖(x-y)-(forwardBackwardStep hp g x-forwardBackwardStep hp g y)‖
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  linarith only [he, hn]

theorem forwardBackwardStep_lipschitz {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) :
    LipschitzWith 1 (forwardBackwardStep hp g) := by
  apply LipschitzWith.mk_one
  intro x y
  simpa only [dist_eq_norm] using forwardBackwardStep_norm_sub_le hp hf hL hh x y

/-- An additive gradient-oracle error is attenuated by the physical step 1/L.
This compares exact prox solves; it is not a statement about noisy function values. -/
theorem forwardBackwardStep_oracle_error {L : ℝ≥0} {h : E → ℝ} (hp : HasProx L h)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) (g : E → E) (x e : E) :
    ‖proxMap hp (x-(L : ℝ)⁻¹ • (g x+e))-forwardBackwardStep hp g x‖ ≤
      (L : ℝ)⁻¹*‖e‖ := by
  have hb := proxMap_norm_sub_le hp hL hh (x-(L : ℝ)⁻¹ • (g x+e)) (forwardStep L g x)
  have heq : (x-(L : ℝ)⁻¹ • (g x+e))-forwardStep L g x = -((L : ℝ)⁻¹ • e) := by
    simp only [forwardStep, ParametricGDScaling.normalizedGradient, smul_add]
    abel
  rw [heq, norm_neg, norm_smul, Real.norm_of_nonneg (le_of_lt (inv_pos.mpr hL))] at hb
  exact hb

/-- Ordinary composite minimizers are fixed points of this same step. -/
theorem forwardBackwardStep_fixed_of_minimizer {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) {xStar : E}
    (hmin : ∀ y, f xStar+h xStar ≤ f y+h y) : forwardBackwardStep hp g xStar = xStar :=
  proxMap_eq_of_isProxPoint hp hL hh
    ((Proximal.composite_minimizer_iff_prox_fixedPoint hf hh hL).mp hmin)

/-- Two-sided statement, including the absence of separate stationarity. -/
theorem forwardBackwardStep_fixed_iff_minimizer {L : ℝ≥0} {f h : E → ℝ} {g : E → E}
    (hp : HasProx L h) (hf : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) (x : E) :
    forwardBackwardStep hp g x = x ↔ ∀ y, f x+h x ≤ f y+h y := by
  constructor
  · intro hx
    apply (Proximal.composite_minimizer_iff_prox_fixedPoint hf hh hL).mpr
    have hs := proxMap_spec hp (forwardStep L g x)
    change IsProxPoint L h (forwardStep L g x) (forwardBackwardStep hp g x) at hs
    rw [hx] at hs
    exact hs
  · exact forwardBackwardStep_fixed_of_minimizer hp hf hL hh

end ProximalGradientCanonical
end LeanPEP.ActualFunction
