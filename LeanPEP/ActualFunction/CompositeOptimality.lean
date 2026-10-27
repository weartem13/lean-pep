import LeanPEP.ActualFunction.ProximalScaling

/-!
# Composite minimizers and proximal fixed points

The nonsmooth component is real-valued and convex. A quadratic upper model
for the smooth component at the reference point suffices to extract the
supporting vector `-g xStar` from ordinary global minimality of `f+h`.
No subdifferential sum rule, finite-dimensionality, selected prox operator,
or existence of arbitrary proximal minimizers is assumed.

The proof reuses C1 unit proximal optimality and C4 positive normalization.
An auxiliary curvature `L+1` treats even `L=0` without division by zero; this
auxiliary number is not substituted for the step size of any actual run.
-/

noncomputable section
open scoped NNReal
namespace LeanPEP.ActualFunction

namespace ProximalScaling

open Proximal SmoothScaling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Necessity for a positive inverse proximal step size. -/
theorem subgradient_of_isProxPoint {L : ℝ≥0} {h : E → ℝ} {v x : E}
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h)
    (hp : IsProxPoint L h v x) :
    SubgradientAt h ((L : ℝ) • (v-x)) x := by
  have hconv := normalizedFunction_convex (0 : E) hL (by norm_num : (0 : ℝ) < 1) hh
  have hprox : IsUnitProxPoint (normalizedFunction h (0 : E) L 1) v x := by
    apply (normalized_prox_iff hL (by norm_num : (0 : ℝ) < 1) h (0 : E) v x).mp
    simpa only [scaledPoint, one_smul, zero_add] using hp
  have hs := subgradient_of_isUnitProxPoint hconv hprox
  intro y
  have hi := hs y
  simp only [normalizedFunction, scaledPoint, one_smul, zero_add, one_pow, mul_one] at hi
  have hdiv : (h x + (L : ℝ)*inner ℝ (v-x) (y-x) - h 0)/(L : ℝ) ≤
      (h y-h 0)/(L : ℝ) := by
    calc
      (h x + (L : ℝ)*inner ℝ (v-x) (y-x) - h 0)/(L : ℝ) =
          (h x-h 0)/(L : ℝ) + inner ℝ (v-x) (y-x) := by
        field_simp [ne_of_gt hL] <;> ring
      _ ≤ (h y-h 0)/(L : ℝ) := hi
  have hclear := (div_le_div_iff_of_pos_right hL).mp hdiv
  simp only [real_inner_smul_left]
  linarith only [hclear]

/-- Full optimality equivalence for the existing physical prox definition. -/
theorem isProxPoint_iff_subgradient {L : ℝ≥0} {h : E → ℝ} {v x : E}
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h) :
    IsProxPoint L h v x ↔ SubgradientAt h ((L : ℝ) • (v-x)) x :=
  ⟨subgradient_of_isProxPoint hL hh, isProxPoint_of_subgradient⟩

/-- Uniqueness of supplied prox minimizers; this does not assert existence. -/
theorem isProxPoint_unique {L : ℝ≥0} {h : E → ℝ} {v x y : E}
    (hL : 0 < (L : ℝ)) (hh : ConvexOn ℝ Set.univ h)
    (hx : IsProxPoint L h v x) (hy : IsProxPoint L h v y) : y = x :=
  eq_of_subgradient_of_isProxPoint hL (subgradient_of_isProxPoint hL hh hx) hy

end ProximalScaling

namespace Proximal

open ProximalScaling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Residual at a fixed point of a forward/prox step; no stationarity is assumed. -/
theorem scaled_forward_residual {K : ℝ≥0} (hK : 0 < (K : ℝ)) (x a : E) :
    (K : ℝ) • ((x - (K : ℝ)⁻¹ • a)-x) = -a := by
  have hv : (x - (K : ℝ)⁻¹ • a)-x = -((K : ℝ)⁻¹ • a) := by abel
  rw [hv, smul_neg, smul_smul, mul_inv_cancel₀ (ne_of_gt hK), one_smul]

/-- A quadratic support inequality produces an actual prox fixed point.
The smooth component need not be defined: only the vector `a` is used. -/
theorem prox_fixedPoint_of_quadratic_support {K : ℝ≥0} {h : E → ℝ} {x a : E}
    (hK : 0 < (K : ℝ))
    (hmodel : ∀ y, h x ≤ h y + inner ℝ a (y-x) +
      ((K : ℝ)/2)*inner ℝ (y-x) (y-x)) :
    IsProxPoint K h (x - (K : ℝ)⁻¹ • a) x := by
  let v : E := x - (K : ℝ)⁻¹ • a
  have hres : (K : ℝ) • (v-x) = -a := scaled_forward_residual hK x a
  intro y
  have hinner : (K : ℝ)*inner ℝ (v-x) (y-x) = -inner ℝ a (y-x) := by
    rw [← real_inner_smul_left, hres, inner_neg_left]
  have hquad : ((K : ℝ)/2)*inner ℝ (y-v) (y-v) -
      ((K : ℝ)/2)*inner ℝ (x-v) (x-v) =
      inner ℝ a (y-x) + ((K : ℝ)/2)*inner ℝ (y-x) (y-x) := by
    calc
      ((K : ℝ)/2)*inner ℝ (y-v) (y-v) -
          ((K : ℝ)/2)*inner ℝ (x-v) (x-v) =
        (K : ℝ)*((1/2 : ℝ)*inner ℝ (y-v) (y-v) -
          (1/2 : ℝ)*inner ℝ (x-v) (x-v) + inner ℝ (v-x) (y-x)) -
          (K : ℝ)*inner ℝ (v-x) (y-x) := by ring
      _ = (K : ℝ)*((1/2 : ℝ)*inner ℝ (y-x) (y-x)) -
          (K : ℝ)*inner ℝ (v-x) (y-x) := by rw [quadratic_remainder]
      _ = inner ℝ a (y-x) + ((K : ℝ)/2)*inner ℝ (y-x) (y-x) := by
        rw [hinner]
        ring
  change h x + ((K : ℝ)/2)*inner ℝ (x-v) (x-v) ≤
    h y + ((K : ℝ)/2)*inner ℝ (y-v) (y-v)
  calc
    h x + ((K : ℝ)/2)*inner ℝ (x-v) (x-v) ≤
        (h y + inner ℝ a (y-x) + ((K : ℝ)/2)*inner ℝ (y-x) (y-x)) +
          ((K : ℝ)/2)*inner ℝ (x-v) (x-v) := add_le_add (hmodel y) (le_refl _)
    _ = h y + ((K : ℝ)/2)*inner ℝ (y-v) (y-v) := by linarith only [hquad]

/-- Convexity converts quadratic support into exact linear support. -/
theorem subgradient_of_quadratic_support {K : ℝ≥0} {h : E → ℝ} {x a : E}
    (hK : 0 < (K : ℝ)) (hh : ConvexOn ℝ Set.univ h)
    (hmodel : ∀ y, h x ≤ h y + inner ℝ a (y-x) +
      ((K : ℝ)/2)*inner ℝ (y-x) (y-x)) : SubgradientAt h (-a) x := by
  have hs := ProximalScaling.subgradient_of_isProxPoint hK hh
    (prox_fixedPoint_of_quadratic_support hK hmodel)
  rw [scaled_forward_residual hK x a] at hs
  exact hs

/-- Only a smooth upper model at the minimizer is needed for necessity.
The auxiliary positive coefficient L+1 allows a zero smoothness bound. -/
theorem subgradient_of_minimizer_of_upperModel {L : ℝ≥0}
    {f h : E → ℝ} {x a : E}
    (hupper : ∀ y, f y ≤ f x + inner ℝ a (y-x) +
      ((L : ℝ)/2)*inner ℝ (y-x) (y-x))
    (hh : ConvexOn ℝ Set.univ h)
    (hmin : ∀ y, f x + h x ≤ f y + h y) : SubgradientAt h (-a) x := by
  let K : ℝ≥0 := L + 1
  have hK : 0 < (K : ℝ) := by
    change 0 < (L : ℝ) + 1
    positivity
  apply subgradient_of_quadratic_support (K := K) hK hh
  intro y
  have hcoeff : (L : ℝ)/2 ≤ (K : ℝ)/2 := by
    change (L : ℝ)/2 ≤ ((L : ℝ)+1)/2
    linarith
  have hraise := mul_le_mul_of_nonneg_right hcoeff
    (real_inner_self_nonneg (x := y-x))
  have hm := hmin y
  have hu := hupper y
  linarith only [hm, hu, hraise]

/-- Global minimality supplies the original composite stationarity certificate. -/
theorem subgradient_of_composite_minimizer {L : ℝ≥0}
    {f h : E → ℝ} {g : E → E} {xStar : E}
    (hf : IsSmoothConvexFirstOrder L f g) (hh : ConvexOn ℝ Set.univ h)
    (hmin : ∀ y, f xStar + h xStar ≤ f y + h y) :
    SubgradientAt h (-g xStar) xStar :=
  subgradient_of_minimizer_of_upperModel (hf.upperModel xStar) hh hmin

/-- Sufficiency uses supporting models of the two components, with cancellation. -/
theorem composite_minimizer_of_subgradient {L : ℝ≥0}
    {f h : E → ℝ} {g : E → E} {xStar : E}
    (hf : IsSmoothConvexFirstOrder L f g)
    (hs : SubgradientAt h (-g xStar) xStar) (y : E) :
    f xStar + h xStar ≤ f y + h y := by
  have hfLower := hf.lowerModel xStar y
  have hhLower := hs y
  simp only [inner_neg_left] at hhLower
  linarith only [hfLower, hhLower]

/-- No positive L or complete-space assumption is needed for this equivalence. -/
theorem composite_minimizer_iff_subgradient {L : ℝ≥0}
    {f h : E → ℝ} {g : E → E} {xStar : E}
    (hf : IsSmoothConvexFirstOrder L f g) (hh : ConvexOn ℝ Set.univ h) :
    (∀ y, f xStar + h xStar ≤ f y + h y) ↔ SubgradientAt h (-g xStar) xStar :=
  ⟨subgradient_of_composite_minimizer hf hh, composite_minimizer_of_subgradient hf⟩

/-- Positive-step proximal fixed points are precisely global composite minimizers. -/
theorem composite_minimizer_iff_prox_fixedPoint {L : ℝ≥0}
    {f h : E → ℝ} {g : E → E} {xStar : E}
    (hf : IsSmoothConvexFirstOrder L f g) (hh : ConvexOn ℝ Set.univ h)
    (hL : 0 < (L : ℝ)) :
    (∀ y, f xStar + h xStar ≤ f y + h y) ↔
      IsProxPoint L h (xStar - (L : ℝ)⁻¹ • g xStar) xStar := by
  rw [ProximalScaling.isProxPoint_iff_subgradient hL hh,
    scaled_forward_residual hL xStar (g xStar)]
  exact composite_minimizer_iff_subgradient hf hh

/-- Analysis-facing version of the minimizer characterization. -/
theorem composite_minimizer_iff_subgradient_analytic [CompleteSpace E] {L : ℝ≥0}
    {f h : E → ℝ} {g : E → E} {xStar : E}
    (hf : IsSmoothConvexAnalytic L f g) (hh : ConvexOn ℝ Set.univ h) :
    (∀ y, f xStar + h xStar ≤ f y + h y) ↔ SubgradientAt h (-g xStar) xStar :=
  composite_minimizer_iff_subgradient hf.toFirstOrder hh

end Proximal
end LeanPEP.ActualFunction
