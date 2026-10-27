import LeanPEP.ActualFunction.Proximal
import LeanPEP.ActualFunction.SmoothScalingCore

/-!
# Exact scaling of real-valued proximal minimization

`IsProxPoint L h v x` means minimization of h(z) + (L/2)||z-v||^2.
Thus the proximal step size is 1/L, not L. The coordinate transformation
uses the existing SmoothScaling function/point definitions. Positive L and
positive radius are required for normalization; zero radius is handled by
strict quadratic remainder and uniqueness, never by division by zero.
No selected prox map, existence theorem, or extended-real domain is assumed.
-/

noncomputable section
open scoped NNReal
namespace LeanPEP.ActualFunction.ProximalScaling

open Proximal SmoothScaling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Ordinary proximal minimization, with inverse step size L. -/
def IsProxPoint (L : ℝ≥0) (h : E → ℝ) (v x : E) : Prop :=
  ∀ y, h x + ((L : ℝ)/2) * inner ℝ (x-v) (x-v) ≤
    h y + ((L : ℝ)/2) * inner ℝ (y-v) (y-v)

theorem isProxPoint_iff_norm (L : ℝ≥0) (h : E → ℝ) (v x : E) :
    IsProxPoint L h v x ↔ ∀ y,
      h x + ((L : ℝ)/2) * ‖x-v‖^2 ≤ h y + ((L : ℝ)/2) * ‖y-v‖^2 := by
  simp only [IsProxPoint, real_inner_self_eq_norm_sq]

@[simp] theorem isProxPoint_one (h : E → ℝ) (v x : E) :
    IsProxPoint 1 h v x ↔ IsUnitProxPoint h v x := by
  simp only [IsProxPoint, IsUnitProxPoint, NNReal.coe_one]

/-- Inverse affine coordinates; only nonzero-radius lemmas use the inverse. -/
def normalizedPoint (center : E) (R : ℝ) (x : E) : E := R⁻¹ • (x-center)

@[simp] theorem scaled_normalizedPoint (center x : E) {R : ℝ} (hR : R ≠ 0) :
    scaledPoint center R (normalizedPoint center R x) = x := by
  simp only [scaledPoint, normalizedPoint, smul_smul, mul_inv_cancel₀ hR, one_smul]
  abel

@[simp] theorem normalized_scaledPoint (center z : E) {R : ℝ} (hR : R ≠ 0) :
    normalizedPoint center R (scaledPoint center R z) = z := by
  have hd : center + R • z - center = R • z := by abel
  simp only [normalizedPoint, scaledPoint, hd, smul_smul, inv_mul_cancel₀ hR, one_smul]

theorem scaledPoint_sub (center : E) (R : ℝ) (x y : E) :
    scaledPoint center R y - scaledPoint center R x = R • (y-x) := by
  simp only [scaledPoint, smul_sub]
  abel

theorem scaledPoint_combination (center : E) (R a b : ℝ) (x y : E) (hab : a+b=1) :
    scaledPoint center R (a • x + b • y) =
      a • scaledPoint center R x + b • scaledPoint center R y := by
  have hc : a • center + b • center = center := by
    rw [← add_smul, hab, one_smul]
  simp only [scaledPoint, smul_add, smul_smul]
  calc
    center + ((R*a) • x + (R*b) • y) =
        (a • center + b • center) + ((R*a) • x + (R*b) • y) := by rw [hc]
    _ = a • center + (a*R) • x + (b • center + (b*R) • y) := by
      rw [mul_comm R a, mul_comm R b]
      abel

/-- The same positive value/space normalization works for a nonsmooth component. -/
theorem normalizedFunction_convex {L : ℝ≥0} {R : ℝ} {h : E → ℝ} (center : E)
    (hL : 0 < (L : ℝ)) (hR : 0 < R) (hh : ConvexOn ℝ Set.univ h) :
    ConvexOn ℝ Set.univ (normalizedFunction h center L R) := by
  have hA : 0 < (L : ℝ)*R^2 := by positivity
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hc := hh.2 (show scaledPoint center R x ∈ Set.univ from trivial)
    (show scaledPoint center R y ∈ Set.univ from trivial) ha hb hab
  simp only [smul_eq_mul] at hc
  have hcenter : a * h center + b * h center = h center := by
    rw [← add_mul, hab, one_mul]
  change (h (scaledPoint center R (a • x + b • y)) - h center) / ((L : ℝ)*R^2) ≤
    a * ((h (scaledPoint center R x)-h center)/((L : ℝ)*R^2)) +
    b * ((h (scaledPoint center R y)-h center)/((L : ℝ)*R^2))
  rw [scaledPoint_combination center R a b x y hab]
  calc
    (h (a • scaledPoint center R x + b • scaledPoint center R y)-h center) /
        ((L : ℝ)*R^2) ≤
      (a*(h (scaledPoint center R x)-h center) +
        b*(h (scaledPoint center R y)-h center))/((L : ℝ)*R^2) := by
          apply (div_le_div_iff_of_pos_right hA).2
          nlinarith
    _ = _ := by ring

/-- Supporting covectors normalize by 1/(LR), not by 1/(LR^2). -/
theorem normalized_subgradient {L : ℝ≥0} {R : ℝ} {h : E → ℝ}
    (center : E) (hL : 0 < (L : ℝ)) (hR : 0 < R) {s z : E}
    (hs : SubgradientAt h s (scaledPoint center R z)) :
    SubgradientAt (normalizedFunction h center L R) ((1/((L : ℝ)*R)) • s) z := by
  intro y
  have hA : 0 < (L : ℝ)*R^2 := by positivity
  have heq : normalizedFunction h center L R z +
        inner ℝ ((1/((L : ℝ)*R)) • s) (y-z) =
      (h (scaledPoint center R z)-h center +
        inner ℝ s (scaledPoint center R y-scaledPoint center R z))/((L : ℝ)*R^2) := by
    simp only [normalizedFunction, scaledPoint_sub, real_inner_smul_left,
      real_inner_smul_right]
    field_simp [ne_of_gt hL, ne_of_gt hR] <;> ring
  rw [heq]
  change _ ≤ (h (scaledPoint center R y)-h center)/((L : ℝ)*R^2)
  apply (div_le_div_iff_of_pos_right hA).2
  linarith [hs (scaledPoint center R y)]

/-- Exact objective identity for the whole proximal subproblem. -/
theorem normalized_prox_objective {L : ℝ≥0} {R : ℝ}
    (hL : 0 < (L : ℝ)) (hR : 0 < R) (h : E → ℝ) (center v z : E) :
    normalizedFunction h center L R z + (1/2 : ℝ)*inner ℝ (z-v) (z-v) =
      (h (scaledPoint center R z) + ((L : ℝ)/2)*
        inner ℝ (scaledPoint center R z-scaledPoint center R v)
          (scaledPoint center R z-scaledPoint center R v) - h center)/((L : ℝ)*R^2) := by
  simp only [normalizedFunction, scaledPoint_sub, real_inner_smul_left,
    real_inner_smul_right]
  field_simp [ne_of_gt hL, ne_of_gt hR] <;> ring

/-- Full equivalence of actual minimizers. The reverse direction uses the
surjectivity of the affine change of variables, not just sampled points. -/
theorem normalized_prox_iff {L : ℝ≥0} {R : ℝ}
    (hL : 0 < (L : ℝ)) (hR : 0 < R) (h : E → ℝ) (center v z : E) :
    IsProxPoint L h (scaledPoint center R v) (scaledPoint center R z) ↔
      IsUnitProxPoint (normalizedFunction h center L R) v z := by
  have hA : 0 < (L : ℝ)*R^2 := by positivity
  constructor
  · intro hp y
    rw [normalized_prox_objective hL hR, normalized_prox_objective hL hR]
    apply (div_le_div_iff_of_pos_right hA).2
    exact sub_le_sub_right (hp (scaledPoint center R y)) (h center)
  · intro hp y
    have hi := hp (normalizedPoint center R y)
    rw [normalized_prox_objective hL hR, normalized_prox_objective hL hR,
      scaled_normalizedPoint center y (ne_of_gt hR)] at hi
    have hi' := (div_le_div_iff_of_pos_right hA).1 hi
    linarith

/-- A physical residual subgradient suffices for global proximal minimality. -/
theorem isProxPoint_of_subgradient {L : ℝ≥0} {h : E → ℝ} {v x : E}
    (hs : SubgradientAt h ((L : ℝ) • (v-x)) x) : IsProxPoint L h v x := by
  intro y
  have hi := hs y
  simp only [real_inner_smul_left] at hi
  have hq := quadratic_remainder v x y
  have hrem : 0 ≤ (L : ℝ) * ((1/2 : ℝ) * inner ℝ (y-x) (y-x)) :=
    mul_nonneg L.property
      (mul_nonneg (by norm_num) (real_inner_self_nonneg (x := y-x)))
  calc
    h x + ((L : ℝ)/2) * inner ℝ (x-v) (x-v) ≤
        h x + ((L : ℝ)/2) * inner ℝ (x-v) (x-v) +
          (L : ℝ) * ((1/2 : ℝ) * inner ℝ (y-x) (y-x)) :=
      le_add_of_nonneg_right hrem
    _ = h x + ((L : ℝ)/2) * inner ℝ (x-v) (x-v) +
        (L : ℝ) * ((1/2 : ℝ) * inner ℝ (y-v) (y-v) -
          (1/2 : ℝ) * inner ℝ (x-v) (x-v) + inner ℝ (v-x) (y-x)) := by
      rw [hq]
    _ = (h x + (L : ℝ) * inner ℝ (v-x) (y-x)) +
        ((L : ℝ)/2) * inner ℝ (y-v) (y-v) := by ring
    _ ≤ h y + ((L : ℝ)/2) * inner ℝ (y-v) (y-v) :=
      add_le_add hi (le_refl _)

/-- Strict quadratic remainder makes an existing proximal solution unique.
Only a supporting subgradient at the reference solution is needed here. -/
theorem eq_of_subgradient_of_isProxPoint {L : ℝ≥0} {h : E → ℝ} {v x y : E}
    (hL : 0 < (L : ℝ)) (hs : SubgradientAt h ((L : ℝ) • (v-x)) x)
    (hp : IsProxPoint L h v y) : y = x := by
  have hi := hs y
  simp only [real_inner_smul_left] at hi
  have hp' := hp x
  have hq := quadratic_remainder v x y
  have hqL := congrArg (fun a : ℝ => (L : ℝ)*a) hq
  have hnonpos : (L : ℝ) * inner ℝ (y-x) (y-x) ≤ 0 := by nlinarith
  have hinner : inner ℝ (y-x) (y-x) ≤ 0 := by
    by_contra hi
    have hpos := mul_pos hL (lt_of_not_ge hi)
    linarith
  rw [real_inner_self_eq_norm_sq] at hinner
  have hnorm : ‖y-x‖ = 0 := by nlinarith [norm_nonneg (y-x)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

end LeanPEP.ActualFunction.ProximalScaling
