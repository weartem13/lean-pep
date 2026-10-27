import LeanPEP.ActualFunction.ProximalScaling
import LeanPEP.ActualFunction.ProximalGradient

/-! Generic certificate interface, moved unchanged; rate and witness applications
remain in the compatibility module. -/
noncomputable section
open scoped NNReal
namespace LeanPEP.ActualFunction.ProximalGradientScaling
open Proximal ProximalScaling SmoothScaling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Physical 1/L proximal-gradient run. It supplies minimizers, not an existence axiom. -/
def IsSmoothProxRun (N : ℕ) (L : ℝ≥0) (h : E → ℝ) (g : E → E) (x : ℕ → E) : Prop :=
  ∀ k < N, IsProxPoint L h (x k - (L : ℝ)⁻¹ • g (x k)) (x (k+1))

@[simp] theorem isSmoothProxRun_zero (L : ℝ≥0) (h : E → ℝ) (g : E → E) (x : ℕ → E) :
    IsSmoothProxRun 0 L h g x := by
  intro k hk
  omega

/-- Unit scaling is exactly the existing C2 run contract. -/
@[simp] theorem isSmoothProxRun_one (N : ℕ) (h : E → ℝ) (g : E → E) (x : ℕ → E) :
    IsSmoothProxRun N 1 h g x ↔ ProximalGradient.IsProxRun N h g x := by
  simp only [IsSmoothProxRun, ProximalGradient.IsProxRun, isProxPoint_one,
    NNReal.coe_one, inv_one, one_smul]

theorem IsSmoothProxRun.restrict {M N : ℕ} {L : ℝ≥0} {h : E → ℝ} {g : E → E}
    {x : ℕ → E} (hrun : IsSmoothProxRun N L h g x) (hMN : M ≤ N) :
    IsSmoothProxRun M L h g x := by
  intro k hk
  exact hrun k (by omega)

/-- The affine image of a normalized forward point is the physical forward point. -/
theorem normalized_forward {L : ℝ≥0} {R : ℝ} (hL : 0 < (L : ℝ)) (hR : 0 < R)
    (g : E → E) (center x : E) :
    scaledPoint center R (normalizedPoint center R x -
        normalizedGradient g center L R (normalizedPoint center R x)) =
      x - (L : ℝ)⁻¹ • g x := by
  have hcoeff : R * (1/((L : ℝ)*R)) = (L : ℝ)⁻¹ := by
    field_simp [ne_of_gt hL, ne_of_gt hR] <;> ring
  have hgrad : normalizedGradient g center L R (normalizedPoint center R x) =
      (1/((L : ℝ)*R)) • g x := by
    simp only [normalizedGradient, scaled_normalizedPoint center x (ne_of_gt hR)]
  have hRz : R • normalizedPoint center R x = x-center := by
    simp only [normalizedPoint, smul_smul, mul_inv_cancel₀ (ne_of_gt hR), one_smul]
  rw [hgrad]
  change center + R • (normalizedPoint center R x - (1/((L : ℝ)*R)) • g x) = _
  rw [smul_sub, hRz, smul_smul, hcoeff]
  abel

/-- Full equivalence of finite physical and normalized runs, including N=0.
No convexity or stationarity assumption is required for this transport. -/
theorem isSmoothProxRun_iff_normalized {N : ℕ} {L : ℝ≥0} {R : ℝ}
    (hL : 0 < (L : ℝ)) (hR : 0 < R) (h : E → ℝ) (g : E → E)
    (center : E) (x : ℕ → E) :
    IsSmoothProxRun N L h g x ↔
      ProximalGradient.IsProxRun N (normalizedFunction h center L R)
        (normalizedGradient g center L R) (fun k => normalizedPoint center R (x k)) := by
  have heq (k : ℕ) :
      IsProxPoint L h (x k - (L : ℝ)⁻¹ • g (x k)) (x (k+1)) ↔
        IsUnitProxPoint (normalizedFunction h center L R)
          (normalizedPoint center R (x k) -
            normalizedGradient g center L R (normalizedPoint center R (x k)))
          (normalizedPoint center R (x (k+1))) := by
    have hp := normalized_prox_iff hL hR h center
      (normalizedPoint center R (x k) -
        normalizedGradient g center L R (normalizedPoint center R (x k)))
      (normalizedPoint center R (x (k+1)))
    rw [normalized_forward hL hR,
      scaled_normalizedPoint center (x (k+1)) (ne_of_gt hR)] at hp
    exact hp
  constructor
  · intro hp k hk
    exact (heq k).mp (hp k hk)
  · intro hp k hk
    exact (heq k).mpr (hp k hk)

/-- The normalized reference subgradient cancels the normalized smooth gradient. -/
theorem normalized_stationarity {L : ℝ≥0} {R : ℝ} {h : E → ℝ} {g : E → E}
    {xStar : E} (hL : 0 < (L : ℝ)) (hR : 0 < R)
    (hs : SubgradientAt h (-g xStar) xStar) :
    SubgradientAt (normalizedFunction h xStar L R)
      (-normalizedGradient g xStar L R 0) 0 := by
  have hs' : SubgradientAt h (-g xStar) (scaledPoint xStar R (0 : E)) := by
    simpa only [scaledPoint, smul_zero, add_zero] using hs
  have hn := normalized_subgradient xStar hL hR hs'
  simpa only [normalizedGradient, scaledPoint, smul_zero, add_zero, smul_neg] using hn

theorem normalizedPoint_radius {R : ℝ} {xStar x0 : E} (hR : 0 < R)
    (hradius : ‖x0-xStar‖^2 ≤ R^2) :
    ‖normalizedPoint xStar R x0 - (0 : E)‖^2 ≤ 1 := by
  have hnorm : ‖normalizedPoint xStar R x0‖^2 = ‖x0-xStar‖^2 / R^2 := by
    unfold normalizedPoint
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
    field_simp [ne_of_gt hR] <;> ring
  rw [sub_zero, hnorm]
  have hR2 : 0 < R^2 := by positivity
  apply (div_le_iff₀ hR2).2
  simpa only [one_mul] using hradius

/-- Objective normalization subtracts each component's own reference value. -/
theorem normalized_objective {L : ℝ≥0} {R : ℝ} (hR : R ≠ 0)
    (f h : E → ℝ) (center x : E) :
    (normalizedFunction f center L R (normalizedPoint center R x) +
      normalizedFunction h center L R (normalizedPoint center R x)) -
      (normalizedFunction f center L R 0 + normalizedFunction h center L R 0) =
      ((f x + h x) - (f center + h center))/((L : ℝ)*R^2) := by
  have hzero : scaledPoint center R (0 : E) = center := by
    simp only [scaledPoint, smul_zero, add_zero]
  simp only [normalizedFunction]
  simp only [scaled_normalizedPoint center x hR, hzero,
    sub_self, zero_div, add_zero, sub_zero]
  ring

/-- Starting at a composite stationary point fixes every supplied proximal run.
The smooth gradient and nonsmooth subgradient need not vanish separately. -/
theorem stationary_run {N : ℕ} {L : ℝ≥0} {h : E → ℝ} {g : E → E}
    {xStar : E} {x : ℕ → E} (hL : 0 < (L : ℝ))
    (hs : SubgradientAt h (-g xStar) xStar) (hrun : IsSmoothProxRun N L h g x)
    (hx0 : x 0 = xStar) (k : ℕ) (hk : k ≤ N) : x k = xStar := by
  revert hk
  induction k with
  | zero => intro _; exact hx0
  | succ k ih =>
      intro hk
      have hkN : k < N := by omega
      have hxk := ih (by omega)
      have hp := hrun k hkN
      rw [hxk] at hp
      apply eq_of_subgradient_of_isProxPoint hL (hp := hp)
      have hd : xStar - (L : ℝ)⁻¹ • g xStar - xStar = -((L : ℝ)⁻¹ • g xStar) := by abel
      simpa only [hd, smul_neg, smul_smul, mul_inv_cancel₀ (ne_of_gt hL), one_smul] using hs

/-- Any accepted unit-radius certificate for the ORIGINAL C2 model scales.
No sign condition on the candidate bound is added, even at radius zero. -/
theorem certificate_upper {n : ℕ}
    (c : LeanPEP.GramPEP.UpperCertQ (LeanPEP.Profiles.ProximalGradient.modelQ n))
    (hc : LeanPEP.GramPEP.checkUpperCertQ c = true) (hempty : c.interpTerms = [])
    (hobj : c.objective = LeanPEP.Profiles.ProximalGradient.objectiveQ n)
    {L : ℝ≥0} {R : ℝ} {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsSmoothConvexFirstOrder L f g) (hh : ConvexOn ℝ Set.univ h)
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) (hs : SubgradientAt h (-g xStar) xStar)
    (hrun : IsSmoothProxRun (n+1) L h g x) (hradius : ‖x 0-xStar‖^2 ≤ R^2) :
    f (x (n+1)) + h (x (n+1)) - (f xStar + h xStar) ≤
      (L : ℝ)*R^2*(c.bound : ℝ) := by
  rcases eq_or_lt_of_le hR with rfl | hR
  · have hnorm : ‖x 0-xStar‖ = 0 := by nlinarith [norm_nonneg (x 0-xStar)]
    have hx0 := sub_eq_zero.mp (norm_eq_zero.mp hnorm)
    rw [stationary_run hL hs hrun hx0 (n+1) (le_refl _)]
    simp
  · have hnormalized := SmoothScaling.normalizedFirstOrder (xStar := xStar) hf hL hR
    have hconvex := normalizedFunction_convex xStar hL hR hh
    have hstationary := normalized_stationarity hL hR hs
    have hp := (isSmoothProxRun_iff_normalized hL hR h g xStar x).mp hrun
    have hr := normalizedPoint_radius hR hradius
    have hb := ProximalGradient.certificate_upper_of_prox c hc hempty hobj
      hnormalized hconvex hstationary hp hr
    rw [normalized_objective (ne_of_gt hR)] at hb
    have hA : 0 < (L : ℝ)*R^2 := by positivity
    have ht := (div_le_iff₀ hA).1 hb
    calc
      f (x (n+1)) + h (x (n+1)) - (f xStar + h xStar) ≤
          (c.bound : ℝ)*((L : ℝ)*R^2) := ht
      _ = _ := by ring

end LeanPEP.ActualFunction.ProximalGradientScaling
