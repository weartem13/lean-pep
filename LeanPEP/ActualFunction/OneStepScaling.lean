import LeanPEP.ActualFunction.SmoothScalingCore
import LeanPEP.ActualFunction.OneStepUpper
import Mathlib.Tactic

/-!
# General `L` and radius scaling for the one-step actual-function theorem

The exact certificate used by v0.12A is normalized to:

* gradient Lipschitz constant `1`;
* unit gradient step; and
* initial squared radius at most `1`.

This file first exposes the same certificate theorem directly from the exact
normalized first-order models.  It then normalizes an `L`-smooth first-order
pair by an affine coordinate change and positive function-value scaling, and
transports the result back to

```text
f(x₀ - (1/L) g(x₀)) - f(x★) <= L R² / 6.
```

The `R = 0` case is discharged separately from the radius assumption and
stationarity.  No new certificate, numerical computation, or interpolation
completeness result is introduced.
-/

open scoped NNReal

namespace LeanPEP
namespace ActualFunction

namespace IsOneSmoothConvexFirstOrder

open GramPEP
open GramPEP.UpperCertificateExamples

variable
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {g : E → E}

/-- The normalized one-step exact certificate needs only the exact first-order
models; completeness of the ambient Hilbert space is not used at this stage. -/
theorem oneStepGD_upper_of_inner_radius
    (h : IsOneSmoothConvexFirstOrder f g)
    {xStar x0 x1 : E}
    (hstationary : g xStar = 0)
    (hstep : x1 = x0 - g x0)
    (hradius : inner ℝ (x0 - xStar) (x0 - xStar) ≤ 1) :
    f x1 - f xStar ≤ (1 : ℝ) / 6 := by
  have hreal :=
    OneStepGram.oneStepRealizesActualSamples
      g xStar x0 x1 hstationary hstep
  have hcore :
      CoreFeasible (OneStepGram.oneStepData f g xStar x0 x1) := by
    constructor
    · exact FiniteGram.gramOfVectors_posSemidef
        (OneStepGram.oneStepBase g xStar x0 x1)
    · intro i j
      unfold OneStepGram.oneStepData
      rw [FiniteGram.interpolationSlack_dataOfModel hreal i j]
      exact ActualFunction.interpolationSlack_nonneg h
        (OneStepGram.oneStepSamples xStar x0 x1 i)
        (OneStepGram.oneStepSamples xStar x0 x1 j)
  have hcertificate :=
    oneStep_upper
      (OneStepGram.oneStepData f g xStar x0 x1)
      (OneStepGram.oneStepData_realizesModel f g xStar x0 x1)
      hcore
      (OneStepGram.oneStepData_assumptionsFeasible
        f g xStar x0 x1 hradius)
  simpa [OneStepGram.oneStepData, OneStepGram.oneStepSamples,
    FiniteGram.dataOfModel] using hcertificate

/-- Norm-squared form of the first-order one-step theorem. -/
theorem oneStepGD_upper
    (h : IsOneSmoothConvexFirstOrder f g)
    {xStar x0 x1 : E}
    (hstationary : g xStar = 0)
    (hstep : x1 = x0 - g x0)
    (hradius : ‖x0 - xStar‖ ^ 2 ≤ 1) :
    f x1 - f xStar ≤ (1 : ℝ) / 6 := by
  apply h.oneStepGD_upper_of_inner_radius hstationary hstep
  simpa [real_inner_self_eq_norm_sq] using hradius

/-- Direct-update form of the first-order one-step theorem. -/
theorem oneStepGD_upper_at_update
    (h : IsOneSmoothConvexFirstOrder f g)
    {xStar x0 : E}
    (hstationary : g xStar = 0)
    (hradius : ‖x0 - xStar‖ ^ 2 ≤ 1) :
    f (x0 - g x0) - f xStar ≤ (1 : ℝ) / 6 :=
  h.oneStepGD_upper hstationary rfl hradius

end IsOneSmoothConvexFirstOrder


namespace IsSmoothConvexAnalytic

variable
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {L : ℝ≥0} {f : E → ℝ} {g : E → E}

/-- General one-step upper theorem for positive radius. This is the scaling
core used by the public nonnegative-radius theorem. -/
theorem oneStepGD_upper_at_update_of_pos_radius
    (h : IsSmoothConvexAnalytic L f g)
    (hL : 0 < (L : ℝ))
    {xStar x0 : E} {R : ℝ}
    (hR : 0 < R)
    (hstationary : g xStar = 0)
    (hradius : ‖x0 - xStar‖ ^ 2 ≤ R ^ 2) :
    f (x0 - (L : ℝ)⁻¹ • g x0) - f xStar ≤
      (L : ℝ) * R ^ 2 / 6 := by
  let F : E → ℝ := SmoothScaling.normalizedFunction f xStar L R
  let G : E → E := SmoothScaling.normalizedGradient g xStar L R
  let z0 : E := R⁻¹ • (x0 - xStar)
  have hL0 : (L : ℝ) ≠ 0 := ne_of_gt hL
  have hR0 : R ≠ 0 := ne_of_gt hR
  have hA : 0 < (L : ℝ) * R ^ 2 := by positivity
  have hnormalized : IsOneSmoothConvexFirstOrder F G := by
    simpa [F, G] using
      SmoothScaling.normalizedFirstOrder
        (xStar := xStar) h.toFirstOrder hL hR
  have hGzero : G 0 = 0 := by
    simp [G, SmoothScaling.normalizedGradient,
      SmoothScaling.scaledPoint, hstationary]
  have hzradius : ‖z0‖ ^ 2 ≤ 1 := by
    have hR2 : 0 < R ^ 2 := by positivity
    have hnorm :
        ‖z0‖ ^ 2 = ‖x0 - xStar‖ ^ 2 / R ^ 2 := by
      dsimp [z0]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
      field_simp [hR0] <;> ring
    rw [hnorm]
    apply (div_le_iff₀ hR2).2
    simpa using hradius
  have hRz0 : R • z0 = x0 - xStar := by
    simp [z0, smul_smul, hR0]
  have hscaledZ0 : SmoothScaling.scaledPoint xStar R z0 = x0 := by
    rw [SmoothScaling.scaledPoint, hRz0]
    abel
  have hGz0 :
      G z0 = (1 / ((L : ℝ) * R)) • g x0 := by
    dsimp [G, SmoothScaling.normalizedGradient]
    rw [hscaledZ0]
  have hcoeff :
      R * (1 / ((L : ℝ) * R)) = (L : ℝ)⁻¹ := by
    field_simp [hL0, hR0] <;> ring
  have hscaledUpdate :
      SmoothScaling.scaledPoint xStar R (z0 - G z0) =
        x0 - (L : ℝ)⁻¹ • g x0 := by
    rw [SmoothScaling.scaledPoint, smul_sub, hRz0, hGz0, smul_smul,
      hcoeff]
    abel
  have hunit :
      F (z0 - G z0) - F 0 ≤ (1 : ℝ) / 6 :=
    hnormalized.oneStepGD_upper_at_update
      (xStar := (0 : E)) (x0 := z0) hGzero (by simpa using hzradius)
  have hgap :
      F (z0 - G z0) - F 0 =
        (f (x0 - (L : ℝ)⁻¹ • g x0) - f xStar) /
          ((L : ℝ) * R ^ 2) := by
    dsimp [F, SmoothScaling.normalizedFunction]
    rw [hscaledUpdate]
    simp [SmoothScaling.scaledPoint]
  rw [hgap] at hunit
  have hscaled := (div_le_iff₀ hA).1 hunit
  calc
    f (x0 - (L : ℝ)⁻¹ • g x0) - f xStar ≤
        ((1 : ℝ) / 6) * ((L : ℝ) * R ^ 2) := hscaled
    _ = (L : ℝ) * R ^ 2 / 6 := by ring

/-- General one-step upper theorem for a nonnegative radius. The zero-radius
case follows from `x0 = xStar` and stationarity; the positive-radius case is
handled by exact normalization. -/
theorem oneStepGD_upper_at_update
    (h : IsSmoothConvexAnalytic L f g)
    (hL : 0 < (L : ℝ))
    {xStar x0 : E} {R : ℝ}
    (hR : 0 ≤ R)
    (hstationary : g xStar = 0)
    (hradius : ‖x0 - xStar‖ ^ 2 ≤ R ^ 2) :
    f (x0 - (L : ℝ)⁻¹ • g x0) - f xStar ≤
      (L : ℝ) * R ^ 2 / 6 := by
  rcases eq_or_lt_of_le hR with rfl | hRpos
  · have hnorm : ‖x0 - xStar‖ = 0 := by
      have hsquare : ‖x0 - xStar‖ ^ 2 ≤ 0 := by
        simpa using hradius
      nlinarith [norm_nonneg (x0 - xStar)]
    have hx : x0 = xStar := by
      apply sub_eq_zero.mp
      exact norm_eq_zero.mp hnorm
    subst x0
    simp [hstationary]
  · exact h.oneStepGD_upper_at_update_of_pos_radius
      hL hRpos hstationary hradius

/-- Explicit-iterate form of the general one-step upper theorem. -/
theorem oneStepGD_upper
    (h : IsSmoothConvexAnalytic L f g)
    (hL : 0 < (L : ℝ))
    {xStar x0 x1 : E} {R : ℝ}
    (hR : 0 ≤ R)
    (hstationary : g xStar = 0)
    (hstep : x1 = x0 - (L : ℝ)⁻¹ • g x0)
    (hradius : ‖x0 - xStar‖ ^ 2 ≤ R ^ 2) :
    f x1 - f xStar ≤ (L : ℝ) * R ^ 2 / 6 := by
  subst x1
  exact h.oneStepGD_upper_at_update hL hR hstationary hradius

/-- Radius-free corollary using the exact initial distance as the scale. -/
theorem oneStepGD_upper_exact_radius
    (h : IsSmoothConvexAnalytic L f g)
    (hL : 0 < (L : ℝ))
    {xStar x0 : E}
    (hstationary : g xStar = 0) :
    f (x0 - (L : ℝ)⁻¹ • g x0) - f xStar ≤
      (L : ℝ) * ‖x0 - xStar‖ ^ 2 / 6 := by
  apply h.oneStepGD_upper_at_update hL (norm_nonneg (x0 - xStar)) hstationary
  rfl

end IsSmoothConvexAnalytic

end ActualFunction
end LeanPEP
