import LeanPEP.ActualFunction.HuberWitnessAnalytic
import LeanPEP.ActualFunction.ParametricGDScaling
import Mathlib.Tactic

/-!
# General smoothness and radius scaling of the Huber lower witness

The normalized Huber witness is now kernel-verified as an actual analytic
one-smooth convex function, and its actual unit-step gradient-descent trajectory
attains `gdBoundQ N = 1 / (4N + 2)`.

This file transports that explicit witness to a positive smoothness constant
`L : ℝ≥0` and a nonnegative radius `R : ℝ`.  The scaled pair is

```text
F_{N,L,R}(x) = L * H_{R q_N}(x),
G_{N,L,R}(x) = L * min(x, R q_N),
q_N = 1 / (2N + 1).
```

Starting from `x0 = R`, the step-size-`1/L` recursion follows
`R * witnessPoint N k` and attains

```text
L * R^2 * gdBoundQ N = L * R^2 / (4N + 2).
```

The final section defines the one-dimensional analytic performance set and
proves that this value is its greatest element.  Combined with the already
verified dimension-independent upper theorem, this packages the exact tight
rate without using interpolation completeness or an external solver.
-/

noncomputable section

open scoped NNReal

namespace LeanPEP
namespace ActualFunction
namespace HuberWitness

open Set Filter
open ParametricGDActual
open ParametricGDScaling
open Toy.FiniteGD.ParametricUpper

open scoped Topology

/-- Radius-scaled Huber threshold. -/
def scaledThreshold (N : ℕ) (R : ℝ) : ℝ :=
  R * threshold N

/-- General-`L,R` Huber lower-witness function. -/
def scaledWitnessFunction
    (N : ℕ) (L : ℝ≥0) (R : ℝ) (x : ℝ) : ℝ :=
  (L : ℝ) * huberFunction (scaledThreshold N R) x

/-- Gradient field paired with `scaledWitnessFunction`. -/
def scaledWitnessGradient
    (N : ℕ) (L : ℝ≥0) (R : ℝ) (x : ℝ) : ℝ :=
  (L : ℝ) * huberGradient (scaledThreshold N R) x

/-- Radius-scaled closed-form trajectory. -/
def scaledWitnessPoint (N : ℕ) (R : ℝ) (k : ℕ) : ℝ :=
  R * witnessPoint N k

/-- Scaling the threshold and input by a nonnegative factor scales the clipped
Huber gradient by the same factor. -/
theorem huberGradient_scale
    {R a x : ℝ} (hR : 0 ≤ R) :
    huberGradient (R * a) (R * x) = R * huberGradient a x := by
  by_cases hxa : x ≤ a
  · have hRxa : R * x ≤ R * a :=
      mul_le_mul_of_nonneg_left hxa hR
    rw [huberGradient_of_le hRxa, huberGradient_of_le hxa]
  · have hax : a ≤ x := le_of_not_ge hxa
    have hRax : R * a ≤ R * x :=
      mul_le_mul_of_nonneg_left hax hR
    rw [huberGradient_of_ge hRax, huberGradient_of_ge hax]

/-- Scaling the threshold and input by a nonnegative factor scales the Huber
function value quadratically. -/
theorem huberFunction_scale
    {R a x : ℝ} (hR : 0 ≤ R) :
    huberFunction (R * a) (R * x) = R ^ 2 * huberFunction a x := by
  by_cases hxa : x ≤ a
  · have hRxa : R * x ≤ R * a :=
      mul_le_mul_of_nonneg_left hxa hR
    rw [huberFunction_of_le hRxa, huberFunction_of_le hxa]
    ring
  · have hax : a ≤ x := le_of_not_ge hxa
    have hRax : R * a ≤ R * x :=
      mul_le_mul_of_nonneg_left hax hR
    rw [huberFunction_of_ge hRax, huberFunction_of_ge hax]
    ring

@[simp] theorem scaledWitnessPoint_zero (N : ℕ) (R : ℝ) :
    scaledWitnessPoint N R 0 = R := by
  simp [scaledWitnessPoint]

@[simp] theorem scaledWitnessPoint_succ (N k : ℕ) (R : ℝ) :
    scaledWitnessPoint N R (k + 1) =
      scaledWitnessPoint N R k - R * threshold N := by
  unfold scaledWitnessPoint
  rw [witnessPoint_succ]
  ring

/-- Function values at radius-scaled points are exactly the normalized values
multiplied by `L R²`. -/
theorem scaledWitnessFunction_scale_point
    (N : ℕ) (L : ℝ≥0) {R x : ℝ} (hR : 0 ≤ R) :
    scaledWitnessFunction N L R (R * x) =
      (L : ℝ) * R ^ 2 * witnessFunction N x := by
  unfold scaledWitnessFunction scaledThreshold witnessFunction
  rw [huberFunction_scale hR]
  ring

/-- Gradients at radius-scaled points are exactly the normalized gradients
multiplied by `L R`. -/
theorem scaledWitnessGradient_scale_point
    (N : ℕ) (L : ℝ≥0) {R x : ℝ} (hR : 0 ≤ R) :
    scaledWitnessGradient N L R (R * x) =
      (L : ℝ) * R * witnessGradient N x := by
  unfold scaledWitnessGradient scaledThreshold witnessGradient
  rw [huberGradient_scale hR]
  ring

/-- Gradient of the amplitude-scaled Huber function, proved directly in
Fréchet/gradient form.  This avoids transporting a one-dimensional
`HasDerivAt` proposition across definitionally different real module-instance
paths. -/
theorem scaledWitnessFunction_hasGradientAt
    (N : ℕ) (L : ℝ≥0) (R x : ℝ) :
    HasGradientAt
      (scaledWitnessFunction N L R)
      (scaledWitnessGradient N L R x)
      x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hfun :
      scaledWitnessFunction N L R =
        (L : ℝ) • huberFunction (scaledThreshold N R) := by
    funext y
    simp [scaledWitnessFunction, smul_eq_mul]
  have hdual :
      InnerProductSpace.toDual ℝ ℝ (scaledWitnessGradient N L R x) =
        (L : ℝ) •
          InnerProductSpace.toDual ℝ ℝ (huberGradient (scaledThreshold N R) x) := by
    simpa [scaledWitnessGradient, smul_eq_mul] using
      (map_smulₛₗ (InnerProductSpace.toDual ℝ ℝ) (L : ℝ)
        (huberGradient (scaledThreshold N R) x))
  rw [hfun, hdual]
  exact
    (huberFunction_hasGradientAt (scaledThreshold N R) x).hasFDerivAt.const_smul
      (L : ℝ)

/-- Derivative of the scaled quadratic branch.  It is rebuilt under the
currently selected real derivative structures, rather than importing a
`HasDerivAt` proposition elaborated before later instances entered the
environment. -/
private theorem hasDerivAt_scaledQuadraticBranch
    (c x : ℝ) :
    HasDerivAt (fun y : ℝ => c * (y ^ 2 / 2)) (c * x) x := by
  have hsquare : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x)
  have hhalf : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
    have hmul := hsquare.mul_const ((1 : ℝ) / 2)
    have hcoeff : (2 * x) * ((1 : ℝ) / 2) = x := by ring
    rw [hcoeff] at hmul
    simpa [div_eq_mul_inv] using hmul
  simpa using hhalf.const_mul c

/-- Derivative of the scaled affine branch. -/
private theorem hasDerivAt_scaledAffineBranch
    (c a x : ℝ) :
    HasDerivAt
      (fun y : ℝ => c * (a * y - a ^ 2 / 2))
      (c * a) x := by
  have hlinear : HasDerivAt (fun y : ℝ => a * y) a x := by
    simpa using (hasDerivAt_id x).const_mul a
  have haffine :
      HasDerivAt (fun y : ℝ => a * y - a ^ 2 / 2) a x := by
    simpa using hlinear.sub_const (a ^ 2 / 2)
  simpa using haffine.const_mul c

/-- Derivative of the amplitude-scaled Huber function.  The proof follows the
same three-region argument as the normalized witness, but all derivative
lemmas are elaborated in this module's current instance environment. -/
theorem scaledWitnessFunction_hasDerivAt
    (N : ℕ) (L : ℝ≥0) (R x : ℝ) :
    HasDerivAt
      (scaledWitnessFunction N L R)
      (scaledWitnessGradient N L R x)
      x := by
  rcases lt_trichotomy x (scaledThreshold N R) with hxa | hxa | hax
  · have hEq :
        scaledWitnessFunction N L R =ᶠ[𝓝 x]
          (fun y : ℝ => (L : ℝ) * (y ^ 2 / 2)) := by
      filter_upwards [Iio_mem_nhds hxa] with y hy
      unfold scaledWitnessFunction
      rw [huberFunction_of_le (le_of_lt hy)]
    have hderiv :=
      (hasDerivAt_scaledQuadraticBranch (L : ℝ) x).congr_of_eventuallyEq hEq
    have hgrad : scaledWitnessGradient N L R x = (L : ℝ) * x := by
      unfold scaledWitnessGradient
      rw [huberGradient_of_le (le_of_lt hxa)]
    simpa [hgrad] using hderiv
  · subst x
    have hleft :
        HasDerivWithinAt
          (scaledWitnessFunction N L R)
          ((L : ℝ) * scaledThreshold N R)
          (Iic (scaledThreshold N R))
          (scaledThreshold N R) := by
      apply
        (hasDerivAt_scaledQuadraticBranch
          (L : ℝ) (scaledThreshold N R)).hasDerivWithinAt.congr_of_mem
      · intro y hy
        unfold scaledWitnessFunction
        rw [huberFunction_of_le hy]
      · exact mem_Iic.mpr le_rfl
    have hright :
        HasDerivWithinAt
          (scaledWitnessFunction N L R)
          ((L : ℝ) * scaledThreshold N R)
          (Ici (scaledThreshold N R))
          (scaledThreshold N R) := by
      apply
        (hasDerivAt_scaledAffineBranch
          (L : ℝ) (scaledThreshold N R)
          (scaledThreshold N R)).hasDerivWithinAt.congr_of_mem
      · intro y hy
        unfold scaledWitnessFunction
        rw [huberFunction_of_ge hy]
      · exact mem_Ici.mpr le_rfl
    have hcover :
        Iic (scaledThreshold N R) ∪ Ici (scaledThreshold N R) =
          (Set.univ : Set ℝ) := by
      ext y
      simp only [mem_union, mem_Iic, mem_Ici, mem_univ, iff_true]
      exact le_total y (scaledThreshold N R)
    have hnhds :
        Iic (scaledThreshold N R) ∪ Ici (scaledThreshold N R) ∈
          𝓝 (scaledThreshold N R) := by
      rw [hcover]
      exact univ_mem
    have hjoin :
        HasDerivAt
          (scaledWitnessFunction N L R)
          ((L : ℝ) * scaledThreshold N R)
          (scaledThreshold N R) :=
      (hleft.union hright).hasDerivAt hnhds
    have hgrad :
        scaledWitnessGradient N L R (scaledThreshold N R) =
          (L : ℝ) * scaledThreshold N R := by
      unfold scaledWitnessGradient
      rw [huberGradient_of_ge le_rfl]
    simpa [hgrad] using hjoin
  · have hEq :
        scaledWitnessFunction N L R =ᶠ[𝓝 x]
          (fun y : ℝ =>
            (L : ℝ) *
              (scaledThreshold N R * y - (scaledThreshold N R) ^ 2 / 2)) := by
      filter_upwards [Ioi_mem_nhds hax] with y hy
      unfold scaledWitnessFunction
      rw [huberFunction_of_ge (le_of_lt hy)]
    have hderiv :=
      (hasDerivAt_scaledAffineBranch
        (L : ℝ) (scaledThreshold N R) x).congr_of_eventuallyEq hEq
    have hgrad :
        scaledWitnessGradient N L R x =
          (L : ℝ) * scaledThreshold N R := by
      unfold scaledWitnessGradient
      rw [huberGradient_of_ge (le_of_lt hax)]
    simpa [hgrad] using hderiv

@[simp] theorem deriv_scaledWitnessFunction
    (N : ℕ) (L : ℝ≥0) (R x : ℝ) :
    deriv (scaledWitnessFunction N L R) x =
      scaledWitnessGradient N L R x :=
  (scaledWitnessFunction_hasDerivAt N L R x).deriv

/-- The general scaled witness is differentiable everywhere. -/
theorem scaledWitnessFunction_differentiable
    (N : ℕ) (L : ℝ≥0) (R : ℝ) :
    Differentiable ℝ (scaledWitnessFunction N L R) :=
  fun x => (scaledWitnessFunction_hasDerivAt N L R x).differentiableAt

/-- Nonnegative amplitude scaling preserves monotonicity of the clipped
field. -/
theorem scaledWitnessGradient_monotone
    (N : ℕ) (L : ℝ≥0) (R : ℝ) :
    Monotone (scaledWitnessGradient N L R) := by
  intro x y hxy
  change
    (L : ℝ) * huberGradient (scaledThreshold N R) x ≤
      (L : ℝ) * huberGradient (scaledThreshold N R) y
  exact mul_le_mul_of_nonneg_left
    (huberGradient_monotone (scaledThreshold N R) hxy) L.coe_nonneg

/-- Convexity of the general scaled witness. -/
theorem scaledWitnessFunction_convexOn
    (N : ℕ) (L : ℝ≥0) (R : ℝ) :
    ConvexOn ℝ Set.univ (scaledWitnessFunction N L R) := by
  apply Monotone.convexOn_univ_of_deriv
    (scaledWitnessFunction_differentiable N L R)
  intro x y hxy
  rw [deriv_scaledWitnessFunction, deriv_scaledWitnessFunction]
  exact scaledWitnessGradient_monotone N L R hxy

/-- The amplitude-scaled clipped gradient has Lipschitz constant `L`. -/
theorem scaledWitnessGradient_lipschitz
    (N : ℕ) (L : ℝ≥0) (R : ℝ) :
    LipschitzWith L (scaledWitnessGradient N L R) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  have hbase :=
    (huberGradient_lipschitz (scaledThreshold N R)).dist_le_mul x y
  have hbase' :
      |huberGradient (scaledThreshold N R) x -
          huberGradient (scaledThreshold N R) y| ≤ |x - y| := by
    simpa [Real.dist_eq] using hbase
  simp only [Real.dist_eq]
  change
    |(L : ℝ) * huberGradient (scaledThreshold N R) x -
        (L : ℝ) * huberGradient (scaledThreshold N R) y| ≤
      (L : ℝ) * |x - y|
  rw [← mul_sub, abs_mul, abs_of_nonneg L.coe_nonneg]
  exact mul_le_mul_of_nonneg_left hbase' L.coe_nonneg

/-- Full `L`-smooth analytic contract for the scaled witness. -/
theorem scaledWitness_analytic
    (N : ℕ) (L : ℝ≥0) (R : ℝ) :
    IsSmoothConvexAnalytic L
      (scaledWitnessFunction N L R)
      (scaledWitnessGradient N L R) where
  hasGradientAt := scaledWitnessFunction_hasGradientAt N L R
  convexOn := scaledWitnessFunction_convexOn N L R
  gradientLipschitz := scaledWitnessGradient_lipschitz N L R


/-- The radius-scaled threshold is nonnegative for nonnegative `R`. -/
theorem scaledThreshold_nonneg
    (N : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ scaledThreshold N R := by
  exact mul_nonneg hR (le_of_lt (threshold_pos N))

@[simp] theorem scaledWitnessFunction_zero
    (N : ℕ) (L : ℝ≥0) {R : ℝ} (hR : 0 ≤ R) :
    scaledWitnessFunction N L R 0 = 0 := by
  unfold scaledWitnessFunction
  rw [huberFunction_zero (scaledThreshold_nonneg N hR)]
  ring

@[simp] theorem scaledWitnessGradient_zero
    (N : ℕ) (L : ℝ≥0) {R : ℝ} (hR : 0 ≤ R) :
    scaledWitnessGradient N L R 0 = 0 := by
  unfold scaledWitnessGradient
  rw [huberGradient_zero (scaledThreshold_nonneg N hR)]
  ring

/-- Zero remains a global minimizer after nonnegative amplitude and radius
scaling. -/
theorem scaledWitness_zero_isGlobalMin
    (N : ℕ) (L : ℝ≥0) {R : ℝ} (hR : 0 ≤ R) (x : ℝ) :
    scaledWitnessFunction N L R 0 ≤ scaledWitnessFunction N L R x := by
  have hbase := zero_isGlobalMin (scaledThreshold_nonneg N hR) x
  exact mul_le_mul_of_nonneg_left hbase L.coe_nonneg

/-- The scaled gradient is constant along every required closed-form point. -/
theorem scaledWitnessGradient_scaledWitnessPoint
    (N : ℕ) (L : ℝ≥0) {R : ℝ} (hR : 0 ≤ R)
    (k : ℕ) (hk : k ≤ N) :
    scaledWitnessGradient N L R (scaledWitnessPoint N R k) =
      (L : ℝ) * R * threshold N := by
  rw [scaledWitnessPoint, scaledWitnessGradient_scale_point N L hR,
    witnessGradient_witnessPoint N k hk]

/-- One step of the step-size-`1/L` recursion advances the scaled closed-form
trajectory. -/
theorem scaledWitnessPoint_smoothGD_step
    (N : ℕ) {L : ℝ≥0} {R : ℝ}
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (k : ℕ) (hk : k ≤ N) :
    scaledWitnessPoint N R (k + 1) =
      scaledWitnessPoint N R k -
        (L : ℝ)⁻¹ •
          scaledWitnessGradient N L R (scaledWitnessPoint N R k) := by
  rw [scaledWitnessPoint_succ,
    scaledWitnessGradient_scaledWitnessPoint N L hR k hk]
  have hL0 : (L : ℝ) ≠ 0 := ne_of_gt hL
  have hcancel :
      (L : ℝ)⁻¹ • ((L : ℝ) * R * threshold N) =
        R * threshold N := by
    change
      (L : ℝ)⁻¹ * ((L : ℝ) * R * threshold N) =
        R * threshold N
    field_simp [hL0] <;> ring
  rw [hcancel]

/-- The actual step-size-`1/L` recursion starting at `R` follows the scaled
closed-form trajectory through index `N + 1`. -/
theorem smoothGDIterate_eq_scaledWitnessPoint
    (N : ℕ) {L : ℝ≥0} {R : ℝ}
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) :
    ∀ k : ℕ, k ≤ N + 1 →
      smoothGDIterate L (scaledWitnessGradient N L R) R k =
        scaledWitnessPoint N R k := by
  intro k
  induction k with
  | zero =>
      intro hk
      simp
  | succ k ih =>
      intro hk
      have hkN : k ≤ N := by omega
      have hkSucc : k ≤ N + 1 := by omega
      calc
        smoothGDIterate L (scaledWitnessGradient N L R) R (k + 1) =
            smoothGDIterate L (scaledWitnessGradient N L R) R k -
              (L : ℝ)⁻¹ •
                scaledWitnessGradient N L R
                  (smoothGDIterate L (scaledWitnessGradient N L R) R k) := by
            rw [smoothGDIterate_succ]
        _ = scaledWitnessPoint N R k -
              (L : ℝ)⁻¹ •
                scaledWitnessGradient N L R (scaledWitnessPoint N R k) := by
            rw [ih hkSucc]
        _ = scaledWitnessPoint N R (k + 1) :=
          (scaledWitnessPoint_smoothGD_step N hL hR k hkN).symm

/-- The final actual iterate is the scaled advertised point. -/
theorem smoothGDIterate_final
    (N : ℕ) {L : ℝ≥0} {R : ℝ}
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) :
    smoothGDIterate L (scaledWitnessGradient N L R) R N =
      scaledWitnessPoint N R N :=
  smoothGDIterate_eq_scaledWitnessPoint N hL hR N (by omega)

/-- General scaled performance bound. -/
def generalBound (N : ℕ) (L : ℝ≥0) (R : ℝ) : ℝ :=
  (L : ℝ) * R ^ 2 * (gdBoundQ N : ℝ)

/-- Closed form of the general scaled bound. -/
theorem generalBound_eq_closed
    (N : ℕ) (L : ℝ≥0) (R : ℝ) :
    generalBound N L R =
      (L : ℝ) * R ^ 2 / (((4 * N + 2 : ℕ) : ℝ)) := by
  unfold generalBound
  rw [gdBoundQ_cast_eq_closed]
  ring

/-- The actual scaled execution attains `L R² * gdBoundQ N`. -/
theorem scaledWitness_smoothGD_attains_bound
    (N : ℕ) {L : ℝ≥0} {R : ℝ}
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) :
    scaledWitnessFunction N L R
        (smoothGDIterate L (scaledWitnessGradient N L R) R N) -
      scaledWitnessFunction N L R 0 =
        generalBound N L R := by
  rw [smoothGDIterate_final N hL hR]
  change
    scaledWitnessFunction N L R (R * witnessPoint N N) -
      scaledWitnessFunction N L R 0 = generalBound N L R
  rw [scaledWitnessFunction_scale_point N L hR,
    witnessFunction_final_eq_bound,
    scaledWitnessFunction_zero N L hR]
  simp [generalBound]

/-- User-facing closed form of the attained general value. -/
theorem scaledWitness_smoothGD_attains_closed_form
    (N : ℕ) {L : ℝ≥0} {R : ℝ}
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) :
    scaledWitnessFunction N L R
        (smoothGDIterate L (scaledWitnessGradient N L R) R N) -
      scaledWitnessFunction N L R 0 =
        (L : ℝ) * R ^ 2 / (((4 * N + 2 : ℕ) : ℝ)) := by
  rw [scaledWitness_smoothGD_attains_bound N hL hR,
    generalBound_eq_closed]

/-- The scaled initial point has exactly the declared squared radius. -/
theorem scaledWitness_initialRadius
    {R : ℝ} (hR : 0 ≤ R) :
    ‖R - 0‖ ^ 2 = R ^ 2 := by
  simp [Real.norm_eq_abs, abs_of_nonneg hR]

/-- Proof-carrying general analytic lower witness. -/
theorem general_analytic_lower_witness
    (N : ℕ) {L : ℝ≥0} {R : ℝ}
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) :
    IsSmoothConvexAnalytic L
        (scaledWitnessFunction N L R)
        (scaledWitnessGradient N L R) ∧
      scaledWitnessGradient N L R 0 = 0 ∧
      (∀ x : ℝ,
        scaledWitnessFunction N L R 0 ≤ scaledWitnessFunction N L R x) ∧
      ‖R - 0‖ ^ 2 ≤ R ^ 2 ∧
      scaledWitnessFunction N L R
          (smoothGDIterate L (scaledWitnessGradient N L R) R N) -
        scaledWitnessFunction N L R 0 = generalBound N L R := by
  refine ⟨scaledWitness_analytic N L R,
    scaledWitnessGradient_zero N L hR,
    scaledWitness_zero_isGlobalMin N L hR, ?_,
    scaledWitness_smoothGD_attains_bound N hL hR⟩
  exact le_of_eq (scaledWitness_initialRadius hR)

/-- Values attained by one-dimensional analytic `L`-smooth convex GD instances
with squared initial radius at most `R²`. -/
def oneDimensionalAnalyticGDValues
    (N : ℕ) (L : ℝ≥0) (R : ℝ) : Set ℝ :=
  { value | ∃ (f g : ℝ → ℝ) (xStar x0 : ℝ),
      IsSmoothConvexAnalytic L f g ∧
      g xStar = 0 ∧
      ‖x0 - xStar‖ ^ 2 ≤ R ^ 2 ∧
      f (smoothGDIterate L g x0 N) - f xStar = value }

/-- The scaled Huber instance attains the general bound in the one-dimensional
analytic performance set. -/
theorem generalBound_mem_oneDimensionalAnalyticGDValues
    (N : ℕ) {L : ℝ≥0} {R : ℝ}
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) :
    generalBound N L R ∈ oneDimensionalAnalyticGDValues N L R := by
  refine ⟨scaledWitnessFunction N L R,
    scaledWitnessGradient N L R, 0, R,
    scaledWitness_analytic N L R,
    scaledWitnessGradient_zero N L hR, ?_,
    scaledWitness_smoothGD_attains_bound N hL hR⟩
  exact le_of_eq (scaledWitness_initialRadius hR)

/-- Exact one-dimensional analytic worst-case value. -/
theorem oneDimensional_analytic_tight
    (N : ℕ) {L : ℝ≥0} {R : ℝ}
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) :
    IsGreatest
      (oneDimensionalAnalyticGDValues N L R)
      (generalBound N L R) := by
  constructor
  · exact generalBound_mem_oneDimensionalAnalyticGDValues N hL hR
  · intro value hvalue
    rcases hvalue with
      ⟨f, g, xStar, x0, hfun, hstationary, hradius, hattain⟩
    have hupper := hfun.parametricGD_upper_radius
      hL (R := R) N hstationary hradius
    rw [← hattain]
    simpa [generalBound] using hupper

/-- Dimension-independent upper bound together with exact one-dimensional
attainment.  Since the ambient Hilbert space `E` is arbitrary, this is the
formal packaging of the tight analytic rate. -/
theorem analytic_upper_and_oneDimensional_tight
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (N : ℕ) {L : ℝ≥0} {R : ℝ}
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) :
    (∀ {f : E → ℝ} {g : E → E} {xStar x0 : E},
      IsSmoothConvexAnalytic L f g →
      g xStar = 0 →
      ‖x0 - xStar‖ ^ 2 ≤ R ^ 2 →
      f (smoothGDIterate L g x0 N) - f xStar ≤ generalBound N L R) ∧
    IsGreatest
      (oneDimensionalAnalyticGDValues N L R)
      (generalBound N L R) := by
  constructor
  · intro f g xStar x0 hfun hstationary hradius
    simpa [generalBound] using
      hfun.parametricGD_upper_radius
        hL (R := R) N hstationary hradius
  · exact oneDimensional_analytic_tight N hL hR

end HuberWitness
end ActualFunction
end LeanPEP
