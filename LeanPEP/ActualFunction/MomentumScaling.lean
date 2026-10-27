import LeanPEP.ActualFunction.MomentumActual
import LeanPEP.ActualFunction.ParametricGDScaling
import LeanPEP.GramPEP.UpperCertificateChecker
import Mathlib.Tactic

/-!
# Affine transport and general smoothness/radius for actual momentum

Both state and query are transported under `z ↦ xStar + R • z`.  The generic
transport theorem allows singular and signed spatial scales, provided the
fields intertwine.  The normalization theorem uses positive `L,R`; the public
certificate theorem handles `R = 0` separately by stationarity.

The normalized certificate, its objective, the rational schedule, the profile
compiler, and the Gram checker are unchanged.  Only the actual oracle is scaled:
physical steps are `(s.step k : ℝ) / L`, whereas momentum is unchanged.
-/

open scoped NNReal

namespace LeanPEP.ActualFunction.MomentumScaling

open LeanPEP.Profiles.Momentum (ScheduleQ outputModelQ outputObjectiveQ)
open LeanPEP.Profiles.GramCompilation (unitRadiusNormalizationQ)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual state with physical step coefficient `alpha_k / L`. -/
noncomputable def smoothState (s : ScheduleQ) (L : ℝ≥0)
    (g : E → E) (x0 : E) (k : ℕ) : E :=
  MomentumActual.state s (ParametricGDScaling.normalizedGradient L g) x0 k

/-- Actual query of the same run; momentum is not divided by `L`. -/
noncomputable def smoothQuery (s : ScheduleQ) (L : ℝ≥0)
    (g : E → E) (x0 : E) (k : ℕ) : E :=
  MomentumActual.query s (ParametricGDScaling.normalizedGradient L g) x0 k

@[simp] theorem smoothState_zero (s : ScheduleQ) (L : ℝ≥0) (g : E → E) (x0 : E) :
    smoothState s L g x0 0 = x0 := rfl

@[simp] theorem smoothQuery_zero (s : ScheduleQ) (L : ℝ≥0) (g : E → E) (x0 : E) :
    smoothQuery s L g x0 0 = x0 := rfl

theorem smoothState_succ (s : ScheduleQ) (L : ℝ≥0) (g : E → E) (x0 : E) (k : ℕ) :
    smoothState s L g x0 (k + 1) = smoothQuery s L g x0 k -
      ((s.step k : ℝ) / (L : ℝ)) • g (smoothQuery s L g x0 k) := by
  simpa [smoothState, smoothQuery, ParametricGDScaling.normalizedGradient,
    smul_smul, div_eq_mul_inv] using
    MomentumActual.state_succ s (ParametricGDScaling.normalizedGradient L g) x0 k

theorem smoothQuery_succ (s : ScheduleQ) (L : ℝ≥0) (g : E → E) (x0 : E) (k : ℕ) :
    smoothQuery s L g x0 (k + 1) = smoothState s L g x0 (k + 1) +
      (s.momentum k : ℝ) • (smoothState s L g x0 (k + 1) - smoothState s L g x0 k) := rfl

/-- A transparent reuse of the existing run contract, not a second recursion. -/
abbrev IsSmoothRun (N : ℕ) (s : ScheduleQ) (L : ℝ≥0)
    (g : E → E) (x0 : E) (x y : ℕ → E) : Prop :=
  MomentumActual.IsRun N s (ParametricGDScaling.normalizedGradient L g) x0 x y

/-- Build the reused run contract from the ordinary physical update equations. -/
theorem isSmoothRun_of_updates {N : ℕ} {s : ScheduleQ} {L : ℝ≥0}
    {g : E → E} {x0 : E} {x y : ℕ → E}
    (hx : x 0 = x0) (hy : y 0 = x0)
    (hstep : ∀ k, k < N → x (k + 1) = y k -
      ((s.step k : ℝ) / (L : ℝ)) • g (y k))
    (hmomentum : ∀ k, k < N → y (k + 1) = x (k + 1) +
      (s.momentum k : ℝ) • (x (k + 1) - x k)) :
    IsSmoothRun N s L g x0 x y where
  state_initial := hx
  query_initial := hy
  step := by
    intro k hk
    simpa [ParametricGDScaling.normalizedGradient, smul_smul, div_eq_mul_inv]
      using hstep k hk
  extrapolate := hmomentum

theorem eq_of_isSmoothRun {N : ℕ} {s : ScheduleQ} {L : ℝ≥0}
    {g : E → E} {x0 : E} {x y : ℕ → E}
    (h : IsSmoothRun N s L g x0 x y) (k : ℕ) (hk : k ≤ N) :
    x k = smoothState s L g x0 k ∧ y k = smoothQuery s L g x0 k :=
  MomentumActual.eq_of_isRun h k hk

/-- Affine images preserve a step, with the field scaled by `R`. -/
theorem scaledPoint_sub_smul (center : E) (R a : ℝ) (y v : E) :
    SmoothScaling.scaledPoint center R (y - a • v) =
      SmoothScaling.scaledPoint center R y - a • (R • v) := by
  simp only [SmoothScaling.scaledPoint, smul_sub, smul_smul]
  rw [mul_comm R a]
  abel

/-- Momentum is an affine combination; its coefficient does not change. -/
theorem scaledPoint_extrapolate (center : E) (R b : ℝ) (x y : E) :
    SmoothScaling.scaledPoint center R (x + b • (x - y)) =
      SmoothScaling.scaledPoint center R x + b •
        (SmoothScaling.scaledPoint center R x - SmoothScaling.scaledPoint center R y) := by
  have hdiff : SmoothScaling.scaledPoint center R x -
      SmoothScaling.scaledPoint center R y = R • (x - y) := by
    simp only [SmoothScaling.scaledPoint, smul_sub]
    abel
  rw [hdiff]
  simp only [SmoothScaling.scaledPoint, smul_add, smul_smul]
  rw [mul_comm R b]
  abel

/-- Intertwining fields transport the reference run by the affine map.
There is no positivity, invertibility, smoothness, or certificate assumption. -/
theorem isRun_affine (N : ℕ) (s : ScheduleQ) (g g' : E → E)
    (center : E) (R : ℝ) (z0 : E)
    (hfields : ∀ z, g' (SmoothScaling.scaledPoint center R z) = R • g z) :
    MomentumActual.IsRun N s g' (SmoothScaling.scaledPoint center R z0)
      (fun k => SmoothScaling.scaledPoint center R (MomentumActual.state s g z0 k))
      (fun k => SmoothScaling.scaledPoint center R (MomentumActual.query s g z0 k)) where
  state_initial := rfl
  query_initial := rfl
  step := by
    intro k _
    rw [MomentumActual.state_succ, scaledPoint_sub_smul, hfields]
  extrapolate := by
    intro k _
    rw [MomentumActual.query_succ, scaledPoint_extrapolate]

/-- Both sequences commute with the affine map, at every finite index. -/
theorem affine_trajectory (s : ScheduleQ) (g g' : E → E)
    (center : E) (R : ℝ) (z0 : E)
    (hfields : ∀ z, g' (SmoothScaling.scaledPoint center R z) = R • g z) (k : ℕ) :
    MomentumActual.state s g' (SmoothScaling.scaledPoint center R z0) k =
        SmoothScaling.scaledPoint center R (MomentumActual.state s g z0 k) ∧
      MomentumActual.query s g' (SmoothScaling.scaledPoint center R z0) k =
        SmoothScaling.scaledPoint center R (MomentumActual.query s g z0 k) := by
  have h := MomentumActual.eq_of_isRun (isRun_affine k s g g' center R z0 hfields)
    k (le_refl k)
  exact ⟨h.1.symm, h.2.symm⟩

/-- Initial point in normalized coordinates.  Only positive-radius theorems
use its inverse; the public zero-radius branch never normalizes by zero. -/
noncomputable def normalizedInitial (xStar x0 : E) (R : ℝ) : E :=
  R⁻¹ • (x0 - xStar)

theorem scaledPoint_normalizedInitial (xStar x0 : E) {R : ℝ} (hR : R ≠ 0) :
    SmoothScaling.scaledPoint xStar R (normalizedInitial xStar x0 R) = x0 := by
  simp [SmoothScaling.scaledPoint, normalizedInitial, smul_smul, hR] <;> abel

theorem normalizedInitial_normSq (xStar x0 : E) {R : ℝ} (hR : 0 < R) :
    ‖normalizedInitial xStar x0 R‖ ^ 2 = ‖x0 - xStar‖ ^ 2 / R ^ 2 := by
  unfold normalizedInitial
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
  field_simp [ne_of_gt hR] <;> ring

theorem normalizedInitial_radius {xStar x0 : E} {R : ℝ} (hR : 0 < R)
    (hradius : ‖x0 - xStar‖ ^ 2 ≤ R ^ 2) :
    ‖normalizedInitial xStar x0 R‖ ^ 2 ≤ 1 := by
  rw [normalizedInitial_normSq xStar x0 hR]
  have hR2 : 0 < R ^ 2 := by positivity
  apply (div_le_iff₀ hR2).2
  simpa using hradius

/-- Positive-`L,R` coordinate normalization preserves BOTH actual sequences. -/
theorem normalized_trajectory (s : ScheduleQ) {L : ℝ≥0} {R : ℝ}
    (hL : 0 < (L : ℝ)) (hR : 0 < R) (g : E → E) (xStar x0 : E) (k : ℕ) :
    SmoothScaling.scaledPoint xStar R
        (MomentumActual.state s (SmoothScaling.normalizedGradient g xStar L R)
          (normalizedInitial xStar x0 R) k) = smoothState s L g x0 k ∧
      SmoothScaling.scaledPoint xStar R
        (MomentumActual.query s (SmoothScaling.normalizedGradient g xStar L R)
          (normalizedInitial xStar x0 R) k) = smoothQuery s L g x0 k := by
  have hcoeff : R * (1 / ((L : ℝ) * R)) = (L : ℝ)⁻¹ := by
    field_simp [ne_of_gt hL, ne_of_gt hR] <;> ring
  have hfields : ∀ z,
      ParametricGDScaling.normalizedGradient L g (SmoothScaling.scaledPoint xStar R z) =
        R • SmoothScaling.normalizedGradient g xStar L R z := by
    intro z
    simp only [ParametricGDScaling.normalizedGradient,
      SmoothScaling.normalizedGradient, smul_smul, hcoeff]
  have h := affine_trajectory s (SmoothScaling.normalizedGradient g xStar L R)
    (ParametricGDScaling.normalizedGradient L g) xStar R
    (normalizedInitial xStar x0 R) hfields k
  rw [scaledPoint_normalizedInitial xStar x0 (ne_of_gt hR)] at h
  exact ⟨h.1.symm, h.2.symm⟩

/-- A stationary starting point stays stationary for every rational schedule.
This is the zero-radius argument, independent of function-class assumptions. -/
theorem stationary_trajectory (s : ScheduleQ) (L : ℝ≥0) {g : E → E} {xStar : E}
    (hs : g xStar = 0) (k : ℕ) :
    smoothState s L g xStar k = xStar ∧ smoothQuery s L g xStar k = xStar := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
      have hx : smoothState s L g xStar (k + 1) = xStar := by
        simp only [smoothState_succ, ih.2, hs, smul_zero, sub_zero]
      refine ⟨hx, ?_⟩
      simp only [smoothQuery_succ, hx, ih.1, sub_self, smul_zero, add_zero]

/-- A unit-radius accepted certificate transfers to any positive physical radius.
The certificate's objective must still match the compiled final-state gap. -/
theorem certificate_upper_of_pos_radius {N : ℕ} {s : ScheduleQ}
    (c : GramPEP.UpperCertQ (outputModelQ N s unitRadiusNormalizationQ))
    (hcheck : GramPEP.checkUpperCertQ c = true)
    (hobjective : c.objective = outputObjectiveQ N s unitRadiusNormalizationQ)
    {L : ℝ≥0} {R : ℝ} {f : E → ℝ} {g : E → E} {xStar x0 : E}
    (hfun : IsSmoothConvexFirstOrder L f g) (hL : 0 < (L : ℝ)) (hR : 0 < R)
    (hs : g xStar = 0) (hradius : ‖x0 - xStar‖ ^ 2 ≤ R ^ 2) :
    f (smoothState s L g x0 N) - f xStar ≤ (L : ℝ) * R ^ 2 * (c.bound : ℝ) := by
  let F : E → ℝ := SmoothScaling.normalizedFunction f xStar L R
  let G : E → E := SmoothScaling.normalizedGradient g xStar L R
  let z0 : E := normalizedInitial xStar x0 R
  have hnormalized : IsOneSmoothConvexFirstOrder F G :=
    SmoothScaling.normalizedFirstOrder hfun hL hR
  have hGzero : G (0 : E) = 0 := by
    simp [G, SmoothScaling.normalizedGradient, SmoothScaling.scaledPoint, hs]
  have hzradius : ‖z0 - (0 : E)‖ ^ 2 ≤ (unitRadiusNormalizationQ.radiusSq : ℝ) := by
    simpa [z0, unitRadiusNormalizationQ] using normalizedInitial_radius hR hradius
  have hunit : F (MomentumActual.state s G z0 N) - F 0 ≤ (c.bound : ℝ) :=
    MomentumActual.certificate_upper c hcheck hobjective hnormalized hGzero hzradius
  have hstate : SmoothScaling.scaledPoint xStar R (MomentumActual.state s G z0 N) =
      smoothState s L g x0 N := (normalized_trajectory s hL hR g xStar x0 N).1
  have hgap : F (MomentumActual.state s G z0 N) - F 0 =
      (f (smoothState s L g x0 N) - f xStar) / ((L : ℝ) * R ^ 2) := by
    dsimp [F, SmoothScaling.normalizedFunction]
    rw [hstate]
    simp [SmoothScaling.scaledPoint]
  rw [hgap] at hunit
  have hA : 0 < (L : ℝ) * R ^ 2 := by positivity
  have hscaled := (div_le_iff₀ hA).1 hunit
  calc
    f (smoothState s L g x0 N) - f xStar ≤
        (c.bound : ℝ) * ((L : ℝ) * R ^ 2) := hscaled
    _ = (L : ℝ) * R ^ 2 * (c.bound : ℝ) := by ring

/-- Nonnegative-radius version, including `R = 0` without dividing by `R`. -/
theorem certificate_upper {N : ℕ} {s : ScheduleQ}
    (c : GramPEP.UpperCertQ (outputModelQ N s unitRadiusNormalizationQ))
    (hcheck : GramPEP.checkUpperCertQ c = true)
    (hobjective : c.objective = outputObjectiveQ N s unitRadiusNormalizationQ)
    {L : ℝ≥0} {R : ℝ} {f : E → ℝ} {g : E → E} {xStar x0 : E}
    (hfun : IsSmoothConvexFirstOrder L f g) (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hs : g xStar = 0) (hradius : ‖x0 - xStar‖ ^ 2 ≤ R ^ 2) :
    f (smoothState s L g x0 N) - f xStar ≤ (L : ℝ) * R ^ 2 * (c.bound : ℝ) := by
  rcases eq_or_lt_of_le hR with rfl | hRpos
  · have hnorm : ‖x0 - xStar‖ = 0 := by
      have hn := norm_nonneg (x0 - xStar)
      nlinarith
    have hx : x0 = xStar := sub_eq_zero.mp (norm_eq_zero.mp hnorm)
    calc
      f (smoothState s L g x0 N) - f xStar = 0 := by
        rw [hx, (stationary_trajectory s L hs N).1, sub_self]
      _ ≤ (L : ℝ) * (0 : ℝ) ^ 2 * (c.bound : ℝ) := by simp
  · exact certificate_upper_of_pos_radius c hcheck hobjective hfun hL hRpos hs hradius

/-- Generic accepted-certificate theorem with the exact initial distance. -/
theorem certificate_upper_exact_radius {N : ℕ} {s : ScheduleQ}
    (c : GramPEP.UpperCertQ (outputModelQ N s unitRadiusNormalizationQ))
    (hcheck : GramPEP.checkUpperCertQ c = true)
    (hobjective : c.objective = outputObjectiveQ N s unitRadiusNormalizationQ)
    {L : ℝ≥0} {f : E → ℝ} {g : E → E} {xStar x0 : E}
    (hfun : IsSmoothConvexFirstOrder L f g) (hL : 0 < (L : ℝ)) (hs : g xStar = 0) :
    f (smoothState s L g x0 N) - f xStar ≤
      (L : ℝ) * ‖x0 - xStar‖ ^ 2 * (c.bound : ℝ) :=
  certificate_upper c hcheck hobjective hfun hL (norm_nonneg _) hs (le_refl _)

/-- Analysis-facing scaled certificate soundness on any real Hilbert space. -/
theorem certificate_upper_analytic [CompleteSpace E] {N : ℕ} {s : ScheduleQ}
    (c : GramPEP.UpperCertQ (outputModelQ N s unitRadiusNormalizationQ))
    (hcheck : GramPEP.checkUpperCertQ c = true)
    (hobjective : c.objective = outputObjectiveQ N s unitRadiusNormalizationQ)
    {L : ℝ≥0} {R : ℝ} {f : E → ℝ} {g : E → E} {xStar x0 : E}
    (hfun : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hs : g xStar = 0) (hradius : ‖x0 - xStar‖ ^ 2 ≤ R ^ 2) :
    f (smoothState s L g x0 N) - f xStar ≤ (L : ℝ) * R ^ 2 * (c.bound : ℝ) :=
  certificate_upper c hcheck hobjective hfun.toFirstOrder hL hR hs hradius

/-- External implementations need only the reused physical run contract. -/
theorem certificate_upper_of_isSmoothRun {N : ℕ} {s : ScheduleQ}
    (c : GramPEP.UpperCertQ (outputModelQ N s unitRadiusNormalizationQ))
    (hcheck : GramPEP.checkUpperCertQ c = true)
    (hobjective : c.objective = outputObjectiveQ N s unitRadiusNormalizationQ)
    {L : ℝ≥0} {R : ℝ} {f : E → ℝ} {g : E → E} {xStar x0 : E} {x y : ℕ → E}
    (hfun : IsSmoothConvexFirstOrder L f g) (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hs : g xStar = 0) (hradius : ‖x0 - xStar‖ ^ 2 ≤ R ^ 2)
    (hrun : IsSmoothRun N s L g x0 x y) :
    f (x N) - f xStar ≤ (L : ℝ) * R ^ 2 * (c.bound : ℝ) := by
  rw [(eq_of_isSmoothRun hrun N (le_refl N)).1]
  exact certificate_upper c hcheck hobjective hfun hL hR hs hradius

end LeanPEP.ActualFunction.MomentumScaling
