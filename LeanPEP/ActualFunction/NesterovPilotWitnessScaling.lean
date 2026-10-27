import LeanPEP.ActualFunction.NesterovPilotScaling
import LeanPEP.ActualFunction.NesterovPilotWitness
import LeanPEP.ActualFunction.HuberWitnessScaling

/-!
# General-L,R actual lower witness and tightness for the four-step pilot

The explicit pair is `F(x)=L H_(2R/21)(x)`, `G(x)=L min(x,2R/21)`.
The actual physical state and query are R times their B3 trajectories, even
when R is zero.  The final state attains `L R² / 21`; the unused final query
has gap `2 L R² / 49`.  Tightness quantifies actual functions, not finite Gram
feasible data.  The horizon remains four, and `L` is strictly positive.
-/

noncomputable section
open scoped NNReal

namespace LeanPEP.ActualFunction

namespace HuberWitness

/-- Expose arbitrary-threshold amplitude scaling from the already verified
Huber family.  At index zero its threshold is one, so radius `a` represents
exactly `H_a`.  This reuses regularity, not any GD trajectory or rate. -/
theorem amplitudeScaled_analytic (L : ℝ≥0) (a : ℝ) :
    IsSmoothConvexAnalytic L
      (fun x : ℝ => (L : ℝ) * huberFunction a x)
      (fun x : ℝ => (L : ℝ) * huberGradient a x) := by
  have hfunction : scaledWitnessFunction 0 L a =
      (fun x : ℝ => (L : ℝ) * huberFunction a x) := by
    funext x
    simp [scaledWitnessFunction, scaledThreshold, threshold]
  have hgradient : scaledWitnessGradient 0 L a =
      (fun x : ℝ => (L : ℝ) * huberGradient a x) := by
    funext x
    simp [scaledWitnessGradient, scaledThreshold, threshold]
  have hregularity := scaledWitness_analytic 0 L a
  rw [hfunction, hgradient] at hregularity
  exact hregularity

end HuberWitness

namespace NesterovPilotWitnessScaling

open LeanPEP.Profiles.NesterovPilot (nesterovScheduleQ)

def scaledThreshold (R : ℝ) : ℝ := R * NesterovPilotWitness.threshold

def scaledWitnessFunction (L : ℝ≥0) (R x : ℝ) : ℝ :=
  (L : ℝ) * HuberWitness.huberFunction (scaledThreshold R) x

def scaledWitnessGradient (L : ℝ≥0) (R x : ℝ) : ℝ :=
  (L : ℝ) * HuberWitness.huberGradient (scaledThreshold R) x

theorem scaledThreshold_nonneg {R : ℝ} (hR : 0 ≤ R) : 0 ≤ scaledThreshold R :=
  mul_nonneg hR (le_of_lt NesterovPilotWitness.threshold_pos)

/-- Genuine gradient, convexity and L-Lipschitz regularity of the explicit pair. -/
theorem analytic (L : ℝ≥0) (R : ℝ) :
    IsSmoothConvexAnalytic L (scaledWitnessFunction L R) (scaledWitnessGradient L R) :=
  HuberWitness.amplitudeScaled_analytic L (scaledThreshold R)

theorem firstOrder (L : ℝ≥0) (R : ℝ) :
    IsSmoothConvexFirstOrder L (scaledWitnessFunction L R) (scaledWitnessGradient L R) :=
  (analytic L R).toFirstOrder

@[simp] theorem scaledWitnessFunction_zero (L : ℝ≥0) {R : ℝ} (hR : 0 ≤ R) :
    scaledWitnessFunction L R 0 = 0 := by
  simp [scaledWitnessFunction, HuberWitness.huberFunction_zero (scaledThreshold_nonneg hR)]

@[simp] theorem scaledWitnessGradient_zero (L : ℝ≥0) {R : ℝ} (hR : 0 ≤ R) :
    scaledWitnessGradient L R 0 = 0 := by
  simp [scaledWitnessGradient, HuberWitness.huberGradient_zero (scaledThreshold_nonneg hR)]

theorem zero_isGlobalMin (L : ℝ≥0) {R : ℝ} (hR : 0 ≤ R) (x : ℝ) :
    scaledWitnessFunction L R 0 ≤ scaledWitnessFunction L R x :=
  mul_le_mul_of_nonneg_left
    (HuberWitness.zero_isGlobalMin (scaledThreshold_nonneg hR) x) L.coe_nonneg

/-- Quadratic scaling of the actual function; includes the singular scale R=0. -/
theorem scaledWitnessFunction_scale_point (L : ℝ≥0) {R x : ℝ} (hR : 0 ≤ R) :
    scaledWitnessFunction L R (R * x) =
      (L : ℝ) * R ^ 2 * NesterovPilotWitness.witnessFunction x := by
  unfold scaledWitnessFunction scaledThreshold NesterovPilotWitness.witnessFunction
  rw [HuberWitness.huberFunction_scale hR]
  ring

theorem scaledWitnessGradient_scale_point (L : ℝ≥0) {R x : ℝ} (hR : 0 ≤ R) :
    scaledWitnessGradient L R (R * x) =
      (L : ℝ) * R * NesterovPilotWitness.witnessGradient x := by
  unfold scaledWitnessGradient scaledThreshold NesterovPilotWitness.witnessGradient
  rw [HuberWitness.huberGradient_scale hR]
  ring

/-- The full physical run is the spatially scaled B3 run, at every index.
Unlike coordinate normalization, this forward transport also admits R=0. -/
theorem scaled_trajectory {L : ℝ≥0} {R : ℝ}
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) (k : ℕ) :
    NesterovPilotScaling.iterate L (scaledWitnessGradient L R) R k =
        R * NesterovPilotUpper.iterate NesterovPilotWitness.witnessGradient 1 k ∧
      NesterovPilotScaling.query L (scaledWitnessGradient L R) R k =
        R * NesterovPilotUpper.query NesterovPilotWitness.witnessGradient 1 k := by
  have hfields : ∀ z : ℝ,
      ParametricGDScaling.normalizedGradient L (scaledWitnessGradient L R)
        (SmoothScaling.scaledPoint 0 R z) = R • NesterovPilotWitness.witnessGradient z := by
    intro z
    change (L : ℝ)⁻¹ * scaledWitnessGradient L R (0 + R * z) =
      R * NesterovPilotWitness.witnessGradient z
    rw [zero_add, scaledWitnessGradient_scale_point L hR]
    field_simp [ne_of_gt hL] <;> ring
  have h := MomentumScaling.affine_trajectory nesterovScheduleQ
    NesterovPilotWitness.witnessGradient
    (ParametricGDScaling.normalizedGradient L (scaledWitnessGradient L R))
    0 R 1 hfields k
  simpa [NesterovPilotScaling.iterate, NesterovPilotScaling.query,
    MomentumScaling.smoothState, MomentumScaling.smoothQuery,
    NesterovPilotUpper.iterate, NesterovPilotUpper.query,
    SmoothScaling.scaledPoint, smul_eq_mul] using h

theorem iterate_four {L : ℝ≥0} {R : ℝ} (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) :
    NesterovPilotScaling.iterate L (scaledWitnessGradient L R) R 4 = R * ((23 : ℝ) / 42) := by
  rw [(scaled_trajectory hL hR 4).1, NesterovPilotWitness.iterate_four]

theorem query_four {L : ℝ≥0} {R : ℝ} (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) :
    NesterovPilotScaling.query L (scaledWitnessGradient L R) R 4 = R * ((10 : ℝ) / 21) := by
  rw [(scaled_trajectory hL hR 4).2, NesterovPilotWitness.query_four]

/-- At positive radius the final state and final query are distinct.
No such distinction is claimed for R=0, when both are zero. -/
theorem terminal_state_ne_query {L : ℝ≥0} {R : ℝ}
    (hL : 0 < (L : ℝ)) (hR : 0 < R) :
    NesterovPilotScaling.iterate L (scaledWitnessGradient L R) R 4 ≠
      NesterovPilotScaling.query L (scaledWitnessGradient L R) R 4 := by
  rw [iterate_four hL (le_of_lt hR), query_four hL (le_of_lt hR)]
  intro heq
  nlinarith

/-- Exact actual-function lower attainment, including zero radius. -/
theorem attains {L : ℝ≥0} {R : ℝ} (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) :
    scaledWitnessFunction L R
        (NesterovPilotScaling.iterate L (scaledWitnessGradient L R) R 4) -
      scaledWitnessFunction L R 0 = (L : ℝ) * R ^ 2 / 21 := by
  have hbase := NesterovPilotWitness.attains
  rw [NesterovPilotWitness.witnessFunction_zero, sub_zero] at hbase
  rw [(scaled_trajectory hL hR 4).1, scaledWitnessFunction_scale_point L hR,
    scaledWitnessFunction_zero L hR, hbase] <;> ring

theorem final_query_gap {L : ℝ≥0} {R : ℝ} (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) :
    scaledWitnessFunction L R
        (NesterovPilotScaling.query L (scaledWitnessGradient L R) R 4) -
      scaledWitnessFunction L R 0 = 2 * (L : ℝ) * R ^ 2 / 49 := by
  have hbase := NesterovPilotWitness.final_query_gap
  rw [NesterovPilotWitness.witnessFunction_zero, sub_zero] at hbase
  rw [(scaled_trajectory hL hR 4).2, scaledWitnessFunction_scale_point L hR,
    scaledWitnessFunction_zero L hR, hbase] <;> ring

theorem zeroRadius_trajectory {L : ℝ≥0} (hL : 0 < (L : ℝ)) (k : ℕ) :
    NesterovPilotScaling.iterate L (scaledWitnessGradient L 0) 0 k = 0 ∧
      NesterovPilotScaling.query L (scaledWitnessGradient L 0) 0 k = 0 := by
  simpa using scaled_trajectory hL (le_refl (0 : ℝ)) k

theorem attains_of_isSmoothRun {L : ℝ≥0} {R : ℝ}
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) {x y : ℕ → ℝ}
    (hrun : MomentumScaling.IsSmoothRun 4 nesterovScheduleQ L
      (scaledWitnessGradient L R) R x y) :
    scaledWitnessFunction L R (x 4) - scaledWitnessFunction L R 0 =
      (L : ℝ) * R ^ 2 / 21 := by
  rw [(MomentumScaling.eq_of_isSmoothRun hrun 4 (le_refl 4)).1]
  exact attains hL hR

/-- Actual lower-witness obligations, independent of finite primal feasibility. -/
theorem analytic_lower_witness {L : ℝ≥0} {R : ℝ}
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) :
    IsSmoothConvexAnalytic L (scaledWitnessFunction L R) (scaledWitnessGradient L R) ∧
      scaledWitnessGradient L R 0 = 0 ∧
      (∀ x : ℝ, scaledWitnessFunction L R 0 ≤ scaledWitnessFunction L R x) ∧
      ‖R - (0 : ℝ)‖ ^ 2 ≤ R ^ 2 ∧
      scaledWitnessFunction L R
          (NesterovPilotScaling.iterate L (scaledWitnessGradient L R) R 4) -
        scaledWitnessFunction L R 0 = (L : ℝ) * R ^ 2 / 21 := by
  refine ⟨analytic L R, scaledWitnessGradient_zero L hR, zero_isGlobalMin L hR, ?_,
    attains hL hR⟩
  simp [Real.norm_eq_abs, sq_abs]

/-- Performance set of actual one-dimensional L-smooth convex functions and
physical step-size-1/L runs.  No Gram-feasibility assumption occurs here. -/
def oneDimensionalAnalyticValues (L : ℝ≥0) (R : ℝ) : Set ℝ :=
  { value | ∃ (f g : ℝ → ℝ) (xStar x0 : ℝ),
      IsSmoothConvexAnalytic L f g ∧
      g xStar = 0 ∧
      ‖x0 - xStar‖ ^ 2 ≤ R ^ 2 ∧
      f (NesterovPilotScaling.iterate L g x0 4) - f xStar = value }

theorem bound_mem_oneDimensionalAnalyticValues {L : ℝ≥0} {R : ℝ}
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) :
    (L : ℝ) * R ^ 2 / 21 ∈ oneDimensionalAnalyticValues L R := by
  refine ⟨scaledWitnessFunction L R, scaledWitnessGradient L R, 0, R,
    analytic L R, scaledWitnessGradient_zero L hR, ?_, attains hL hR⟩
  simp [Real.norm_eq_abs, sq_abs]

/-- Exact worst-case value in the actual one-dimensional function class. -/
theorem oneDimensional_analytic_tight {L : ℝ≥0} {R : ℝ}
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) :
    IsGreatest (oneDimensionalAnalyticValues L R) ((L : ℝ) * R ^ 2 / 21) := by
  constructor
  · exact bound_mem_oneDimensionalAnalyticValues hL hR
  · intro value hvalue
    rcases hvalue with ⟨f, g, xStar, x0, hfun, hs, hradius, hattain⟩
    rw [← hattain]
    exact NesterovPilotScaling.upper_analytic hfun hL hR hs hradius

/-- Arbitrary real Hilbert-space upper bound and one-dimensional attainment.
This does not define a single cross-universe supremum object. -/
theorem analytic_upper_and_oneDimensional_tight
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {L : ℝ≥0} {R : ℝ} (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) :
    (∀ {f : E → ℝ} {g : E → E} {xStar x0 : E},
      IsSmoothConvexAnalytic L f g →
      g xStar = 0 → ‖x0 - xStar‖ ^ 2 ≤ R ^ 2 →
      f (NesterovPilotScaling.iterate L g x0 4) - f xStar ≤ (L : ℝ) * R ^ 2 / 21) ∧
      IsGreatest (oneDimensionalAnalyticValues L R) ((L : ℝ) * R ^ 2 / 21) := by
  constructor
  · intro f g xStar x0 hfun hs hradius
    exact NesterovPilotScaling.upper_analytic hfun hL hR hs hradius
  · exact oneDimensional_analytic_tight hL hR

end NesterovPilotWitnessScaling
end LeanPEP.ActualFunction
