import LeanPEP.ActualFunction.MomentumScaling
import LeanPEP.ActualFunction.NesterovPilotUpper
import LeanPEP.Profiles.NesterovPilot

/-!
# General-L,R actual upper theorem for the four-step Nesterov pilot

The physical recursion has step size `1/L` and momentum `k/(k+3)`.  The upper
bound `L R² / 21` reuses the B1 rational certificate through the generic B4
scaling theorem.  No new model or certificate is constructed here.
-/

open scoped NNReal

namespace LeanPEP.ActualFunction.NesterovPilotScaling

open LeanPEP.Profiles.NesterovPilot

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def iterate (L : ℝ≥0) (g : E → E) (x0 : E) (k : ℕ) : E :=
  MomentumScaling.smoothState nesterovScheduleQ L g x0 k

noncomputable def query (L : ℝ≥0) (g : E → E) (x0 : E) (k : ℕ) : E :=
  MomentumScaling.smoothQuery nesterovScheduleQ L g x0 k

@[simp] theorem iterate_zero (L : ℝ≥0) (g : E → E) (x0 : E) :
    iterate L g x0 0 = x0 := rfl

@[simp] theorem query_zero (L : ℝ≥0) (g : E → E) (x0 : E) :
    query L g x0 0 = x0 := rfl

theorem iterate_succ (L : ℝ≥0) (g : E → E) (x0 : E) (k : ℕ) :
    iterate L g x0 (k + 1) = query L g x0 k - (L : ℝ)⁻¹ • g (query L g x0 k) := by
  simpa [iterate, query, nesterovScheduleQ, one_div] using
    MomentumScaling.smoothState_succ nesterovScheduleQ L g x0 k

theorem query_succ (L : ℝ≥0) (g : E → E) (x0 : E) (k : ℕ) :
    query L g x0 (k + 1) = iterate L g x0 (k + 1) +
      ((k : ℝ) / ((k : ℝ) + 3)) • (iterate L g x0 (k + 1) - iterate L g x0 k) := by
  simpa [iterate, query, nesterovScheduleQ] using
    MomentumScaling.smoothQuery_succ nesterovScheduleQ L g x0 k

/-- At `L = 1` the actual state is exactly the already verified B2 state. -/
@[simp] theorem iterate_one (g : E → E) (x0 : E) (k : ℕ) :
    iterate 1 g x0 k = NesterovPilotUpper.iterate g x0 k := by
  have hgradient : ParametricGDScaling.normalizedGradient (1 : ℝ≥0) g = g := by
    funext x
    simp [ParametricGDScaling.normalizedGradient]
  change MomentumActual.state nesterovScheduleQ
      (ParametricGDScaling.normalizedGradient (1 : ℝ≥0) g) x0 k =
    MomentumActual.state nesterovScheduleQ g x0 k
  rw [hgradient]

@[simp] theorem query_one (g : E → E) (x0 : E) (k : ℕ) :
    query 1 g x0 k = NesterovPilotUpper.query g x0 k := by
  have hgradient : ParametricGDScaling.normalizedGradient (1 : ℝ≥0) g = g := by
    funext x
    simp [ParametricGDScaling.normalizedGradient]
  change MomentumActual.query nesterovScheduleQ
      (ParametricGDScaling.normalizedGradient (1 : ℝ≥0) g) x0 k =
    MomentumActual.query nesterovScheduleQ g x0 k
  rw [hgradient]

/-- Four-step upper theorem for a general smooth first-order pair. -/
theorem upper_firstOrder {L : ℝ≥0} {R : ℝ} {f : E → ℝ} {g : E → E} {xStar x0 : E}
    (hfun : IsSmoothConvexFirstOrder L f g) (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hs : g xStar = 0) (hradius : ‖x0 - xStar‖ ^ 2 ≤ R ^ 2) :
    f (iterate L g x0 4) - f xStar ≤ (L : ℝ) * R ^ 2 / 21 := by
  have h := MomentumScaling.certificate_upper
    pilotUpperCertQ pilotUpperCertQ_check rfl hfun hL hR hs hradius
  simpa [iterate, pilotUpperCertQ, div_eq_mul_inv] using h

/-- Universal four-step actual upper theorem, including zero radius. -/
theorem upper_analytic [CompleteSpace E]
    {L : ℝ≥0} {R : ℝ} {f : E → ℝ} {g : E → E} {xStar x0 : E}
    (hfun : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hs : g xStar = 0) (hradius : ‖x0 - xStar‖ ^ 2 ≤ R ^ 2) :
    f (iterate L g x0 4) - f xStar ≤ (L : ℝ) * R ^ 2 / 21 :=
  upper_firstOrder hfun.toFirstOrder hL hR hs hradius

/-- Exact-distance form needs no separately chosen radius. -/
theorem upper_analytic_exact_radius [CompleteSpace E]
    {L : ℝ≥0} {f : E → ℝ} {g : E → E} {xStar x0 : E}
    (hfun : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ)) (hs : g xStar = 0) :
    f (iterate L g x0 4) - f xStar ≤ (L : ℝ) * ‖x0 - xStar‖ ^ 2 / 21 :=
  upper_analytic hfun hL (norm_nonneg _) hs (le_refl _)

/-- Actual upper theorem for any external implementation of the physical run. -/
theorem upper_analytic_of_isSmoothRun [CompleteSpace E]
    {L : ℝ≥0} {R : ℝ} {f : E → ℝ} {g : E → E} {xStar x0 : E} {x y : ℕ → E}
    (hfun : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hs : g xStar = 0) (hradius : ‖x0 - xStar‖ ^ 2 ≤ R ^ 2)
    (hrun : MomentumScaling.IsSmoothRun 4 nesterovScheduleQ L g x0 x y) :
    f (x 4) - f xStar ≤ (L : ℝ) * R ^ 2 / 21 := by
  rw [(MomentumScaling.eq_of_isSmoothRun hrun 4 (le_refl 4)).1]
  exact upper_analytic hfun hL hR hs hradius

end LeanPEP.ActualFunction.NesterovPilotScaling
