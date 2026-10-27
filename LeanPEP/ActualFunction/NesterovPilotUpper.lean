import LeanPEP.ActualFunction.MomentumActual
import LeanPEP.Profiles.NesterovPilot

/-!
# Four-step actual-function Nesterov pilot upper bound

The bound is transported from the kernel-verified B1 certificate through the
GENERIC profile and momentum bridges, with no change to the certificate or
Gram checker.  For the rational schedule `step(k)=1`, `momentum(k)=k/(k+3)`,
the conclusion is `f(x_4)-f(xStar) <= 1/21` under unit initial radius and actual
normalized smooth-convex assumptions on any real Hilbert space.

Only a universal upper bound is asserted here.  B1's finite primal and finite
`IsGreatest` do not by themselves prove actual-function lower attainment.
-/

namespace LeanPEP.ActualFunction.NesterovPilotUpper

open LeanPEP.Profiles.GramCompilation
open LeanPEP.Profiles.NesterovPilot

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual state iterate of the rational schedule used by the B1 formulation. -/
noncomputable def iterate (g : E → E) (x0 : E) (k : ℕ) : E :=
  MomentumActual.state nesterovScheduleQ g x0 k

/-- The pilot's actual query sequence. -/
noncomputable def query (g : E → E) (x0 : E) (k : ℕ) : E :=
  MomentumActual.query nesterovScheduleQ g x0 k

@[simp] theorem iterate_zero (g : E → E) (x0 : E) : iterate g x0 0 = x0 := rfl

@[simp] theorem query_zero (g : E → E) (x0 : E) : query g x0 0 = x0 := rfl

/-- Actual unit gradient step evaluated at the query point. -/
theorem iterate_succ (g : E → E) (x0 : E) (k : ℕ) :
    iterate g x0 (k + 1) = query g x0 k - g (query g x0 k) := by
  simpa [iterate, query, nesterovScheduleQ] using
    MomentumActual.state_succ nesterovScheduleQ g x0 k

/-- The exact real momentum coefficient is the cast of the rational schedule. -/
theorem query_succ (g : E → E) (x0 : E) (k : ℕ) :
    query g x0 (k + 1) = iterate g x0 (k + 1) +
      ((k : ℝ) / ((k : ℝ) + 3)) • (iterate g x0 (k + 1) - iterate g x0 k) := by
  simpa [iterate, query, nesterovScheduleQ] using
    MomentumActual.query_succ nesterovScheduleQ g x0 k

/-- First-order version; the ambient inner-product space need not be complete. -/
theorem upper_firstOrder {f : E → ℝ} {g : E → E} {xStar x0 : E}
    (hfun : IsOneSmoothConvexFirstOrder f g)
    (hstationary : g xStar = 0) (hradius : ‖x0 - xStar‖ ^ 2 ≤ 1) :
    f (iterate g x0 4) - f xStar ≤ (1 : ℝ) / 21 := by
  have hbound := MomentumActual.certificate_upper
    (N := 4) (s := nesterovScheduleQ) (normalization := unitRadiusNormalizationQ)
    pilotUpperCertQ pilotUpperCertQ_check rfl hfun hstationary
    (by simpa [unitRadiusNormalizationQ] using hradius)
  simpa [iterate, pilotUpperCertQ] using hbound

/-- Universal actual-function upper theorem on an arbitrary real Hilbert space. -/
theorem upper_analytic [CompleteSpace E]
    {f : E → ℝ} {g : E → E} {xStar x0 : E}
    (hfun : IsOneSmoothConvexAnalytic f g)
    (hstationary : g xStar = 0) (hradius : ‖x0 - xStar‖ ^ 2 ≤ 1) :
    f (iterate g x0 4) - f xStar ≤ (1 : ℝ) / 21 :=
  upper_firstOrder hfun.toFirstOrder hstationary hradius

/-- The same upper theorem for any external run of the two-sequence recurrence. -/
theorem upper_analytic_of_isRun [CompleteSpace E]
    {f : E → ℝ} {g : E → E} {xStar x0 : E} {x y : ℕ → E}
    (hfun : IsOneSmoothConvexAnalytic f g)
    (hstationary : g xStar = 0) (hradius : ‖x0 - xStar‖ ^ 2 ≤ 1)
    (hrun : MomentumActual.IsRun 4 nesterovScheduleQ g x0 x y) :
    f (x 4) - f xStar ≤ (1 : ℝ) / 21 := by
  rw [(MomentumActual.eq_of_isRun hrun 4 (le_refl 4)).1]
  exact upper_analytic hfun hstationary hradius

end LeanPEP.ActualFunction.NesterovPilotUpper
