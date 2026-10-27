import LeanPEP.ActualFunction.ProximalGradientScalingCore
import LeanPEP.ActualFunction.ProximalScaling
import LeanPEP.ActualFunction.ProximalGradientRateAll

/-!
# General L and R for the original proximal-gradient certificate

Physical runs have step size 1/L and solve the ordinary h-prox subproblem
with quadratic coefficient L/2. They are equivalent, for positive L,R, to
unit runs of the existing normalized function/gradient pair. The accepted
C3A certificate, C2 compiler, and C3B all-horizon identity are reused intact.
The R=0 branch follows from composite stationarity and proximal uniqueness;
it does not assume g(xStar)=0 or divide by R.
-/

noncomputable section
open scoped NNReal
namespace LeanPEP.ActualFunction.ProximalGradientScaling

open Proximal ProximalScaling SmoothScaling
open LeanPEP.Profiles.ProximalGradientCertificate (boundQ_cast upperCertQ upperCertQ_check_all)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- General smoothness and radius, with no certificate-acceptance hypothesis. -/
theorem upper_firstOrder {n : ℕ} {L : ℝ≥0} {R : ℝ} {f h : E → ℝ} {g : E → E}
    {xStar : E} {x : ℕ → E} (hf : IsSmoothConvexFirstOrder L f g)
    (hh : ConvexOn ℝ Set.univ h) (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hs : SubgradientAt h (-g xStar) xStar) (hrun : IsSmoothProxRun (n+1) L h g x)
    (hradius : ‖x 0-xStar‖^2 ≤ R^2) :
    f (x (n+1)) + h (x (n+1)) - (f xStar + h xStar) ≤
      (L : ℝ)*R^2/(4*((n : ℝ)+1)) := by
  have hb := certificate_upper (upperCertQ n) (upperCertQ_check_all n) rfl rfl
    hf hh hL hR hs hrun hradius
  change _ ≤ (L : ℝ)*R^2*(LeanPEP.Profiles.ProximalGradientCertificate.boundQ n : ℝ) at hb
  rw [boundQ_cast] at hb
  simpa only [div_eq_mul_inv, one_mul] using hb

theorem upper_analytic [CompleteSpace E] {n : ℕ} {L : ℝ≥0} {R : ℝ}
    {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsSmoothConvexAnalytic L f g) (hh : ConvexOn ℝ Set.univ h)
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) (hs : SubgradientAt h (-g xStar) xStar)
    (hrun : IsSmoothProxRun (n+1) L h g x) (hradius : ‖x 0-xStar‖^2 ≤ R^2) :
    f (x (n+1)) + h (x (n+1)) - (f xStar + h xStar) ≤
      (L : ℝ)*R^2/(4*((n : ℝ)+1)) :=
  upper_firstOrder hf.toFirstOrder hh hL hR hs hrun hradius

/-- User-facing physical step count T; zero steps are deliberately excluded. -/
theorem upper_analytic_steps [CompleteSpace E] (T : ℕ) (hT : 0 < T)
    {L : ℝ≥0} {R : ℝ} {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsSmoothConvexAnalytic L f g) (hh : ConvexOn ℝ Set.univ h)
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) (hs : SubgradientAt h (-g xStar) xStar)
    (hrun : IsSmoothProxRun T L h g x) (hradius : ‖x 0-xStar‖^2 ≤ R^2) :
    f (x T) + h (x T) - (f xStar + h xStar) ≤ (L : ℝ)*R^2/(4*(T : ℝ)) := by
  cases T with
  | zero => omega
  | succ n =>
      simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
        (upper_analytic (n := n) hf hh hL hR hs hrun hradius)

theorem upper_analytic_exact_radius [CompleteSpace E] {n : ℕ} {L : ℝ≥0}
    {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsSmoothConvexAnalytic L f g) (hh : ConvexOn ℝ Set.univ h)
    (hL : 0 < (L : ℝ)) (hs : SubgradientAt h (-g xStar) xStar)
    (hrun : IsSmoothProxRun (n+1) L h g x) :
    f (x (n+1)) + h (x (n+1)) - (f xStar + h xStar) ≤
      (L : ℝ)*‖x 0-xStar‖^2/(4*((n : ℝ)+1)) :=
  upper_analytic hf hh hL (norm_nonneg _) hs hrun (le_refl _)

/-- Actual physical functions/runs only. There are no Gram/checker premises. -/
def oneDimensionalAnalyticValues (n : ℕ) (L : ℝ≥0) (R : ℝ) : Set ℝ :=
  {r | ∃ (f h g : ℝ → ℝ) (xStar : ℝ) (x : ℕ → ℝ),
    IsSmoothConvexAnalytic L f g ∧ ConvexOn ℝ Set.univ h ∧
    SubgradientAt h (-g xStar) xStar ∧ IsSmoothProxRun (n+1) L h g x ∧
    ‖x 0-xStar‖^2 ≤ R^2 ∧ f (x (n+1)) + h (x (n+1)) - (f xStar + h xStar) = r}

end LeanPEP.ActualFunction.ProximalGradientScaling
