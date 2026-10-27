import LeanPEP.ActualFunction.ProximalGradientRate
import LeanPEP.Profiles.ProximalGradientCertificateIdentity

/-!
# Positive-horizon proximal-gradient upper and tightness

The old actual-function bridge and old actual lower witness are unchanged.
C3B supplies exactly the missing all-horizon certificate acceptance theorem.
The normalized assumptions remain: unit smoothness/step/radius, real-valued
convex h, composite stationarity, and a supplied finite actual proximal run.
No prox existence or extended-real interpolation theorem is asserted.
-/

noncomputable section
namespace LeanPEP.ActualFunction.ProximalGradientRate

open Proximal
open LeanPEP.Profiles.ProximalGradientCertificate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- No checker-acceptance or coefficient-identity assumption remains. -/
theorem upper_all {n : ℕ}
    {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsOneSmoothConvexFirstOrder f g) (hh : ConvexOn ℝ Set.univ h)
    (hs : SubgradientAt h (-g xStar) xStar)
    (hrun : ProximalGradient.IsProxRun (n + 1) h g x)
    (hradius : ‖x 0 - xStar‖ ^ 2 ≤ 1) :
    (f (x (n + 1)) + h (x (n + 1))) - (f xStar + h xStar) ≤
      1 / (4 * ((n : ℝ) + 1)) :=
  upper_of_check (upperCertQ_check_all n) hf hh hs hrun hradius

/-- The actual analytic-function interface on any real Hilbert space. -/
theorem upper_analytic_all [CompleteSpace E] {n : ℕ}
    {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsOneSmoothConvexAnalytic f g) (hh : ConvexOn ℝ Set.univ h)
    (hs : SubgradientAt h (-g xStar) xStar)
    (hrun : ProximalGradient.IsProxRun (n + 1) h g x)
    (hradius : ‖x 0 - xStar‖ ^ 2 ≤ 1) :
    (f (x (n + 1)) + h (x (n + 1))) - (f xStar + h xStar) ≤
      1 / (4 * ((n : ℝ) + 1)) :=
  upper_analytic_of_check (upperCertQ_check_all n) hf hh hs hrun hradius

/-- Equivalent user-facing statement indexed by the POSITIVE step count T. -/
theorem upper_analytic_steps [CompleteSpace E] (T : ℕ) (hT : 0 < T)
    {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsOneSmoothConvexAnalytic f g) (hh : ConvexOn ℝ Set.univ h)
    (hs : SubgradientAt h (-g xStar) xStar)
    (hrun : ProximalGradient.IsProxRun T h g x)
    (hradius : ‖x 0 - xStar‖ ^ 2 ≤ 1) :
    (f (x T) + h (x T)) - (f xStar + h xStar) ≤ 1 / (4 * (T : ℝ)) := by
  cases T with
  | zero => omega
  | succ n =>
      simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
        (upper_analytic_all (n := n) hf hh hs hrun hradius)

/-- Exact finite value for every positive horizon in the ORIGINAL C2 model. -/
theorem finite_tight_all (n : ℕ) :
    IsGreatest (LeanPEP.Profiles.ProximalGradient.finiteValues n)
      (1 / (4 * ((n : ℝ) + 1))) := by
  simpa only [boundQ_cast] using finite_tight_of_check n (upperCertQ_check_all n)

/-- Exact actual value; membership uses the already verified explicit witness. -/
theorem analytic_tight_all (n : ℕ) :
    IsGreatest (ProximalGradient.oneDimensionalAnalyticValues n)
      (1 / (4 * ((n : ℝ) + 1))) := by
  simpa only [boundQ_cast] using analytic_tight_of_check n (upperCertQ_check_all n)

/-- Universal Hilbert upper plus one-dimensional actual attainment. -/
theorem analytic_upper_and_oneDimensional_tight_all [CompleteSpace E] (n : ℕ) :
    (∀ {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E},
      IsOneSmoothConvexAnalytic f g → ConvexOn ℝ Set.univ h →
      SubgradientAt h (-g xStar) xStar → ProximalGradient.IsProxRun (n + 1) h g x →
      ‖x 0 - xStar‖ ^ 2 ≤ 1 →
      (f (x (n + 1)) + h (x (n + 1))) - (f xStar + h xStar) ≤
        1 / (4 * ((n : ℝ) + 1))) ∧
      IsGreatest (ProximalGradient.oneDimensionalAnalyticValues n)
        (1 / (4 * ((n : ℝ) + 1))) := by
  exact ⟨fun hf hh hs hp hR => upper_analytic_all hf hh hs hp hR, analytic_tight_all n⟩

end LeanPEP.ActualFunction.ProximalGradientRate
