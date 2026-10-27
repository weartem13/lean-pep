import LeanPEP.ActualFunction.ProximalGradientWitness

/-!
# Accepted certificates plus explicit actual lower witnesses

C3A closes finite and actual tightness for T=1,2,3,4 by calling the C2 bridge.
For arbitrary T it exports only an explicitly CONDITIONAL upper/tightness
interface: the certificate acceptance premise is not discharged here.
-/

noncomputable section
namespace LeanPEP.ActualFunction.ProximalGradientRate

open Proximal
open LeanPEP.Profiles.ProximalGradientCertificate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem upper_of_check {n : ℕ}
    (hc : GramPEP.checkUpperCertQ (upperCertQ n) = true)
    {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsOneSmoothConvexFirstOrder f g) (hh : ConvexOn ℝ Set.univ h)
    (hs : SubgradientAt h (-g xStar) xStar)
    (hrun : ProximalGradient.IsProxRun (n + 1) h g x)
    (hradius : ‖x 0 - xStar‖ ^ 2 ≤ 1) :
    (f (x (n + 1)) + h (x (n + 1))) - (f xStar + h xStar) ≤
      1 / (4 * ((n : ℝ) + 1)) := by
  have hb := ProximalGradient.certificate_upper_of_prox (upperCertQ n)
    hc rfl rfl hf hh hs hrun hradius
  change (f (x (n + 1)) + h (x (n + 1))) - (f xStar + h xStar) ≤ (boundQ n : ℝ) at hb
  simpa only [boundQ_cast] using hb

theorem upper_analytic_of_check [CompleteSpace E] {n : ℕ}
    (hc : GramPEP.checkUpperCertQ (upperCertQ n) = true)
    {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsOneSmoothConvexAnalytic f g) (hh : ConvexOn ℝ Set.univ h)
    (hs : SubgradientAt h (-g xStar) xStar)
    (hrun : ProximalGradient.IsProxRun (n + 1) h g x)
    (hradius : ‖x 0 - xStar‖ ^ 2 ≤ 1) :
    (f (x (n + 1)) + h (x (n + 1))) - (f xStar + h xStar) ≤
      1 / (4 * ((n : ℝ) + 1)) :=
  upper_of_check hc hf.toFirstOrder hh hs hrun hradius

theorem finite_tight_of_check (n : ℕ)
    (hc : GramPEP.checkUpperCertQ (upperCertQ n) = true) :
    IsGreatest (LeanPEP.Profiles.ProximalGradient.finiteValues n) (boundQ n : ℝ) := by
  constructor
  · exact ProximalGradientWitness.bound_mem_finiteValues n
  · rintro r ⟨d, hp, hconstraints, hv⟩
    rw [← hv]
    exact LeanPEP.Profiles.ProximalGradient.certificate_upper
      (upperCertQ n) hc rfl rfl d hp hconstraints

theorem analytic_tight_of_check (n : ℕ)
    (hc : GramPEP.checkUpperCertQ (upperCertQ n) = true) :
    IsGreatest (ProximalGradient.oneDimensionalAnalyticValues n) (boundQ n : ℝ) := by
  constructor
  · exact ProximalGradientWitness.bound_mem_analyticValues n
  · rintro r ⟨f, h, g, xStar, x, hf, hh, hs, hp, hR, hv⟩
    rw [← hv, boundQ_cast]
    exact upper_analytic_of_check hc hf hh hs hp hR

/-- No extra checker premise remains at these four horizons. -/
theorem upper_analytic_small [CompleteSpace E] (n : ℕ) (hn : n ≤ 3)
    {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsOneSmoothConvexAnalytic f g) (hh : ConvexOn ℝ Set.univ h)
    (hs : SubgradientAt h (-g xStar) xStar)
    (hrun : ProximalGradient.IsProxRun (n + 1) h g x)
    (hradius : ‖x 0 - xStar‖ ^ 2 ≤ 1) :
    (f (x (n + 1)) + h (x (n + 1))) - (f xStar + h xStar) ≤
      1 / (4 * ((n : ℝ) + 1)) :=
  upper_analytic_of_check (upperCertQ_check_small n hn) hf hh hs hrun hradius

theorem finite_tight_small (n : ℕ) (hn : n ≤ 3) :
    IsGreatest (LeanPEP.Profiles.ProximalGradient.finiteValues n)
      (1 / (4 * ((n : ℝ) + 1))) := by
  simpa only [boundQ_cast] using finite_tight_of_check n (upperCertQ_check_small n hn)

theorem analytic_tight_small (n : ℕ) (hn : n ≤ 3) :
    IsGreatest (ProximalGradient.oneDimensionalAnalyticValues n)
      (1 / (4 * ((n : ℝ) + 1))) := by
  simpa only [boundQ_cast] using analytic_tight_of_check n (upperCertQ_check_small n hn)

theorem twoStep_analytic_tight :
    IsGreatest (ProximalGradient.oneDimensionalAnalyticValues 1) ((1 : ℝ) / 8) := by
  convert analytic_tight_small 1 (by omega) using 1 <;> norm_num

theorem fourStep_analytic_tight :
    IsGreatest (ProximalGradient.oneDimensionalAnalyticValues 3) ((1 : ℝ) / 16) := by
  convert analytic_tight_small 3 (by omega) using 1 <;> norm_num

theorem analytic_upper_and_oneDimensional_tight [CompleteSpace E]
    (n : ℕ) (hn : n ≤ 3) :
    (∀ {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E},
      IsOneSmoothConvexAnalytic f g → ConvexOn ℝ Set.univ h →
      SubgradientAt h (-g xStar) xStar → ProximalGradient.IsProxRun (n + 1) h g x →
      ‖x 0 - xStar‖ ^ 2 ≤ 1 →
      (f (x (n + 1)) + h (x (n + 1))) - (f xStar + h xStar) ≤
        1 / (4 * ((n : ℝ) + 1))) ∧
      IsGreatest (ProximalGradient.oneDimensionalAnalyticValues n)
        (1 / (4 * ((n : ℝ) + 1))) := by
  exact ⟨fun hf hh hs hp hR => upper_analytic_small n hn hf hh hs hp hR,
    analytic_tight_small n hn⟩

end LeanPEP.ActualFunction.ProximalGradientRate
