import LeanPEP.GramPEP.FactorReplacement
import LeanPEP.Imported.PSDSynthesized
import LeanPEP.ActualFunction.ProximalGradientMinimizer

/-!
# D1: exact synthesized dual factors reconnect to the existing actual upper bound

The producer does not control the mathematical target. Concrete imported
matrices are equated to the original closed-form dual matrix. The generic
replacement theorem retains the model, multipliers, bound and identity.
This is a different factor representation of known certificates, not a new rate
or a live PEPit capture, and not a replacement for source-formulation auditing.
-/

noncomputable section
open scoped NNReal
namespace LeanPEP.ActualFunction.PSDSynthesisApplications

open LeanPEP.GramPEP
open LeanPEP.Profiles.ProximalGradientCertificate
open LeanPEP.Imported

/-- Explicit target binding for a one-step composite certificate. -/
theorem pg_one_matrix_binding :
    PSDSynthesized.PGDualOne.matrixQ = (upperCertQ 0).dualMatrix := by
  apply (checkGramEqQ_eq_true_iff _ _).mp
  decide +kernel

/-- Explicit target binding for a two-step composite certificate. -/
theorem pg_two_matrix_binding :
    PSDSynthesized.PGDualTwo.matrixQ = (upperCertQ 1).dualMatrix := by
  apply (checkGramEqQ_eq_true_iff _ _).mp
  decide +kernel

theorem pg_one_factor_check :
    checkPSDFactorQ (upperCertQ 0).dualMatrix PSDSynthesized.PGDualOne.factorQ = true := by
  rw [← pg_one_matrix_binding]
  exact PSDSynthesized.PGDualOne.factor_check

theorem pg_two_factor_check :
    checkPSDFactorQ (upperCertQ 1).dualMatrix PSDSynthesized.PGDualTwo.factorQ = true := by
  rw [← pg_two_matrix_binding]
  exact PSDSynthesized.PGDualTwo.factor_check

theorem pg_one_upper_check :
    checkUpperCertQ ((upperCertQ 0).withDualFactor PSDSynthesized.PGDualOne.factorQ) = true :=
  checkUpperCertQ_withDualFactor (upperCertQ 0) PSDSynthesized.PGDualOne.factorQ (upperCertQ_check_all 0) pg_one_factor_check

theorem pg_two_upper_check :
    checkUpperCertQ ((upperCertQ 1).withDualFactor PSDSynthesized.PGDualTwo.factorQ) = true :=
  checkUpperCertQ_withDualFactor (upperCertQ 1) PSDSynthesized.PGDualTwo.factorQ (upperCertQ_check_all 1) pg_two_factor_check

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Any accepted alternative factors for the fixed n-th dual matrix preserve
its old actual-function bound. No claim of general Python-generator correctness. -/
theorem upper_of_synthesized_dual {n : ℕ}
    (d : PSDFactorCertQ (Profiles.ProximalGradient.basisCount n))
    (hd : checkPSDFactorQ (upperCertQ n).dualMatrix d = true)
    {L : ℝ≥0} {R : ℝ} {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsSmoothConvexFirstOrder L f g) (hh : ConvexOn ℝ Set.univ h)
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar + h xStar ≤ f y + h y)
    (hrun : ProximalGradientScaling.IsSmoothProxRun (n+1) L h g x)
    (hradius : ‖x 0-xStar‖^2 ≤ R^2) :
    f (x (n+1)) + h (x (n+1)) - (f xStar + h xStar) ≤
      (L : ℝ)*R^2/(4*((n : ℝ)+1)) := by
  have hc := checkUpperCertQ_withDualFactor (upperCertQ n) d (upperCertQ_check_all n) hd
  have hb := ProximalGradientScaling.certificate_upper_of_minimizer
    ((upperCertQ n).withDualFactor d) hc rfl rfl hf hh hL hR hmin hrun hradius
  calc
    f (x (n+1)) + h (x (n+1)) - (f xStar + h xStar) ≤
        (L : ℝ)*R^2*(boundQ n : ℝ) := hb
    _ = (L : ℝ)*R^2/(4*((n : ℝ)+1)) := by
      rw [boundQ_cast]
      ring

/-- The concrete two-step imported factors have no unchecked acceptance premise. -/
theorem two_step_upper [CompleteSpace E]
    {L : ℝ≥0} {R : ℝ} {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsSmoothConvexAnalytic L f g) (hh : ConvexOn ℝ Set.univ h)
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar + h xStar ≤ f y + h y)
    (hrun : ProximalGradientScaling.IsSmoothProxRun 2 L h g x)
    (hradius : ‖x 0-xStar‖^2 ≤ R^2) :
    f (x 2) + h (x 2) - (f xStar + h xStar) ≤ (L : ℝ)*R^2/8 := by
  have hb := upper_of_synthesized_dual (n := 1) PSDSynthesized.PGDualTwo.factorQ pg_two_factor_check
    hf.toFirstOrder hh hL hR hmin hrun hradius
  have he : (4 : ℝ)*(1+1) = 8 := by norm_num
  simpa only [Nat.cast_one, he] using hb

end LeanPEP.ActualFunction.PSDSynthesisApplications
