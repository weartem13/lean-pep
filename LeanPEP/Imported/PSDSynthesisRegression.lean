import LeanPEP.Imported.PSDSynthesized
import LeanPEP.Imported.GramOneStepResynthesized
import LeanPEP.Imported.GramOneStepExact

/-! D1: independently bind resynthesized factors to the OLD GD bundle.
No old native-decided acceptance theorem is used by the new proofs. -/
namespace LeanPEP.Imported.PSDSynthesisRegression

open LeanPEP.GramPEP

/-- These are the original model and primal, not new objects defined from factors. -/
theorem gd_model_unchanged :
    GramOneStepResynthesized.modelQ = GramOneStepExact.modelQ := rfl

theorem gd_primal_unchanged :
    GramOneStepResynthesized.primalQ = GramOneStepExact.primalQ := rfl

theorem gd_objective_unchanged :
    GramOneStepResynthesized.upperCertQ.objective = GramOneStepExact.upperCertQ.objective := rfl

theorem gd_dual_matrix_unchanged :
    GramOneStepResynthesized.upperCertQ.dualMatrix = GramOneStepExact.upperCertQ.dualMatrix := rfl

/-- PSD succeeds for both matrices AND the original full bundle obligations pass. -/
theorem gd_bundle_check :
    checkExactGramBundleQ GramOneStepResynthesized.bundleQ = true := by
  decide +kernel

/-- The rebuilt bundle still has its original exact attaining value, 1/6. -/
theorem gd_attainment_real :
    GramOneStepResynthesized.upperCertQ.objective.evalR
      (castDataQ GramOneStepResynthesized.primalQ) = (1/6 : ℝ) := by
  have h := checkExactGramBundleQ_sound_real
    GramOneStepResynthesized.bundleQ gd_bundle_check
  have ha : GramOneStepResynthesized.upperCertQ.objective.evalR
      (castDataQ GramOneStepResynthesized.primalQ) =
        (GramOneStepResynthesized.upperCertQ.bound : ℝ) := h.2.2.2.2.1
  have hb : (GramOneStepResynthesized.upperCertQ.bound : ℝ) = (1/6 : ℝ) := by
    norm_num [GramOneStepResynthesized.upperCertQ]
  exact ha.trans hb

/-- Wrong factor coefficients are rejected even though the target IS PSD. -/
def badFactorQ : PSDFactorCertQ 2 :=
  { factors := [{ weight := 2, vector := ![1, 0] }] }

theorem bad_factor_rejected :
    checkPSDFactorQ PSDSynthesized.IrrationalCholesky.matrixQ badFactorQ = false := by
  decide +kernel

/-- Negative factor weights must be rejected, not accepted by matrix identity alone. -/
def negativeWeightQ : PSDFactorCertQ 2 :=
  { factors := [{ weight := -1, vector := ![1, 0] }] }

theorem negative_weight_rejected : checkFactorWeightsQ negativeWeightQ = false := by
  decide +kernel

/-- Changing the objective is NOT repaired by successfully synthesizing PSD factors. -/
def wrongBoundBundleQ : ExactGramBundleQ 3 3 :=
  { GramOneStepResynthesized.bundleQ with
    upper := { GramOneStepResynthesized.upperCertQ with bound := 0 } }

theorem wrong_bound_bundle_rejected : checkExactGramBundleQ wrongBoundBundleQ = false := by
  decide +kernel

end LeanPEP.Imported.PSDSynthesisRegression
