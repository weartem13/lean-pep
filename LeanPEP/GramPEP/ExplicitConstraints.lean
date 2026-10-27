import LeanPEP.GramPEP.UpperCertificateChecker

/-!
# Explicit-constraint soundness of the unchanged Gram certificate checker

When `interpTerms = []`, the certificate uses only its model's explicit linear
assumptions and a dual PSD pairing. The implicit single-function smooth
interpolation semantics of `CoreFeasible` are then unnecessary.

This lemma is a new application rule, NOT a new coefficient or PSD checker.
The empty-interpolation hypothesis is essential: value slots may now refer to
different functions, so smooth interpolation across all slots would be invalid.
-/

namespace LeanPEP.GramPEP

@[simp] theorem castVecQ_zero {m : ℕ} :
    castVecQ (0 : VecExpr m ℚ) = 0 := by
  funext i
  simp [castVecQ]

@[simp] theorem castVecQ_neg {m : ℕ} (u : VecExpr m ℚ) :
    castVecQ (-u) = -castVecQ u := by
  funext i
  simp [castVecQ]

/-- An accepted certificate with no implicit interpolation terms is sound
on a PSD Gram matrix satisfying the explicitly supplied constraints. The
position/gradient fields of `d` are irrelevant for this application rule. -/
theorem checkUpperCertQ_sound_real_explicit {p m : ℕ} {model : ModelQ p m}
    (c : UpperCertQ model) (hcheck : checkUpperCertQ c = true)
    (hempty : c.interpTerms = []) (d : DataR (Fin p) m)
    (hpsd : IsGramPosSemidef d.gram)
    (hconstraints : AssumptionsFeasibleR model d) :
    c.objective.evalR d ≤ (c.bound : ℝ) := by
  have hc := checkUpperCertQ_sound c hcheck
  have ha := assumptionTermsValueR_nonneg model d hconstraints
    c.assumptionTerms hc.assumptionWeights
  have hd := gramPairingR_nonneg_of_valid c.dualMatrix c.dualFactor
    hc.dualValid d.gram hpsd
  have heval := congrArg (fun e : LinearExprQ p m => e.evalR d) hc.identity
  have hrhs : (certificateRhsExprQ c).evalR d =
      assumptionTermsValueR model d c.assumptionTerms +
        gramPairingR c.dualMatrix d.gram := by
    simp [certificateRhsExprQ, hempty, interpExprSumQ, gramPairingR]
  rw [hrhs, evalR_upperTargetExprQ] at heval
  linarith

end LeanPEP.GramPEP
