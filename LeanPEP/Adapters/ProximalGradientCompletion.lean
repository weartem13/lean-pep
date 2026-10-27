import LeanPEP.Adapters.ProximalGradientCapture
import LeanPEP.GramPEP.RationalLinearSystem

/-! D10: exact bound/multiplier completion at a frozen candidate objective and
residual. The algorithm may fail. Both seed and final policy checks compare
DIRECTLY to raw; the original D9 checker validates the final certificate.
No linear solver or its source-to-system compiler enters the trusted boundary. -/
namespace LeanPEP.Adapters.ProximalGradientCompletion
open LeanPEP.GramPEP LeanPEP.GramPEP.RationalReconstructionAudit
open LeanPEP.Adapters.ProximalGradientSparse (SourceQ)
open LeanPEP.Adapters.ProximalGradientCapture (TraceQ)

def factorSignatureQ {m : ℕ} (f : PSDFactorCertQ m) : List (ℚ × List ℚ) :=
  f.factors.map fun t => (t.weight, List.ofFn t.vector)

def checkFixedTargetsQ {p m : ℕ} {model : ModelQ p m}
    (seed completed : UpperCertQ model) : Bool :=
  checkLinearExprEqQ seed.objective completed.objective &&
    checkGramEqQ seed.dualMatrix completed.dualMatrix &&
    decide (factorSignatureQ seed.dualFactor = factorSignatureQ completed.dualFactor) &&
    decide (assumptionReferencesQ seed = assumptionReferencesQ completed) &&
    decide (seed.interpTerms = []) && decide (completed.interpTerms = [])

theorem checkFixedTargetsQ_eq_true_iff {p m : ℕ} {model : ModelQ p m}
    (seed completed : UpperCertQ model) :
    checkFixedTargetsQ seed completed = true ↔
      seed.objective = completed.objective ∧ seed.dualMatrix = completed.dualMatrix ∧
      factorSignatureQ seed.dualFactor = factorSignatureQ completed.dualFactor ∧
      assumptionReferencesQ seed = assumptionReferencesQ completed ∧
      seed.interpTerms = [] ∧ completed.interpTerms = [] := by
  simp [checkFixedTargetsQ, checkLinearExprEqQ_eq_true_iff, checkGramEqQ_eq_true_iff, and_assoc]

def checkCompletedQ {n k : ℕ} (s : SourceQ n k) (t : TraceQ n k) (policy : PolicyQ)
    (raw seed completed : UpperCertQ s.model) : Bool :=
  checkChangesQ policy raw seed && checkFixedTargetsQ seed completed &&
    ProximalGradientCapture.checkCapturedQ s t policy raw completed

theorem checkCompletedQ_eq_true_iff {n k : ℕ} (s : SourceQ n k) (t : TraceQ n k)
    (policy : PolicyQ) (raw seed completed : UpperCertQ s.model) :
    checkCompletedQ s t policy raw seed completed = true ↔
      checkChangesQ policy raw seed = true ∧ checkFixedTargetsQ seed completed = true ∧
      ProximalGradientCapture.checkCapturedQ s t policy raw completed = true := by
  simp only [checkCompletedQ, Bool.and_eq_true, and_assoc]

theorem captured_check {n k : ℕ} (s : SourceQ n k) (t : TraceQ n k) (policy : PolicyQ)
    (raw seed completed : UpperCertQ s.model)
    (hc : checkCompletedQ s t policy raw seed completed = true) :
    ProximalGradientCapture.checkCapturedQ s t policy raw completed = true :=
  ((checkCompletedQ_eq_true_iff s t policy raw seed completed).mp hc).2.2

theorem residual_preserved {n k : ℕ} (s : SourceQ n k) (t : TraceQ n k) (policy : PolicyQ)
    (raw seed completed : UpperCertQ s.model)
    (hc : checkCompletedQ s t policy raw seed completed = true) :
    seed.dualMatrix = completed.dualMatrix :=
  ((checkFixedTargetsQ_eq_true_iff seed completed).mp
    ((checkCompletedQ_eq_true_iff s t policy raw seed completed).mp hc).2.1).2.1

theorem completion_within_raw_policy {n k : ℕ} (s : SourceQ n k) (t : TraceQ n k)
    (policy : PolicyQ) (raw seed completed : UpperCertQ s.model)
    (hc : checkCompletedQ s t policy raw seed completed = true) :
    CoefficientsWithinQ policy (numericalCoefficientsQ raw) (numericalCoefficientsQ completed) :=
  ProximalGradientReconstruction.reconstruction_within_policy s policy raw completed
    (ProximalGradientCapture.reconstructed_check s t policy raw completed
      (captured_check s t policy raw seed completed hc))

theorem checked_certificate {n k : ℕ} (s : SourceQ n k) (t : TraceQ n k) (policy : PolicyQ)
    (raw seed completed : UpperCertQ s.model)
    (hc : checkCompletedQ s t policy raw seed completed = true) :
    ∃ d : UpperCertQ (Profiles.ProximalGradient.modelQ n),
      checkUpperCertQ d = true ∧ d.interpTerms = [] ∧
      d.objective = Profiles.ProximalGradient.objectiveQ n ∧ d.bound = completed.bound :=
  ProximalGradientCapture.checked_certificate s t policy raw completed
    (captured_check s t policy raw seed completed hc)

end LeanPEP.Adapters.ProximalGradientCompletion
