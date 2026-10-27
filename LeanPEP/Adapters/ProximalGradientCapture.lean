import LeanPEP.Adapters.ProximalGradientReconstruction
import LeanPEP.GramPEP.ExactReindexing

/-!
# D9: binding a prepared solver snapshot to the D8 raw candidate

The external producer is not authenticated. This checker binds the *submitted*
prepared rows, scalar-leaf permutation, objective, bound, every ordered dual
weight (including zero), and independent residual matrix to one D7 source and
one D8 raw candidate. PEPit inequalities use `expression <= 0` and unit scales.
The only conversion here relocates scalar leaves (including tau); Gram axes
and the prepared constraint order are unchanged. No numerical repair occurs.
-/
namespace LeanPEP.Adapters.ProximalGradientCapture

open LeanPEP.GramPEP LeanPEP.GramPEP.ExactReindexing
open LeanPEP.GramPEP.RationalReconstructionAudit
open ProximalGradientOrdering (valueCount basisCount)
open ProximalGradientSparse (SourceQ)

structure TraceQ (n k : ℕ) where
  values : IndexMapQ (valueCount n + 1)
  rows : Fin k → LinearExprQ (valueCount n + 1) (basisCount n)
  objective : LinearExprQ (valueCount n + 1) (basisCount n)
  bound : ℚ
  weights : Fin k → ℚ
  residual : Gram (basisCount n) ℚ

def moveValuesQ {n k : ℕ} (t : TraceQ n k)
    (e : LinearExprQ (valueCount n + 1) (basisCount n)) :
    LinearExprQ (valueCount n + 1) (basisCount n) :=
  expr t.values (IndexMapQ.identity (basisCount n)) e

def checkTraceQ {n k : ℕ} (s : SourceQ n k) (t : TraceQ n k) : Bool :=
  checkQ t.values &&
    (List.finRange k).all (fun i => checkLinearExprEqQ (moveValuesQ t (t.rows i)) (s.rows i)) &&
    checkLinearExprEqQ (moveValuesQ t t.objective) s.objective &&
    (List.finRange k).all (fun i => decide
      ((s.rules i).sense = RowNormalization.SenseQ.leZero ∧ (s.rules i).scale = 1)) &&
    ProximalGradientSparse.checkSourceQ s

theorem checkTraceQ_eq_true_iff {n k : ℕ} (s : SourceQ n k) (t : TraceQ n k) :
    checkTraceQ s t = true ↔
      checkQ t.values = true ∧
      (∀ i, moveValuesQ t (t.rows i) = s.rows i) ∧
      moveValuesQ t t.objective = s.objective ∧
      (∀ i, (s.rules i).sense = RowNormalization.SenseQ.leZero ∧ (s.rules i).scale = 1) ∧
      ProximalGradientSparse.checkSourceQ s = true := by
  simp [checkTraceQ, List.all_eq_true, checkLinearExprEqQ_eq_true_iff, and_assoc]

theorem captured_row_eval {n k : ℕ} (s : SourceQ n k) (t : TraceQ n k)
    (h : checkTraceQ s t = true) (i : Fin k)
    (d : DataR (Fin (valueCount n + 1)) (basisCount n)) :
    (s.rows i).evalR (dataR t.values (IndexMapQ.identity (basisCount n)) d) =
      (t.rows i).evalR d := by
  have ht := (checkTraceQ_eq_true_iff s t).mp h
  rw [← ht.2.1 i]
  exact evalR_reindex t.values _ ht.1 (checkQ_identity _) (t.rows i) d

theorem captured_objective_eval {n k : ℕ} (s : SourceQ n k) (t : TraceQ n k)
    (h : checkTraceQ s t = true)
    (d : DataR (Fin (valueCount n + 1)) (basisCount n)) :
    s.objective.evalR (dataR t.values (IndexMapQ.identity (basisCount n)) d) =
      t.objective.evalR d := by
  have ht := (checkTraceQ_eq_true_iff s t).mp h
  rw [← ht.2.2.1]
  exact evalR_reindex t.values _ ht.1 (checkQ_identity _) t.objective d

def orderedWeightsQ {p m : ℕ} {model : ModelQ p m} (c : UpperCertQ model) : List (ℕ × ℚ) :=
  c.assumptionTerms.map fun u => (u.index.val, u.weight)

def traceWeightsQ {n k : ℕ} (t : TraceQ n k) : List (ℕ × ℚ) :=
  (List.finRange k).map fun i => (i.val, t.weights i)

/-- Exact binding is independent of whether the raw certificate is accepted.
Factors are excluded: D1 generates them separately and the old checker checks
against this very same residual. Every solver row gets exactly one entry. -/
def checkRawBindingQ {n k : ℕ} (s : SourceQ n k) (t : TraceQ n k)
    (raw : UpperCertQ s.model) : Bool :=
  decide (raw.bound = t.bound) &&
    checkLinearExprEqQ raw.objective (moveValuesQ t t.objective) &&
    decide (raw.interpTerms = []) &&
    decide (orderedWeightsQ raw = traceWeightsQ t) &&
    checkGramEqQ raw.dualMatrix t.residual

theorem checkRawBindingQ_eq_true_iff {n k : ℕ} (s : SourceQ n k) (t : TraceQ n k)
    (raw : UpperCertQ s.model) :
    checkRawBindingQ s t raw = true ↔
      raw.bound = t.bound ∧ raw.objective = moveValuesQ t t.objective ∧
      raw.interpTerms = [] ∧ orderedWeightsQ raw = traceWeightsQ t ∧
      raw.dualMatrix = t.residual := by
  simp [checkRawBindingQ, checkLinearExprEqQ_eq_true_iff, checkGramEqQ_eq_true_iff, and_assoc]

theorem captured_numerics_preserved {n k : ℕ} (s : SourceQ n k) (t : TraceQ n k)
    (raw : UpperCertQ s.model) (h : checkRawBindingQ s t raw = true) :
    raw.bound = t.bound ∧ orderedWeightsQ raw = traceWeightsQ t ∧ raw.dualMatrix = t.residual := by
  have ht := (checkRawBindingQ_eq_true_iff s t raw).mp h
  exact ⟨ht.1, ht.2.2.2.1, ht.2.2.2.2⟩

def checkCapturedRawQ {n k : ℕ} (s : SourceQ n k) (t : TraceQ n k)
    (raw : UpperCertQ s.model) : Bool :=
  checkTraceQ s t && checkRawBindingQ s t raw && ProximalGradientReconstruction.checkRawQ s raw

def checkCapturedQ {n k : ℕ} (s : SourceQ n k) (t : TraceQ n k) (policy : PolicyQ)
    (raw reconstructed : UpperCertQ s.model) : Bool :=
  checkTraceQ s t && checkRawBindingQ s t raw &&
    ProximalGradientReconstruction.checkReconstructedQ s policy raw reconstructed

theorem checkCapturedQ_eq_true_iff {n k : ℕ} (s : SourceQ n k) (t : TraceQ n k) (policy : PolicyQ)
    (raw reconstructed : UpperCertQ s.model) :
    checkCapturedQ s t policy raw reconstructed = true ↔
      checkTraceQ s t = true ∧ checkRawBindingQ s t raw = true ∧
      ProximalGradientReconstruction.checkReconstructedQ s policy raw reconstructed = true := by
  simp only [checkCapturedQ, Bool.and_eq_true, and_assoc]

theorem reconstructed_check {n k : ℕ} (s : SourceQ n k) (t : TraceQ n k) (policy : PolicyQ)
    (raw reconstructed : UpperCertQ s.model)
    (h : checkCapturedQ s t policy raw reconstructed = true) :
    ProximalGradientReconstruction.checkReconstructedQ s policy raw reconstructed = true :=
  ((checkCapturedQ_eq_true_iff s t policy raw reconstructed).mp h).2.2

theorem checkCapturedRawQ_eq_true_iff {n k : ℕ} (s : SourceQ n k) (t : TraceQ n k)
    (raw : UpperCertQ s.model) :
    checkCapturedRawQ s t raw = true ↔
      checkTraceQ s t = true ∧ checkRawBindingQ s t raw = true ∧
      ProximalGradientReconstruction.checkRawQ s raw = true := by
  simp only [checkCapturedRawQ, Bool.and_eq_true, and_assoc]

theorem captured_raw_check {n k : ℕ} (s : SourceQ n k) (t : TraceQ n k)
    (raw : UpperCertQ s.model) (h : checkCapturedRawQ s t raw = true) :
    ProximalGradientReconstruction.checkRawQ s raw = true :=
  ((checkCapturedRawQ_eq_true_iff s t raw).mp h).2.2

theorem checked_certificate {n k : ℕ} (s : SourceQ n k) (t : TraceQ n k) (policy : PolicyQ)
    (raw reconstructed : UpperCertQ s.model)
    (h : checkCapturedQ s t policy raw reconstructed = true) :
    ∃ d : UpperCertQ (Profiles.ProximalGradient.modelQ n),
      checkUpperCertQ d = true ∧ d.interpTerms = [] ∧
      d.objective = Profiles.ProximalGradient.objectiveQ n ∧ d.bound = reconstructed.bound :=
  ProximalGradientReconstruction.checked_certificate s policy raw reconstructed
    (reconstructed_check s t policy raw reconstructed h)

end LeanPEP.Adapters.ProximalGradientCapture
