import LeanPEP.Adapters.ProximalGradientPerformance
import LeanPEP.GramPEP.ZeroRowCoverage

/-!
# D7: sparse submitted rows with exact zero-row coverage before D6

A D5 base-source template is checked by the unchanged lower-level source audit.
The D6 full extended row family is generated from that checked template, NOT
from the candidate certificate. Actual sparse raw rows, directions/scales,
labels, and both partial-inverse maps are independently submitted and checked.
Only coefficientwise ZERO full rows may be absent. No matching-point tests,
zero-dual-weight heuristic, arbitrary redundant row deletion, or extra rows.
-/
namespace LeanPEP.Adapters.ProximalGradientSparse

open LeanPEP.GramPEP LeanPEP.GramPEP.ZeroRowCoverage LeanPEP.GramPEP.RowNormalization
open ProximalGradientOrdering (valueCount basisCount rowCount)

inductive RowLabelQ where
  | performance
  | base (tag : ProximalGradientSource.RowTagQ)
  deriving DecidableEq, Repr

@[ext] structure SourceQ (n k : ℕ) where
  base : ProximalGradientRows.SourceQ n
  performanceRule : RuleQ
  coverage : MapQ k (rowCount n + 1)
  rows : Fin k → LinearExprQ (valueCount n + 1) (basisCount n)
  rules : Fin k → RuleQ
  labels : Fin k → RowLabelQ
  objective : LinearExprQ (valueCount n + 1) (basisCount n)

/-- A proposed full source, subject to the original D6 source check. No upper
certificate or pre-accepted lower certificate is part of the source template. -/
def completedSourceQ {n k : ℕ} (s : SourceQ n k) : ProximalGradientPerformance.SourceQ n :=
  { base := s.base
    performanceRule := s.performanceRule
    rows := ProximalGradientPerformance.expectedRowsQ s.base s.performanceRule
    objective := s.objective }

def fullLabelQ {n k : ℕ} (s : SourceQ n k) : Fin (rowCount n + 1) → RowLabelQ :=
  Fin.cons .performance (fun i => .base (s.base.snapshot.rowTags i))

def orientedRowQ {n k : ℕ} (s : SourceQ n k) (i : Fin k) :
    LinearExprQ (valueCount n + 1) (basisCount n) := orientExprQ (s.rules i).sense (s.rows i)

def SourceQ.model {n k : ℕ} (s : SourceQ n k) : ModelQ (valueCount n + 1) (basisCount n) :=
  { position := fun _ => 0
    gradient := fun _ => 0
    assumptions := List.ofFn (orientedRowQ s) }

def checkCoverageQ {n k : ℕ} (s : SourceQ n k) : Bool :=
  checkRowsQ s.coverage s.rows (completedSourceQ s).rows &&
    ((List.finRange k).all (fun i => decide
      (s.rules i = ProximalGradientPerformance.rowRuleQ (completedSourceQ s) (s.coverage.toFull i))) &&
      (List.finRange k).all (fun i => decide (s.labels i = fullLabelQ s (s.coverage.toFull i))))

theorem checkCoverageQ_eq_true_iff {n k : ℕ} (s : SourceQ n k) :
    checkCoverageQ s = true ↔
      checkRowsQ s.coverage s.rows (completedSourceQ s).rows = true ∧
      (∀ i, s.rules i = ProximalGradientPerformance.rowRuleQ (completedSourceQ s) (s.coverage.toFull i)) ∧
      (∀ i, s.labels i = fullLabelQ s (s.coverage.toFull i)) := by
  simp [checkCoverageQ, List.all_eq_true]

def checkSourceQ {n k : ℕ} (s : SourceQ n k) : Bool :=
  checkCoverageQ s && ProximalGradientPerformance.checkSourceQ (completedSourceQ s)

theorem checkSourceQ_eq_true_iff {n k : ℕ} (s : SourceQ n k) :
    checkSourceQ s = true ↔ checkCoverageQ s = true ∧
      ProximalGradientPerformance.checkSourceQ (completedSourceQ s) = true := by
  simp only [checkSourceQ, Bool.and_eq_true]

theorem retained_row_eq {n k : ℕ} (s : SourceQ n k) (hs : checkCoverageQ s = true) (i : Fin k) :
    orientedRowQ s i =
      ProximalGradientPerformance.orientedRowQ (completedSourceQ s) (s.coverage.toFull i) := by
  obtain ⟨hr, he, _⟩ := (checkCoverageQ_eq_true_iff s).mp hs
  have hx := ((checkRowsQ_eq_true_iff s.coverage s.rows (completedSourceQ s).rows).mp hr).2.1 i
  simp only [orientedRowQ, ProximalGradientPerformance.orientedRowQ, he i, hx]

theorem omitted_row_zero {n k : ℕ} (s : SourceQ n k) (hs : checkCoverageQ s = true)
    (j : Fin (rowCount n + 1)) (hj : s.coverage.fromFull j = none) :
    ProximalGradientPerformance.orientedRowQ (completedSourceQ s) j = LinearExprQ.zero _ _ := by
  have hr := ((checkCoverageQ_eq_true_iff s).mp hs).1
  have hz := ((checkRowsQ_eq_true_iff s.coverage s.rows (completedSourceQ s).rows).mp hr).2.2 j hj
  unfold ProximalGradientPerformance.orientedRowQ
  rw [hz]
  cases (ProximalGradientPerformance.rowRuleQ (completedSourceQ s) j).sense <;>
    simp [orientExprQ, LinearExprQ.neg, LinearExprQ.zero]

/-- This coverage theorem applies BEFORE substituting tau or deleting origin
coordinates; a row that vanishes only after those operations may not be omitted. -/
theorem oriented_coverage_check {n k : ℕ} (s : SourceQ n k) (hs : checkCoverageQ s = true) :
    checkRowsQ s.coverage (orientedRowQ s)
      (ProximalGradientPerformance.orientedRowQ (completedSourceQ s)) = true := by
  have hr := ((checkCoverageQ_eq_true_iff s).mp hs).1
  have hm := ((checkRowsQ_eq_true_iff s.coverage s.rows (completedSourceQ s).rows).mp hr).1
  exact (checkRowsQ_eq_true_iff _ _ _).mpr
    ⟨hm, retained_row_eq s hs, omitted_row_zero s hs⟩

theorem rows_feasible_iff {n k : ℕ} (s : SourceQ n k) (hs : checkCoverageQ s = true)
    (d : DataR (Fin (valueCount n + 1)) (basisCount n)) :
    (∀ i, 0 ≤ (orientedRowQ s i).evalR d) ↔
      ∀ j, 0 ≤ (ProximalGradientPerformance.orientedRowQ (completedSourceQ s) j).evalR d :=
  ZeroRowCoverage.feasible_iff _ _ _ (oriented_coverage_check s hs) d

theorem finite_upper_equivalence {n k : ℕ} (s : SourceQ n k) (hs : checkCoverageQ s = true) (B : ℝ) :
    (∀ d : DataR (Fin (valueCount n + 1)) (basisCount n), IsGramPosSemidef d.gram →
      (∀ i, 0 ≤ (orientedRowQ s i).evalR d) → s.objective.evalR d ≤ B) ↔
    (∀ d : DataR (Fin (valueCount n + 1)) (basisCount n), IsGramPosSemidef d.gram →
      (∀ j, 0 ≤ (ProximalGradientPerformance.orientedRowQ (completedSourceQ s) j).evalR d) →
        s.objective.evalR d ≤ B) :=
  ZeroRowCoverage.finite_upper_equivalence _ _ _ (oriented_coverage_check s hs) s.objective B

def sourceRowQ {n k : ℕ} (s : SourceQ n k) (t : AssumptionTermQ s.model) : Fin k :=
  ⟨t.index.val, by simpa only [SourceQ.model, List.length_ofFn] using t.index.isLt⟩

def completedTermQ {n k : ℕ} (s : SourceQ n k) (t : AssumptionTermQ s.model) :
    AssumptionTermQ (completedSourceQ s).model :=
  { weight := t.weight
    index := ⟨(s.coverage.toFull (sourceRowQ s t)).val, by
      simpa only [ProximalGradientPerformance.SourceQ.model, List.length_ofFn]
        using (s.coverage.toFull (sourceRowQ s t)).isLt⟩ }

@[simp] theorem completedTermQ_weight {n k : ℕ} (s : SourceQ n k) (t : AssumptionTermQ s.model) :
    (completedTermQ s t).weight = t.weight := rfl

@[simp] theorem completedTermQ_index {n k : ℕ} (s : SourceQ n k) (t : AssumptionTermQ s.model) :
    (completedTermQ s t).index.val = (s.coverage.toFull (sourceRowQ s t)).val := rfl

theorem source_get {n k : ℕ} (s : SourceQ n k) (t : AssumptionTermQ s.model) :
    s.model.assumptions.get t.index = orientedRowQ s (sourceRowQ s t) := by
  exact List.get_ofFn (orientedRowQ s) t.index

theorem completed_get {n k : ℕ} (s : SourceQ n k) (hs : checkCoverageQ s = true)
    (t : AssumptionTermQ s.model) :
    (completedSourceQ s).model.assumptions.get (completedTermQ s t).index =
      s.model.assumptions.get t.index := by
  rw [source_get]
  have he := List.get_ofFn (ProximalGradientPerformance.orientedRowQ (completedSourceQ s))
    (completedTermQ s t).index
  exact he.trans (retained_row_eq s hs (sourceRowQ s t)).symm

theorem assumption_sum_preserved {n k : ℕ} (s : SourceQ n k) (hs : checkCoverageQ s = true)
    (ts : List (AssumptionTermQ s.model)) :
    assumptionExprSumQ (completedSourceQ s).model (ts.map (completedTermQ s)) =
      assumptionExprSumQ s.model ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp only [List.map_cons, assumptionExprSumQ, completedTermQ_weight, completed_get s hs, ih]

/-- No terms are deleted here, even zero weights and repeated row references.
D6's separate, proved tau substitution may delete performance references later. -/
def completedUpperQ {n k : ℕ} (s : SourceQ n k) (c : UpperCertQ s.model) :
    UpperCertQ (completedSourceQ s).model :=
  { bound := c.bound
    objective := c.objective
    interpTerms := c.interpTerms
    assumptionTerms := c.assumptionTerms.map (completedTermQ s)
    dualMatrix := c.dualMatrix
    dualFactor := c.dualFactor }

@[simp] theorem completedUpperQ_bound {n k : ℕ} (s : SourceQ n k) (c : UpperCertQ s.model) :
    (completedUpperQ s c).bound = c.bound := rfl

@[simp] theorem completedUpperQ_count {n k : ℕ} (s : SourceQ n k) (c : UpperCertQ s.model) :
    (completedUpperQ s c).assumptionTerms.length = c.assumptionTerms.length := by
  simp only [completedUpperQ, List.length_map]

theorem certificate_rhs_preserved {n k : ℕ} (s : SourceQ n k) (hs : checkCoverageQ s = true)
    (c : UpperCertQ s.model) (hi : c.interpTerms = []) :
    certificateRhsExprQ (completedUpperQ s c) = certificateRhsExprQ c := by
  simp only [certificateRhsExprQ, completedUpperQ, hi, interpExprSumQ, assumption_sum_preserved s hs]

theorem completedUpper_check {n k : ℕ} (s : SourceQ n k) (hs : checkCoverageQ s = true)
    (c : UpperCertQ s.model) (hi : c.interpTerms = []) (hc : checkUpperCertQ c = true) :
    checkUpperCertQ (completedUpperQ s c) = true := by
  have hv := checkUpperCertQ_sound c hc
  apply checkUpperCertQ_complete
  refine
    { interpWeights := hv.interpWeights
      assumptionWeights := ?_
      dualValid := hv.dualValid
      identity := (certificate_rhs_preserved s hs c hi).trans hv.identity }
  intro t ht
  change t ∈ c.assumptionTerms.map (completedTermQ s) at ht
  rcases List.mem_map.mp ht with ⟨u, hu, rfl⟩
  exact hv.assumptionWeights u hu

def checkBoundQ {n k : ℕ} (s : SourceQ n k) (c : UpperCertQ s.model) : Bool :=
  checkSourceQ s && (checkUpperCertQ c && (decide (c.interpTerms = []) &&
    (checkLinearExprEqQ c.objective s.objective &&
      ProximalGradientPerformance.checkBoundQ (completedSourceQ s) (completedUpperQ s c))))

theorem checkBoundQ_eq_true_iff {n k : ℕ} (s : SourceQ n k) (c : UpperCertQ s.model) :
    checkBoundQ s c = true ↔ checkSourceQ s = true ∧ checkUpperCertQ c = true ∧
      c.interpTerms = [] ∧ c.objective = s.objective ∧
      ProximalGradientPerformance.checkBoundQ (completedSourceQ s) (completedUpperQ s c) = true := by
  simp only [checkBoundQ, Bool.and_eq_true, decide_eq_true_eq, checkLinearExprEqQ_eq_true_iff]

theorem checked_certificate {n k : ℕ} (s : SourceQ n k) (c : UpperCertQ s.model)
    (hc : checkBoundQ s c = true) :
    ∃ d : UpperCertQ (LeanPEP.Profiles.ProximalGradient.modelQ n),
      checkUpperCertQ d = true ∧ d.interpTerms = [] ∧
      d.objective = LeanPEP.Profiles.ProximalGradient.objectiveQ n ∧ d.bound = c.bound := by
  have ht := ((checkBoundQ_eq_true_iff s c).mp hc).2.2.2.2
  exact ProximalGradientPerformance.checked_certificate (completedSourceQ s) (completedUpperQ s c) ht

end LeanPEP.Adapters.ProximalGradientSparse
