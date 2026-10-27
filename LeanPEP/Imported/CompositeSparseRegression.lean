import LeanPEP.Imported.CompositeSparse

/-! Independent D7 checks on literal data. The zero-row and missing-nonzero
counterexamples are separate from ordinary certificate coefficient failures. -/
namespace LeanPEP.Imported.CompositeSparse
open LeanPEP.GramPEP LeanPEP.Adapters.ProximalGradientSparse

namespace PGOne
theorem coverage_check : checkCoverageQ sourceQ = true := by decide +kernel
theorem source_check : checkSourceQ sourceQ = true := by decide +kernel
theorem raw_check : checkUpperCertQ upperQ = true := by decide +kernel
theorem completed_check : checkUpperCertQ (completedUpperQ sourceQ upperQ) = true :=
  completedUpper_check sourceQ coverage_check upperQ rfl raw_check
theorem bound_check : checkBoundQ sourceQ upperQ = true := by decide +kernel
end PGOne

namespace PGTwo
theorem coverage_check : checkCoverageQ sourceQ = true := by decide +kernel
theorem source_check : checkSourceQ sourceQ = true := by decide +kernel
theorem raw_check : checkUpperCertQ upperQ = true := by decide +kernel
theorem completed_check : checkUpperCertQ (completedUpperQ sourceQ upperQ) = true :=
  completedUpper_check sourceQ coverage_check upperQ rfl raw_check
theorem bound_check : checkBoundQ sourceQ upperQ = true := by decide +kernel
end PGTwo

namespace PGThree
theorem coverage_check : checkCoverageQ sourceQ = true := by decide +kernel
theorem source_check : checkSourceQ sourceQ = true := by decide +kernel
theorem raw_check : checkUpperCertQ upperQ = true := by decide +kernel
theorem completed_check : checkUpperCertQ (completedUpperQ sourceQ upperQ) = true :=
  completedUpper_check sourceQ coverage_check upperQ rfl raw_check
theorem bound_check : checkBoundQ sourceQ upperQ = true := by decide +kernel
end PGThree

namespace PGAll
theorem coverage_check : checkCoverageQ sourceQ = true := by decide +kernel
theorem source_check : checkSourceQ sourceQ = true := by decide +kernel
theorem raw_check : checkUpperCertQ upperQ = true := by decide +kernel
theorem completed_check : checkUpperCertQ (completedUpperQ sourceQ upperQ) = true :=
  completedUpper_check sourceQ coverage_check upperQ rfl raw_check
theorem bound_check : checkBoundQ sourceQ upperQ = true := by decide +kernel
end PGAll

/-- The full-family check cannot validate the submitted partial inverse. -/
def badInverseQ : SourceQ 0 10 :=
  { PGOne.sourceQ with
    coverage :=
      { toFull := PGOne.sourceQ.coverage.toFull
        fromFull := fun j => if j = 2 then some 0 else PGOne.sourceQ.coverage.fromFull j } }

theorem bad_inverse_completed_passes :
    Adapters.ProximalGradientPerformance.checkSourceQ (completedSourceQ badInverseQ) = true := by
  decide +kernel

theorem bad_inverse_rejected : checkSourceQ badInverseQ = false := by decide +kernel

/-- Identical zero polynomials do not make semantic labels interchangeable. -/
def badZeroLabelsQ : SourceQ 0 15 :=
  { PGAll.sourceQ with
    labels := fun i => if i = 1 then PGAll.sourceQ.labels 5 else
      if i = 5 then PGAll.sourceQ.labels 1 else PGAll.sourceQ.labels i }

theorem bad_zero_labels_rows_unchanged : badZeroLabelsQ.rows = PGAll.sourceQ.rows := rfl

theorem bad_zero_labels_rejected : checkSourceQ badZeroLabelsQ = false := by decide +kernel

/-- Removing an UNUSED nonzero constraint leaves this dual identity unchanged.
It is still not an exact representation of the specified source problem. -/
def missingNonzeroQ : SourceQ 0 9 :=
  { base := PGOne.sourceQ.base
    performanceRule := PGOne.sourceQ.performanceRule
    coverage :=
      { toFull := fun i => PGOne.sourceQ.coverage.toFull i.succ
        fromFull := fun j => (PGOne.sourceQ.coverage.fromFull j).bind
          (Fin.cases none (fun i => some i)) }
    rows := fun i => PGOne.sourceQ.rows i.succ
    rules := fun i => PGOne.sourceQ.rules i.succ
    labels := fun i => PGOne.sourceQ.labels i.succ
    objective := PGOne.sourceQ.objective }

def missingNonzeroUpperQ : UpperCertQ missingNonzeroQ.model :=
  { bound := PGOne.upperQ.bound
    objective := PGOne.upperQ.objective
    interpTerms := PGOne.upperQ.interpTerms
    assumptionTerms := PGOne.upperQ.assumptionTerms.map (fun t =>
      { weight := t.weight
        index := ⟨t.index.val-1, by
          have hi : t.index.val < 10 := (sourceRowQ PGOne.sourceQ t).isLt
          change t.index.val-1 < 9
          omega⟩ })
    dualMatrix := PGOne.upperQ.dualMatrix
    dualFactor := PGOne.upperQ.dualFactor }

theorem missing_nonzero_local_passes : checkUpperCertQ missingNonzeroUpperQ = true := by decide +kernel

theorem missing_nonzero_completed_passes :
    Adapters.ProximalGradientPerformance.checkBoundQ (completedSourceQ missingNonzeroQ)
      (completedUpperQ missingNonzeroQ missingNonzeroUpperQ) = true := by decide +kernel

theorem missing_nonzero_rejected : checkSourceQ missingNonzeroQ = false := by decide +kernel

theorem missing_nonzero_joint_rejected : checkBoundQ missingNonzeroQ missingNonzeroUpperQ = false := by
  decide +kernel

/-- The raw performance row is nonzero even though tau substitution annihilates it. -/
theorem performance_row_not_zero :
    checkLinearExprEqQ ((completedSourceQ PGOne.sourceQ).rows 0) (LinearExprQ.zero _ _) = false := by
  decide +kernel

def implicitQ : UpperCertQ PGOne.sourceQ.model :=
  { PGOne.upperQ with interpTerms := [{ weight := 0, i := 0, j := 1 }] }

theorem implicit_local_passes : checkUpperCertQ implicitQ = true := by decide +kernel

theorem implicit_joint_rejected : checkBoundQ PGOne.sourceQ implicitQ = false := by decide +kernel

/-- Performance is at compact row 19, not compact row 0; duplicate references
are mapped individually and contribute to the same full-row coefficient. -/
theorem split_performance_mass :
    Adapters.ProximalGradientPerformance.performanceMassQ (completedSourceQ PGTwo.sourceQ)
      (completedUpperQ PGTwo.sourceQ PGTwo.upperQ).assumptionTerms = 1 := by
  have ht := ((checkBoundQ_eq_true_iff PGTwo.sourceQ PGTwo.upperQ).mp PGTwo.bound_check).2.2.2.2
  exact Adapters.ProximalGradientPerformance.checked_performance_mass _ _ ht

end LeanPEP.Imported.CompositeSparse
