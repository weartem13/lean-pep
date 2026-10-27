import LeanPEP

open scoped NNReal
open LeanPEP LeanPEP.GramPEP
open LeanPEP.Adapters.ProximalGradientSparse

#check ZeroRowCoverage.checkMapQ_eq_true_iff
#check ZeroRowCoverage.toFull_injective
#check ZeroRowCoverage.omitted_iff
#check ZeroRowCoverage.checkRowsQ_eq_true_iff
#check ZeroRowCoverage.feasible_iff
#check ZeroRowCoverage.finite_upper_equivalence
#check checkCoverageQ_eq_true_iff
#check checkSourceQ_eq_true_iff
#check retained_row_eq
#check omitted_row_zero
#check oriented_coverage_check
#check rows_feasible_iff
#check finite_upper_equivalence
#check completedTermQ_weight
#check completedTermQ_index
#check assumption_sum_preserved
#check certificate_rhs_preserved
#check completedUpper_check
#check completedUpperQ_count
#check checked_certificate
#check Imported.CompositeSparse.PGOne.bound_check
#check Imported.CompositeSparse.PGTwo.bound_check
#check Imported.CompositeSparse.PGThree.bound_check
#check Imported.CompositeSparse.PGAll.bound_check
#check Imported.CompositeSparse.missing_nonzero_local_passes
#check Imported.CompositeSparse.missing_nonzero_completed_passes
#check Imported.CompositeSparse.missing_nonzero_joint_rejected
#check Imported.CompositeSparse.split_performance_mass
#check ActualFunction.ProximalGradientSparseAudit.upper_firstOrder
#check ActualFunction.ProximalGradientSparseAudit.three_step_upper

example : ZeroRowCoverage.checkRowsQ
    ({ toFull := Fin.elim0, fromFull := fun _ => none } : ZeroRowCoverage.MapQ 0 2)
    (fun i => Fin.elim0 i) (fun _ => LinearExprQ.zero 0 0) = true := by decide +kernel

example {p m k r : ℕ} (a : ZeroRowCoverage.MapQ k r)
    (xs : Fin k → LinearExprQ p m) (ys : Fin r → LinearExprQ p m)
    (ha : ZeroRowCoverage.checkRowsQ a xs ys = true) (d : DataR (Fin p) m) :
    (∀ i, 0 ≤ (xs i).evalR d) ↔ ∀ j, 0 ≤ (ys j).evalR d :=
  ZeroRowCoverage.feasible_iff a xs ys ha d

example {n k : ℕ} (s : SourceQ n k) (hs : checkCoverageQ s = true)
    (c : UpperCertQ s.model) (hi : c.interpTerms = []) (hc : checkUpperCertQ c = true) :
    checkUpperCertQ (completedUpperQ s c) = true := completedUpper_check s hs c hi hc

example {n k : ℕ} (s : SourceQ n k) (c : UpperCertQ s.model) :
    (completedUpperQ s c).dualMatrix = c.dualMatrix := rfl

example {n k : ℕ} (s : SourceQ n k) (c : UpperCertQ s.model) :
    (completedUpperQ s c).dualFactor = c.dualFactor := rfl

example : checkBoundQ Imported.CompositeSparse.PGThree.sourceQ Imported.CompositeSparse.PGThree.upperQ = true :=
  Imported.CompositeSparse.PGThree.bound_check

example : checkSourceQ Imported.CompositeSparse.badInverseQ = false :=
  Imported.CompositeSparse.bad_inverse_rejected

example : checkUpperCertQ Imported.CompositeSparse.missingNonzeroUpperQ = true :=
  Imported.CompositeSparse.missing_nonzero_local_passes

example : checkBoundQ Imported.CompositeSparse.missingNonzeroQ Imported.CompositeSparse.missingNonzeroUpperQ = false :=
  Imported.CompositeSparse.missing_nonzero_joint_rejected

example : checkBoundQ Imported.CompositeSparse.PGOne.sourceQ Imported.CompositeSparse.implicitQ = false :=
  Imported.CompositeSparse.implicit_joint_rejected

example : (Imported.CompositeSparse.PGThree.upperQ.bound : ℝ) = 1/12 := by
  norm_num [Imported.CompositeSparse.PGThree.upperQ]

example : IsGreatest
    (ActualFunction.ProximalGradientCanonical.oneDimensionalHilbertValues 7 (3 : ℝ≥0) 2) (3/8 : ℝ) := by
  convert ActualFunction.ProximalGradientCanonical.hilbert_tight_all 7
    (L := (3 : ℝ≥0)) (R := 2) (by norm_num) (by norm_num) using 1 <;> norm_num

example : IsGreatest
    (ActualFunction.ProximalGradientCanonical.oneDimensionalHilbertValues 7 (3 : ℝ≥0) 0) 0 := by
  convert ActualFunction.ProximalGradientCanonical.hilbert_tight_all 7
    (L := (3 : ℝ≥0)) (R := 0) (by norm_num) (by norm_num) using 1 <;> norm_num

#print axioms LeanPEP.GramPEP.ZeroRowCoverage.feasible_iff
#print axioms LeanPEP.GramPEP.ZeroRowCoverage.finite_upper_equivalence
#print axioms LeanPEP.Adapters.ProximalGradientSparse.assumption_sum_preserved
#print axioms LeanPEP.Adapters.ProximalGradientSparse.completedUpper_check
#print axioms LeanPEP.Imported.CompositeSparse.missing_nonzero_joint_rejected
#print axioms LeanPEP.Imported.CompositeSparse.split_performance_mass
#print axioms LeanPEP.Imported.CompositeSparse.PGThree.bound_check
#print axioms LeanPEP.ActualFunction.ProximalGradientSparseAudit.three_step_upper
