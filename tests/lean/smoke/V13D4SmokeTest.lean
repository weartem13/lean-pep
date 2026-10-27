import LeanPEP

open scoped NNReal BigOperators
open LeanPEP LeanPEP.GramPEP LeanPEP.GramPEP.ExactReindexing
open LeanPEP.Adapters.ProximalGradientOrdering
open LeanPEP.Imported.CompositeOrdering

#check checkQ_eq_true_iff
#check checkQ_identity
#check checkedEquiv
#check vec_roundtrip
#check matrix_roundtrip
#check expr_roundtrip
#check sample_roundtrip
#check factorGram_reindex
#check sum_reindex
#check evalR_reindex
#check checkOrderingQ_eq_true_iff
#check reorderSnapshotQ_roundtrip
#check constraint_reference
#check checkSourceQ_eq_true_iff
#check source_roundtrip
#check nativeAssumptionQ_index
#check nativeUpperQ_bound
#check nativeUpperQ_assumption_count
#check checkBoundQ_eq_true_iff
#check checked_certificate
#check PGOne.bound_check
#check PGTwo.bound_check
#check PGThree.bound_check
#check PGIdentity.bound_check
#check bad_inverse_native_passes
#check bad_inverse_rejected
#check wrong_rows_joint_rejected
#check implicit_joint_rejected
#check forged_joint_rejected
#check ActualFunction.ProximalGradientOrderingAudit.finite_upper
#check ActualFunction.ProximalGradientOrderingAudit.upper_firstOrder
#check ActualFunction.ProximalGradientOrderingAudit.three_step_upper

example : checkQ (IndexMapQ.identity 0) = true := checkQ_identity 0
example {k : ℕ} (p : IndexMapQ k) (hp : checkQ p = true) (f : Fin k → ℚ) :
    (∑ i, f (p.toSource i)) = ∑ i, f i := sum_reindex p hp f
example {p m : ℕ} (pv : IndexMapQ p) (pb : IndexMapQ m)
    (hv : checkQ pv = true) (hb : checkQ pb = true) (e : LinearExprQ p m)
    (d : DataR (Fin p) m) : (expr pv pb e).evalR (dataR pv pb d) = e.evalR d :=
  evalR_reindex pv pb hv hb e d
example {n : ℕ} (o : OrderingQ n) (ho : checkOrderingQ o = true) (s : SnapshotQ n) :
    reorderSnapshotQ o.symm (reorderSnapshotQ o s) = s := reorderSnapshotQ_roundtrip o ho s
example {n : ℕ} (o : OrderingQ n) (ho : checkOrderingQ o = true) (s : SnapshotQ n)
    (j : Fin (rowCount n)) :
    (reorderSnapshotQ o s).constraints (o.rows.toCanonical j) = expr o.values o.basis (s.constraints j) :=
  constraint_reference o ho s j
example : checkBoundQ PGOne.sourceQ PGOne.upperQ = true := PGOne.bound_check
example : checkBoundQ PGTwo.sourceQ PGTwo.upperQ = true := PGTwo.bound_check
example : checkBoundQ PGThree.sourceQ PGThree.upperQ = true := PGThree.bound_check
example : checkBoundQ PGIdentity.sourceQ PGIdentity.upperQ = true := PGIdentity.bound_check
example : Adapters.ProximalGradientCoordinates.checkSourceQ (nativeSourceQ badInverseQ) = true ∧
    checkSourceQ badInverseQ = false := ⟨bad_inverse_native_passes,bad_inverse_rejected⟩
example : checkUpperCertQ implicitQ = true ∧ checkBoundQ PGOne.sourceQ implicitQ = false :=
  ⟨implicit_local_passes,implicit_joint_rejected⟩
example : checkUpperCertQ forgedUpperQ = true ∧ checkBoundQ forgedSourceQ forgedUpperQ = false :=
  ⟨forged_local_passes,forged_joint_rejected⟩
example {n : ℕ} (s : SourceQ n) (c : UpperCertQ s.model) (hc : checkBoundQ s c = true) :
    ∃ d : UpperCertQ (Profiles.ProximalGradient.modelQ n), checkUpperCertQ d = true ∧
      d.interpTerms = [] ∧ d.objective = Profiles.ProximalGradient.objectiveQ n ∧ d.bound = c.bound :=
  checked_certificate s c hc
example : IsGreatest
    (ActualFunction.ProximalGradientScaling.oneDimensionalAnalyticValues 7 (3 : ℝ≥0) 2)
    (3/8 : ℝ) := by
  have h := ActualFunction.ProximalGradientWitnessScaling.analytic_tight_all 7
    (L := (3 : ℝ≥0)) (R := 2) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

#print axioms checkQ_eq_true_iff
#print axioms evalR_reindex
#print axioms reorderSnapshotQ_roundtrip
#print axioms constraint_reference
#print axioms checked_certificate
#print axioms bad_inverse_rejected
#print axioms PGThree.bound_check
#print axioms ActualFunction.ProximalGradientOrderingAudit.three_step_upper
