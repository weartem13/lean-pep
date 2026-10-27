import LeanPEP

open scoped NNReal
open LeanPEP LeanPEP.GramPEP

#check RowNormalization.checkRulesQ_eq_true_iff
#check RowNormalization.orient_involutive
#check RowNormalization.encode_normalize
#check RowNormalization.normalize_encode
#check RowNormalization.normalize_injective
#check RowNormalization.orient_nonneg_iff
#check RowNormalization.normalize_nonneg_iff
#check RowNormalization.weighted_normalize
#check RowNormalization.normalized_weight_nonneg
#check Adapters.ProximalGradientRows.snapshot_roundtrip
#check Adapters.ProximalGradientRows.rows_feasible_iff
#check Adapters.ProximalGradientRows.source_binding
#check Adapters.ProximalGradientRows.normalizedAssumptionQ_weight
#check Adapters.ProximalGradientRows.normalizedAssumptionQ_index
#check Adapters.ProximalGradientRows.assumption_sum_preserved
#check Adapters.ProximalGradientRows.certificate_rhs_preserved
#check Adapters.ProximalGradientRows.normalizedUpper_check
#check Adapters.ProximalGradientRows.normalizedUpperQ_assumption_count
#check Adapters.ProximalGradientRows.checkBoundQ_eq_true_iff
#check Adapters.ProximalGradientRows.checked_certificate
#check Imported.CompositeRows.PGOne.bound_check
#check Imported.CompositeRows.PGTwo.bound_check
#check Imported.CompositeRows.PGThree.bound_check
#check Imported.CompositeRows.PGUnit.bound_check
#check Imported.CompositeRows.zero_scale_normalized_passes
#check Imported.CompositeRows.zero_scale_rejected
#check Imported.CompositeRows.negative_scale_rejected
#check Imported.CompositeRows.forged_local_passes
#check Imported.CompositeRows.forged_joint_rejected
#check ActualFunction.ProximalGradientRowAudit.upper_firstOrder
#check ActualFunction.ProximalGradientRowAudit.upper_analytic
#check ActualFunction.ProximalGradientRowAudit.three_step_upper

example {p m : ℕ} (e : LinearExprQ p m) :
    RowNormalization.normalizeExprQ {sense := .leZero, scale := 3}
      (RowNormalization.encodeExprQ {sense := .leZero, scale := 3} e) = e :=
  RowNormalization.normalize_encode _ (by norm_num) e

example {p m : ℕ} (e : LinearExprQ p m) (d : DataR (Fin p) m) :
    0 ≤ (RowNormalization.normalizeExprQ {sense := .leZero, scale := 2} e).evalR d ↔ e.evalR d ≤ 0 :=
  RowNormalization.normalize_nonneg_iff _ (by norm_num) e d

example (s : Adapters.ProximalGradientRows.SourceQ 0)
    (hr : RowNormalization.checkRulesQ s.rules = true) :
    Adapters.ProximalGradientRows.restoredSnapshotQ s = s.snapshot :=
  Adapters.ProximalGradientRows.snapshot_roundtrip s hr

example {n : ℕ} (s : Adapters.ProximalGradientRows.SourceQ n)
    (hr : RowNormalization.checkRulesQ s.rules = true)
    (c : UpperCertQ s.model) (hi : c.interpTerms = []) (hc : checkUpperCertQ c = true) :
    checkUpperCertQ (Adapters.ProximalGradientRows.normalizedUpperQ s c) = true :=
  Adapters.ProximalGradientRows.normalizedUpper_check s hr c hi hc

example : Adapters.ProximalGradientRows.checkBoundQ Imported.CompositeRows.PGThree.sourceQ
    Imported.CompositeRows.PGThree.upperQ = true := Imported.CompositeRows.PGThree.bound_check

example : Adapters.ProximalGradientRows.checkSourceQ Imported.CompositeRows.zeroScaleQ = false :=
  Imported.CompositeRows.zero_scale_rejected

example : Adapters.ProximalGradientRows.checkSourceQ Imported.CompositeRows.negativeScaleQ = false :=
  Imported.CompositeRows.negative_scale_rejected

example : Adapters.ProximalGradientRows.checkSourceQ Imported.CompositeRows.wrongSenseQ = false :=
  Imported.CompositeRows.wrong_sense_rejected

example : Adapters.ProximalGradientRows.checkBoundQ Imported.CompositeRows.PGOne.sourceQ
    Imported.CompositeRows.implicitQ = false := Imported.CompositeRows.implicit_joint_rejected

example : checkUpperCertQ Imported.CompositeRows.forgedUpperQ = true :=
  Imported.CompositeRows.forged_local_passes

example : Adapters.ProximalGradientRows.checkBoundQ Imported.CompositeRows.forgedSourceQ
    Imported.CompositeRows.forgedUpperQ = false := Imported.CompositeRows.forged_joint_rejected

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {L : ℝ≥0} {R : ℝ} {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : ActualFunction.IsSmoothConvexAnalytic L f g) (hh : ConvexOn ℝ Set.univ h)
    (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar + h xStar ≤ f y + h y)
    (hrun : ActualFunction.ProximalGradientScaling.IsSmoothProxRun 3 L h g x)
    (hradius : ‖x 0-xStar‖^2 ≤ R^2) :
    f (x 3)+h (x 3)-(f xStar+h xStar) ≤ (L : ℝ)*R^2/12 :=
  ActualFunction.ProximalGradientRowAudit.three_step_upper hf hh hL hR hmin hrun hradius

example : IsGreatest
    (ActualFunction.ProximalGradientCanonical.oneDimensionalHilbertValues 7 (3 : ℝ≥0) 2) (3/8 : ℝ) := by
  have h := ActualFunction.ProximalGradientCanonical.hilbert_tight_all
    7 (L := (3 : ℝ≥0)) (R := 2) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

#print axioms RowNormalization.normalize_nonneg_iff
#print axioms RowNormalization.weighted_normalize
#print axioms Adapters.ProximalGradientRows.snapshot_roundtrip
#print axioms Adapters.ProximalGradientRows.assumption_sum_preserved
#print axioms Adapters.ProximalGradientRows.normalizedUpper_check
#print axioms Imported.CompositeRows.zero_scale_rejected
#print axioms Imported.CompositeRows.PGThree.bound_check
#print axioms ActualFunction.ProximalGradientRowAudit.three_step_upper
