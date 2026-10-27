import LeanPEP

open scoped NNReal
open LeanPEP LeanPEP.GramPEP
open LeanPEP.GramPEP.PerformanceLift
open LeanPEP.Adapters.ProximalGradientPerformance

#check substitute_embed
#check substitute_tau
#check substitute_add
#check substitute_scale
#check substitute_link
#check eval_embed
#check eval_tau
#check eval_substitute
#check eval_link
#check checkLiftQ_eq_true_iff
#check checkSourceQ_eq_true_iff
#check rows_feasible_iff
#check finite_upper_equivalence
#check assumption_sum_preserved
#check certificate_rhs_preserved
#check eliminatedUpper_check
#check performance_mass_eq_one
#check checked_performance_mass
#check checked_certificate
#check Imported.CompositePerformance.PGOne.bound_check
#check Imported.CompositePerformance.PGTwo.bound_check
#check Imported.CompositePerformance.PGThree.bound_check
#check Imported.CompositePerformance.PGUnit.bound_check
#check Imported.CompositePerformance.hidden_tau_source_rejected
#check Imported.CompositePerformance.wrong_performance_eliminated_passes
#check Imported.CompositePerformance.wrong_performance_joint_rejected
#check ActualFunction.ProximalGradientPerformanceAudit.upper_firstOrder
#check ActualFunction.ProximalGradientPerformanceAudit.three_step_upper

-- Generic dimensions and arbitrary (possibly nonsymmetric) real data.
example {p m : ℕ} (o : LinearExprQ p m) (e : LinearExprQ (p+1) m) (d : DataR (Fin p) m) :
    (substituteQ o e).evalR d = e.evalR (extendDataR d (o.evalR d)) := eval_substitute o e d

example (o : LinearExprQ 0 0) : substituteQ o (tauExprQ 0 0) = o := substitute_tau o

example {p m : ℕ} (o : LinearExprQ p m) : substituteQ o (linkExprQ o) = LinearExprQ.zero p m :=
  substitute_link o

-- Symbolic horizon, unchanged checker, no known base rate as a premise.
example {n : ℕ} (s : SourceQ n) (hs : checkLiftQ s = true) (c : UpperCertQ s.model)
    (hi : c.interpTerms = []) (hc : checkUpperCertQ c = true) :
    checkUpperCertQ (eliminatedUpperQ s c) = true := eliminatedUpper_check s hs c hi hc

example {n : ℕ} (s : SourceQ n) (c : UpperCertQ s.model) (hc : checkBoundQ s c = true) :
    performanceMassQ s c.assumptionTerms = 1 := checked_performance_mass s c hc

example : checkBoundQ Imported.CompositePerformance.PGThree.sourceQ Imported.CompositePerformance.PGThree.upperQ = true :=
  Imported.CompositePerformance.PGThree.bound_check

example : performanceMassQ Imported.CompositePerformance.PGTwo.sourceQ
    Imported.CompositePerformance.PGTwo.upperQ.assumptionTerms = 1 := Imported.CompositePerformance.PGTwo.performance_mass

example : checkSourceQ Imported.CompositePerformance.hiddenTauQ = false :=
  Imported.CompositePerformance.hidden_tau_source_rejected

example : checkBoundQ Imported.CompositePerformance.PGOne.sourceQ
    Imported.CompositePerformance.wrongPerformanceWeightQ = false := Imported.CompositePerformance.wrong_performance_joint_rejected

example : checkBoundQ Imported.CompositePerformance.PGOne.sourceQ Imported.CompositePerformance.implicitQ = false :=
  Imported.CompositePerformance.implicit_joint_rejected

example : (Imported.CompositePerformance.PGThree.upperQ.bound : ℝ) = 1/12 := by
  norm_num [Imported.CompositePerformance.PGThree.upperQ]

-- The old exact result is neither replaced nor weakened by this adapter.
example : IsGreatest
    (ActualFunction.ProximalGradientCanonical.oneDimensionalHilbertValues 7 (3 : ℝ≥0) 2) (3/8 : ℝ) := by
  convert ActualFunction.ProximalGradientCanonical.hilbert_tight_all 7
    (L := (3 : ℝ≥0)) (R := 2) (by norm_num) (by norm_num) using 1 <;> norm_num

example : IsGreatest
    (ActualFunction.ProximalGradientCanonical.oneDimensionalHilbertValues 7 (3 : ℝ≥0) 0) 0 := by
  convert ActualFunction.ProximalGradientCanonical.hilbert_tight_all 7
    (L := (3 : ℝ≥0)) (R := 0) (by norm_num) (by norm_num) using 1 <;> norm_num

#print axioms LeanPEP.GramPEP.PerformanceLift.eval_substitute
#print axioms LeanPEP.Adapters.ProximalGradientPerformance.finite_upper_equivalence
#print axioms LeanPEP.Adapters.ProximalGradientPerformance.eliminatedUpper_check
#print axioms LeanPEP.Adapters.ProximalGradientPerformance.performance_mass_eq_one
#print axioms LeanPEP.Imported.CompositePerformance.hidden_tau_source_rejected
#print axioms LeanPEP.Imported.CompositePerformance.wrong_performance_joint_rejected
#print axioms LeanPEP.Imported.CompositePerformance.PGThree.bound_check
#print axioms LeanPEP.ActualFunction.ProximalGradientPerformanceAudit.three_step_upper
