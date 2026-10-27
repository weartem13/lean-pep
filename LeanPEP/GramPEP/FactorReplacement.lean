import LeanPEP.GramPEP.UpperCertificateChecker
import LeanPEP.GramPEP.PSDFactorizationRealBridge

/-!
# Replacing untrusted factor representations without changing a certificate

A producer may discover new rank-one factors, but may NOT redefine the target
matrix from those factors. This file reuses the original PSD and upper checkers.
No producer correctness or completeness axiom is assumed. Negative matrix
witnesses certify the matrix only, not the falsity of a convergence theorem.
-/

namespace LeanPEP.GramPEP

/-- A rational negative quadratic value refutes the original rational PSD predicate. -/
theorem not_isGramPosSemidef_of_negative {m : ℕ}
    (G : Gram m ℚ) (v : VecExpr m ℚ) (hv : gramNormSq G v < 0) :
    ¬ IsGramPosSemidef G := by
  intro hG
  exact (not_lt_of_ge (hG.2 v)) hv

/-- The same rational vector refutes PSD after casting the matrix to the reals. -/
theorem not_isGramPosSemidef_real_of_negative {m : ℕ}
    (G : Gram m ℚ) (v : VecExpr m ℚ) (hv : gramNormSq G v < 0) :
    ¬ IsGramPosSemidef (castGramQ G) := by
  intro hG
  have hn := hG.2 (castVecQ v)
  rw [gramNormSq_castQ] at hn
  have hnQ : (0 : ℚ) ≤ gramNormSq G v := by exact_mod_cast hn
  exact (not_lt_of_ge hnQ) hv

/-- Asymmetry is a separate failure of the project's symmetric PSD predicate. -/
theorem not_isGramPosSemidef_of_asymmetry {m : ℕ}
    (G : Gram m ℚ) (i j : Fin m) (hij : G i j ≠ G j i) :
    ¬ IsGramPosSemidef G := by
  intro hG
  exact hij (hG.1 i j)

/-- Only replace the representation of the fixed dual matrix. -/
def UpperCertQ.withDualFactor {p m : ℕ} {model : ModelQ p m}
    (c : UpperCertQ model) (d : PSDFactorCertQ m) : UpperCertQ model :=
  { c with dualFactor := d }

@[simp] theorem UpperCertQ.withDualFactor_bound {p m : ℕ} {model : ModelQ p m}
    (c : UpperCertQ model) (d : PSDFactorCertQ m) :
    (c.withDualFactor d).bound = c.bound := rfl

@[simp] theorem UpperCertQ.withDualFactor_objective {p m : ℕ} {model : ModelQ p m}
    (c : UpperCertQ model) (d : PSDFactorCertQ m) :
    (c.withDualFactor d).objective = c.objective := rfl

@[simp] theorem UpperCertQ.withDualFactor_matrix {p m : ℕ} {model : ModelQ p m}
    (c : UpperCertQ model) (d : PSDFactorCertQ m) :
    (c.withDualFactor d).dualMatrix = c.dualMatrix := rfl

@[simp] theorem certificateRhsExprQ_withDualFactor {p m : ℕ} {model : ModelQ p m}
    (c : UpperCertQ model) (d : PSDFactorCertQ m) :
    certificateRhsExprQ (c.withDualFactor d) = certificateRhsExprQ c := rfl

/-- The original validity predicate accepts another exact factorization of the
same dual matrix; the coefficient identity and all multipliers are unchanged. -/
theorem UpperCertValidQ.withDualFactor {p m : ℕ} {model : ModelQ p m}
    {c : UpperCertQ model} (hc : UpperCertValidQ c) (d : PSDFactorCertQ m)
    (hd : checkPSDFactorQ c.dualMatrix d = true) :
    UpperCertValidQ (c.withDualFactor d) := by
  exact
    { interpWeights := hc.interpWeights
      assumptionWeights := hc.assumptionWeights
      dualValid := (checkPSDFactorQ_eq_true_iff c.dualMatrix d).mp hd
      identity := hc.identity }

/-- Accepted old upper certificate + accepted factors of its UNCHANGED matrix
imply acceptance by the same original upper checker. -/
theorem checkUpperCertQ_withDualFactor {p m : ℕ} {model : ModelQ p m}
    (c : UpperCertQ model) (d : PSDFactorCertQ m)
    (hc : checkUpperCertQ c = true)
    (hd : checkPSDFactorQ c.dualMatrix d = true) :
    checkUpperCertQ (c.withDualFactor d) = true := by
  exact checkUpperCertQ_complete _ ((checkUpperCertQ_sound c hc).withDualFactor d hd)

end LeanPEP.GramPEP
