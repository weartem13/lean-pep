import LeanPEP.GramPEP.UpperCertificate

/-!
# Executable general Gram upper-certificate checker

The checker verifies, with exact rational arithmetic:

1. every interpolation multiplier is nonnegative;
2. every formulation-assumption multiplier is nonnegative;
3. the dual matrix has an accepted exact PSD factorization; and
4. the affine-linear identity holds coefficient by coefficient.

The soundness theorem applies every accepted certificate to any real Gram datum
that realizes the fixed model, is core feasible, and satisfies the additional
model assumptions.
-/

namespace LeanPEP
namespace GramPEP

/-- Exact coefficient equality for affine-linear value/Gram expressions. -/
def checkLinearExprEqQ {p m : ℕ}
    (a b : LinearExprQ p m) : Bool :=
  decide (a.constCoeff = b.constCoeff) &&
    ((pointIndices p).all (fun i =>
      decide (a.valueCoeff i = b.valueCoeff i)) &&
    (gramIndexPairs m).all (fun ij =>
      decide (a.gramCoeff ij.1 ij.2 = b.gramCoeff ij.1 ij.2)))

/-- Boolean coefficient equality is sound. -/
theorem checkLinearExprEqQ_sound {p m : ℕ}
    (a b : LinearExprQ p m)
    (h : checkLinearExprEqQ a b = true) :
    a = b := by
  have hparts :
      a.constCoeff = b.constCoeff ∧
      (∀ i ∈ pointIndices p, a.valueCoeff i = b.valueCoeff i) ∧
      (∀ ij ∈ gramIndexPairs m,
        a.gramCoeff ij.1 ij.2 = b.gramCoeff ij.1 ij.2) := by
    simpa [checkLinearExprEqQ, List.all_eq_true] using h
  apply LinearExprQ.ext
  · exact hparts.1
  · funext i
    exact hparts.2.1 i (mem_pointIndices i)
  · funext i j
    exact hparts.2.2 (i, j) (mem_gramIndexPairs i j)

/-- Equal coefficient objects are accepted. -/
theorem checkLinearExprEqQ_complete {p m : ℕ}
    (a b : LinearExprQ p m) (h : a = b) :
    checkLinearExprEqQ a b = true := by
  subst b
  simp [checkLinearExprEqQ]

/-- The coefficient checker exactly decides expression equality. -/
theorem checkLinearExprEqQ_eq_true_iff {p m : ℕ}
    (a b : LinearExprQ p m) :
    checkLinearExprEqQ a b = true ↔ a = b := by
  constructor
  · exact checkLinearExprEqQ_sound a b
  · exact checkLinearExprEqQ_complete a b

/-- Proposition-level meaning of a valid general Gram upper certificate. -/
structure UpperCertValidQ {p m : ℕ} {model : ModelQ p m}
    (c : UpperCertQ model) : Prop where
  interpWeights : ∀ t ∈ c.interpTerms, 0 ≤ t.weight
  assumptionWeights : ∀ t ∈ c.assumptionTerms, 0 ≤ t.weight
  dualValid : PSDFactorValidQ c.dualMatrix c.dualFactor
  identity :
    certificateRhsExprQ c = upperTargetExprQ c.bound c.objective

/-- Executably check all general Gram upper-certificate obligations. -/
def checkUpperCertQ {p m : ℕ} {model : ModelQ p m}
    (c : UpperCertQ model) : Bool :=
  c.interpTerms.all (fun t => decide (0 ≤ t.weight)) &&
    (c.assumptionTerms.all (fun t => decide (0 ≤ t.weight)) &&
      (checkPSDFactorQ c.dualMatrix c.dualFactor &&
        checkLinearExprEqQ
          (certificateRhsExprQ c)
          (upperTargetExprQ c.bound c.objective)))

/-- Boolean acceptance has the proposition-level certificate meaning. -/
theorem checkUpperCertQ_sound {p m : ℕ} {model : ModelQ p m}
    (c : UpperCertQ model)
    (h : checkUpperCertQ c = true) :
    UpperCertValidQ c := by
  have hparts :
      (∀ t ∈ c.interpTerms, 0 ≤ t.weight) ∧
      (∀ t ∈ c.assumptionTerms, 0 ≤ t.weight) ∧
      checkPSDFactorQ c.dualMatrix c.dualFactor = true ∧
      checkLinearExprEqQ
        (certificateRhsExprQ c)
        (upperTargetExprQ c.bound c.objective) = true := by
    simpa [checkUpperCertQ, List.all_eq_true] using h
  exact
    { interpWeights := hparts.1
      assumptionWeights := hparts.2.1
      dualValid :=
        (checkPSDFactorQ_eq_true_iff _ _).mp hparts.2.2.1
      identity := checkLinearExprEqQ_sound _ _ hparts.2.2.2 }

/-- Every propositionally valid certificate is accepted. -/
theorem checkUpperCertQ_complete {p m : ℕ} {model : ModelQ p m}
    (c : UpperCertQ model)
    (h : UpperCertValidQ c) :
    checkUpperCertQ c = true := by
  have hinterp :
      c.interpTerms.all (fun t => decide (0 ≤ t.weight)) = true := by
    apply List.all_eq_true.mpr
    intro t ht
    exact decide_eq_true (h.interpWeights t ht)
  have hassumptions :
      c.assumptionTerms.all (fun t => decide (0 ≤ t.weight)) = true := by
    apply List.all_eq_true.mpr
    intro t ht
    exact decide_eq_true (h.assumptionWeights t ht)
  have hdual : checkPSDFactorQ c.dualMatrix c.dualFactor = true :=
    (checkPSDFactorQ_eq_true_iff _ _).mpr h.dualValid
  have hid :
      checkLinearExprEqQ
        (certificateRhsExprQ c)
        (upperTargetExprQ c.bound c.objective) = true :=
    checkLinearExprEqQ_complete _ _ h.identity
  simp [checkUpperCertQ, hinterp, hassumptions, hdual, hid]

/-- The general Gram upper checker exactly decides certificate validity. -/
theorem checkUpperCertQ_eq_true_iff {p m : ℕ} {model : ModelQ p m}
    (c : UpperCertQ model) :
    checkUpperCertQ c = true ↔ UpperCertValidQ c := by
  constructor
  · exact checkUpperCertQ_sound c
  · exact checkUpperCertQ_complete c

/-- Nonnegative interpolation multipliers applied to core-feasible data produce
a nonnegative total. -/
theorem interpTermsValueR_nonneg {p m : ℕ}
    (d : DataR (Fin p) m) (hcore : CoreFeasible d)
    (terms : List (InterpTermQ p))
    (hweights : ∀ t ∈ terms, 0 ≤ t.weight) :
    0 ≤ interpTermsValueR d terms := by
  revert hweights
  induction terms with
  | nil =>
      intro hweights
      simp [interpTermsValueR]
  | cons t ts ih =>
      intro hweights
      have hwQ : 0 ≤ t.weight := hweights t (by simp)
      have hwR : 0 ≤ (t.weight : ℝ) := Rat.cast_nonneg.mpr hwQ
      have hs : 0 ≤ interpolationSlack d t.i t.j := hcore.2 t.i t.j
      have htailWeights : ∀ u ∈ ts, 0 ≤ u.weight := by
        intro u hu
        exact hweights u (by simp [hu])
      have htail := ih htailWeights
      simp only [interpTermsValueR]
      exact add_nonneg (mul_nonneg hwR hs) htail

/-- Nonnegative assumption multipliers applied to feasible assumptions produce
a nonnegative total. -/
theorem assumptionTermsValueR_nonneg {p m : ℕ}
    (model : ModelQ p m) (d : DataR (Fin p) m)
    (hassumptions : AssumptionsFeasibleR model d)
    (terms : List (AssumptionTermQ model))
    (hweights : ∀ t ∈ terms, 0 ≤ t.weight) :
    0 ≤ assumptionTermsValueR model d terms := by
  revert hweights
  induction terms with
  | nil =>
      intro hweights
      simp [assumptionTermsValueR]
  | cons t ts ih =>
      intro hweights
      have hwQ : 0 ≤ t.weight := hweights t (by simp)
      have hwR : 0 ≤ (t.weight : ℝ) := Rat.cast_nonneg.mpr hwQ
      have ha : 0 ≤ (model.assumptions.get t.index).evalR d :=
        hassumptions t.index
      have htailWeights : ∀ u ∈ ts, 0 ≤ u.weight := by
        intro u hu
        exact hweights u (by simp [hu])
      have htail := ih htailWeights
      simp only [assumptionTermsValueR]
      exact add_nonneg (mul_nonneg hwR ha) htail

/-- Pairing with the zero rational matrix is zero. -/
@[simp] theorem gramPairingR_zero {m : ℕ} (G : Gram m ℝ) :
    gramPairingR (0 : Gram m ℚ) G = 0 := by
  simp [gramPairingR]

/-- The rational/real pairing is additive in its rational matrix argument. -/
@[simp] theorem gramPairingR_add {m : ℕ}
    (S T : Gram m ℚ) (G : Gram m ℝ) :
    gramPairingR (S + T) G = gramPairingR S G + gramPairingR T G := by
  simp [gramPairingR, Finset.sum_add_distrib, add_mul]

/-- One weighted rank-one dual factor pairs with the primal Gram matrix as one
weighted represented squared norm. -/
theorem gramPairingR_weightedOuterQ {m : ℕ}
    (t : RankOneFactorQ m) (G : Gram m ℝ) :
    gramPairingR (weightedOuterQ t) G =
      (t.weight : ℝ) * gramNormSq G (castVecQ t.vector) := by
  calc
    gramPairingR (weightedOuterQ t) G =
        (t.weight : ℝ) *
          (∑ i, ∑ j,
            (t.vector i : ℝ) * G i j * (t.vector j : ℝ)) := by
      unfold gramPairingR weightedOuterQ
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Rat.cast_mul]
      ring
    _ = (t.weight : ℝ) * gramNormSq G (castVecQ t.vector) := by
      rfl

/-- Pairing with a reconstructed dual matrix is the sum of weighted primal Gram
norms. -/
noncomputable def dualFactorsValueR {m : ℕ}
    (G : Gram m ℝ) : List (RankOneFactorQ m) → ℝ
  | [] => 0
  | t :: ts =>
      (t.weight : ℝ) * gramNormSq G (castVecQ t.vector)
        + dualFactorsValueR G ts

@[simp] theorem gramPairingR_factorGramQ {m : ℕ}
    (factors : List (RankOneFactorQ m)) (G : Gram m ℝ) :
    gramPairingR (factorGramQ factors) G =
      dualFactorsValueR G factors := by
  induction factors with
  | nil =>
      simp [factorGramQ, dualFactorsValueR]
  | cons t ts ih =>
      simp [factorGramQ, dualFactorsValueR, ih,
        gramPairingR_weightedOuterQ]

/-- Nonnegative dual-factor weights pair nonnegatively with a PSD primal Gram
matrix. -/
theorem dualFactorsValueR_nonneg {m : ℕ}
    (G : Gram m ℝ) (hG : IsGramPosSemidef G)
    (factors : List (RankOneFactorQ m))
    (hweights : ∀ t ∈ factors, 0 ≤ t.weight) :
    0 ≤ dualFactorsValueR G factors := by
  revert hweights
  induction factors with
  | nil =>
      intro hweights
      simp [dualFactorsValueR]
  | cons t ts ih =>
      intro hweights
      have hwQ : 0 ≤ t.weight := hweights t (by simp)
      have hwR : 0 ≤ (t.weight : ℝ) := Rat.cast_nonneg.mpr hwQ
      have hnorm : 0 ≤ gramNormSq G (castVecQ t.vector) :=
        hG.2 (castVecQ t.vector)
      have htailWeights : ∀ u ∈ ts, 0 ≤ u.weight := by
        intro u hu
        exact hweights u (by simp [hu])
      have htail := ih htailWeights
      simp only [dualFactorsValueR]
      exact add_nonneg (mul_nonneg hwR hnorm) htail

/-- An exact rational PSD factor certificate makes the dual pairing
nonnegative against every real PSD primal Gram matrix. -/
theorem gramPairingR_nonneg_of_valid {m : ℕ}
    (S : Gram m ℚ) (cert : PSDFactorCertQ m)
    (hS : PSDFactorValidQ S cert)
    (G : Gram m ℝ) (hG : IsGramPosSemidef G) :
    0 ≤ gramPairingR S G := by
  rw [← hS.identity, gramPairingR_factorGramQ]
  exact dualFactorsValueR_nonneg G hG cert.factors hS.weights

/-- A propositionally valid general Gram certificate proves its claimed upper
bound for every real feasible realization. -/
theorem upperCertValidQ_sound_real {p m : ℕ} {model : ModelQ p m}
    (c : UpperCertQ model) (hc : UpperCertValidQ c)
    (d : DataR (Fin p) m)
    (hrealizes : RealizesModelQ model d)
    (hcore : CoreFeasible d)
    (hassumptions : AssumptionsFeasibleR model d) :
    c.objective.evalR d ≤ (c.bound : ℝ) := by
  have hinterp : 0 ≤ interpTermsValueR d c.interpTerms :=
    interpTermsValueR_nonneg d hcore c.interpTerms hc.interpWeights
  have hassumptionTerms :
      0 ≤ assumptionTermsValueR model d c.assumptionTerms :=
    assumptionTermsValueR_nonneg model d hassumptions
      c.assumptionTerms hc.assumptionWeights
  have hdual : 0 ≤ gramPairingR c.dualMatrix d.gram :=
    gramPairingR_nonneg_of_valid c.dualMatrix c.dualFactor
      hc.dualValid d.gram hcore.1
  have htotal : 0 ≤ certificateRhsValueR c d := by
    unfold certificateRhsValueR
    exact add_nonneg (add_nonneg hinterp hassumptionTerms) hdual
  have hidentity :
      (c.bound : ℝ) - c.objective.evalR d =
        certificateRhsValueR c d := by
    have heval := congrArg
      (fun e : LinearExprQ p m => e.evalR d) hc.identity
    rw [evalR_certificateRhsExprQ c d hrealizes hcore.1.1,
      evalR_upperTargetExprQ] at heval
    exact heval.symm
  nlinarith

/-- An accepted executable general Gram certificate proves its claimed upper
bound. -/
theorem checkUpperCertQ_sound_real {p m : ℕ} {model : ModelQ p m}
    (c : UpperCertQ model)
    (h : checkUpperCertQ c = true)
    (d : DataR (Fin p) m)
    (hrealizes : RealizesModelQ model d)
    (hcore : CoreFeasible d)
    (hassumptions : AssumptionsFeasibleR model d) :
    c.objective.evalR d ≤ (c.bound : ℝ) :=
  upperCertValidQ_sound_real c (checkUpperCertQ_sound c h)
    d hrealizes hcore hassumptions

end GramPEP
end LeanPEP
