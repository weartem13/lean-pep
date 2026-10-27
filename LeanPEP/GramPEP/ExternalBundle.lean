import LeanPEP.GramPEP.PSDFactorizationRealBridge
import LeanPEP.GramPEP.UpperCertificateAudit

/-!
# Exact external Gram-bundle boundary

This module is the Lean-side target of the strict external Gram JSON importer.
The Python parser and code generator are deliberately outside the mathematical
trust base.  They may construct exact rational candidates, but Lean independently
checks:

* declared dimensions, ordering lengths, and artifact counts;
* exact agreement between imported sampled data and the fixed formulation;
* the primal Gram matrix through an exact PSD factorization;
* every ordered scalar interpolation inequality;
* every additional formulation assumption;
* the complete general Gram upper certificate and dual PSD factorization; and
* exact equality between the primal objective and the certified upper bound.

Point labels, Gram-basis labels, and assumption labels are retained as
provenance.  The mathematical semantics are determined by the typed arrays and
coefficient objects that Lean checks.
-/

namespace LeanPEP
namespace GramPEP

open scoped BigOperators

namespace LinearExprQ

/-- Exact rational evaluation of an affine-linear expression on rational Gram
data. -/
def evalQ {p m : ℕ}
    (e : LinearExprQ p m) (d : DataQ (Fin p) m) : ℚ :=
  e.constCoeff
    + ∑ i, e.valueCoeff i * d.value i
    + ∑ i, ∑ j, e.gramCoeff i j * d.gram i j

/-- Exact rational evaluation commutes with the rational-to-real data cast. -/
@[simp] theorem evalR_castDataQ
    {p m : ℕ} (e : LinearExprQ p m) (d : DataQ (Fin p) m) :
    e.evalR (castDataQ d) = (e.evalQ d : ℝ) := by
  simp [evalR, evalQ, castDataQ, castGramQ]

end LinearExprQ

/-- Exact rational realization of a fixed formulation. -/
structure RealizesModelExactQ {p m : ℕ}
    (model : ModelQ p m) (d : DataQ (Fin p) m) : Prop where
  position : ∀ i, d.position i = model.position i
  gradient : ∀ i, d.gradient i = model.gradient i

/-- Entrywise exact equality checker for rational coefficient vectors. -/
def checkVecExprEqQ {m : ℕ} (u v : VecExpr m ℚ) : Bool :=
  (gramIndices m).all (fun i => decide (u i = v i))

/-- The coefficient-vector checker exactly decides function equality. -/
theorem checkVecExprEqQ_eq_true_iff
    {m : ℕ} (u v : VecExpr m ℚ) :
    checkVecExprEqQ u v = true ↔ u = v := by
  unfold checkVecExprEqQ
  rw [List.all_eq_true]
  constructor
  · intro hall
    funext i
    exact of_decide_eq_true (hall i (mem_gramIndices i))
  · intro h i hi
    subst v
    exact decide_eq_true rfl

/-- Exact checker that sampled positions and gradients agree with the imported
model. -/
def checkDataRealizesModelQ {p m : ℕ}
    (model : ModelQ p m) (d : DataQ (Fin p) m) : Bool :=
  (pointIndices p).all (fun i =>
    checkVecExprEqQ (d.position i) (model.position i) &&
      checkVecExprEqQ (d.gradient i) (model.gradient i))

/-- The exact model/data checker decides proposition-level realization. -/
theorem checkDataRealizesModelQ_eq_true_iff
    {p m : ℕ} (model : ModelQ p m) (d : DataQ (Fin p) m) :
    checkDataRealizesModelQ model d = true ↔
      RealizesModelExactQ model d := by
  unfold checkDataRealizesModelQ
  rw [List.all_eq_true]
  constructor
  · intro hall
    refine { position := ?_, gradient := ?_ }
    · intro i
      have hi := hall i (mem_pointIndices i)
      have hparts :
          checkVecExprEqQ (d.position i) (model.position i) = true ∧
            checkVecExprEqQ (d.gradient i) (model.gradient i) = true := by
        simpa using hi
      exact (checkVecExprEqQ_eq_true_iff _ _).mp hparts.1
    · intro i
      have hi := hall i (mem_pointIndices i)
      have hparts :
          checkVecExprEqQ (d.position i) (model.position i) = true ∧
            checkVecExprEqQ (d.gradient i) (model.gradient i) = true := by
        simpa using hi
      exact (checkVecExprEqQ_eq_true_iff _ _).mp hparts.2
  · intro h i hi
    have hposition :=
      (checkVecExprEqQ_eq_true_iff _ _).mpr (h.position i)
    have hgradient :=
      (checkVecExprEqQ_eq_true_iff _ _).mpr (h.gradient i)
    simpa using And.intro hposition hgradient

/-- Exact realization implies realization of the cast real data. -/
theorem realizesModelExactQ_toReal
    {p m : ℕ} {model : ModelQ p m} {d : DataQ (Fin p) m}
    (h : RealizesModelExactQ model d) :
    RealizesModelQ model (castDataQ d) := by
  constructor
  · intro i
    change castVecQ (d.position i) = castVecQ (model.position i)
    rw [h.position i]
  · intro i
    change castVecQ (d.gradient i) = castVecQ (model.gradient i)
    rw [h.gradient i]

/-- Every ordered point pair in deterministic row-major order. -/
def pointIndexPairs (p : ℕ) : List (Fin p × Fin p) :=
  (pointIndices p).flatMap (fun i =>
    (pointIndices p).map (fun j => (i, j)))

@[simp] theorem mem_pointIndexPairs {p : ℕ} (i j : Fin p) :
    (i, j) ∈ pointIndexPairs p := by
  simp [pointIndexPairs]

/-- Exact Boolean checker for every ordered rational interpolation slack. -/
def checkInterpolationFeasibleQ
    {p m : ℕ} (d : DataQ (Fin p) m) : Bool :=
  (pointIndexPairs p).all (fun ij =>
    decide (0 ≤ interpolationSlack d ij.1 ij.2))

/-- The executable interpolation checker exactly decides rational
interpolation feasibility. -/
theorem checkInterpolationFeasibleQ_eq_true_iff
    {p m : ℕ} (d : DataQ (Fin p) m) :
    checkInterpolationFeasibleQ d = true ↔ InterpolationFeasible d := by
  unfold checkInterpolationFeasibleQ InterpolationFeasible
  rw [List.all_eq_true]
  constructor
  · intro hall i j
    exact of_decide_eq_true
      (hall (i, j) (mem_pointIndexPairs i j))
  · intro h ij hij
    exact decide_eq_true (h ij.1 ij.2)

/-- One exact negative interpolation slack. -/
structure InterpolationViolationQ (p : ℕ) where
  i : Fin p
  j : Fin p
  value : ℚ
  deriving DecidableEq, Repr

/-- Complete ordered list of negative interpolation slacks. -/
def interpolationViolationsQ
    {p m : ℕ} (d : DataQ (Fin p) m) :
    List (InterpolationViolationQ p) :=
  (pointIndexPairs p).flatMap (fun ij =>
    let value := interpolationSlack d ij.1 ij.2
    if value < 0 then
      [{ i := ij.1, j := ij.2, value := value }]
    else
      [])

/-- Every reported interpolation violation is strictly negative and records
the exact slack. -/
theorem mem_interpolationViolationsQ_sound
    {p m : ℕ} (d : DataQ (Fin p) m)
    (e : InterpolationViolationQ p)
    (h : e ∈ interpolationViolationsQ d) :
    e.value = interpolationSlack d e.i e.j ∧ e.value < 0 := by
  unfold interpolationViolationsQ at h
  simp only [List.mem_flatMap] at h
  rcases h with ⟨ij, hij, hitem⟩
  rcases ij with ⟨i, j⟩
  by_cases hneg : interpolationSlack d i j < 0
  · simp [hneg] at hitem
    subst e
    exact ⟨rfl, hneg⟩
  · simp [hneg] at hitem

/-- Exact rational feasibility of every imported formulation assumption. -/
def AssumptionsFeasibleQ {p m : ℕ}
    (model : ModelQ p m) (d : DataQ (Fin p) m) : Prop :=
  ∀ k : Fin model.assumptions.length,
    0 ≤ (model.assumptions.get k).evalQ d

/-- Deterministic assumption-index enumeration. -/
def assumptionIndices {p m : ℕ} (model : ModelQ p m) :
    List (Fin model.assumptions.length) :=
  List.finRange model.assumptions.length

@[simp] theorem mem_assumptionIndices
    {p m : ℕ} (model : ModelQ p m)
    (k : Fin model.assumptions.length) :
    k ∈ assumptionIndices model := by
  simp [assumptionIndices]

/-- Exact Boolean checker for every formulation assumption on the imported
primal datum. -/
def checkAssumptionsFeasibleQ {p m : ℕ}
    (model : ModelQ p m) (d : DataQ (Fin p) m) : Bool :=
  (assumptionIndices model).all (fun k =>
    decide (0 ≤ (model.assumptions.get k).evalQ d))

/-- The assumption checker exactly decides rational assumption feasibility. -/
theorem checkAssumptionsFeasibleQ_eq_true_iff
    {p m : ℕ} (model : ModelQ p m) (d : DataQ (Fin p) m) :
    checkAssumptionsFeasibleQ model d = true ↔
      AssumptionsFeasibleQ model d := by
  unfold checkAssumptionsFeasibleQ AssumptionsFeasibleQ
  rw [List.all_eq_true]
  constructor
  · intro hall k
    exact of_decide_eq_true
      (hall k (mem_assumptionIndices model k))
  · intro h k hk
    exact decide_eq_true (h k)

/-- Rational assumption feasibility implies real assumption feasibility after
casting the imported primal data. -/
theorem assumptionsFeasibleQ_toReal
    {p m : ℕ} (model : ModelQ p m) (d : DataQ (Fin p) m)
    (h : AssumptionsFeasibleQ model d) :
    AssumptionsFeasibleR model (castDataQ d) := by
  intro k
  rw [LinearExprQ.evalR_castDataQ]
  exact Rat.cast_nonneg.mpr (h k)

/-- One exact negative formulation-assumption value. -/
structure AssumptionViolationQ where
  index : Nat
  value : ℚ
  deriving DecidableEq, Repr

/-- Complete deterministic list of violated formulation assumptions. -/
def assumptionViolationsQ {p m : ℕ}
    (model : ModelQ p m) (d : DataQ (Fin p) m) :
    List AssumptionViolationQ :=
  (assumptionIndices model).flatMap (fun k =>
    let value := (model.assumptions.get k).evalQ d
    if value < 0 then [{ index := k.val, value := value }] else [])

/-- Every reported formulation-assumption violation is strictly negative. -/
theorem mem_assumptionViolationsQ_sound
    {p m : ℕ} (model : ModelQ p m) (d : DataQ (Fin p) m)
    (e : AssumptionViolationQ)
    (h : e ∈ assumptionViolationsQ model d) :
    e.value < 0 := by
  unfold assumptionViolationsQ at h
  simp only [List.mem_flatMap] at h
  rcases h with ⟨k, hk, hitem⟩
  simp at hitem
  rcases hitem with ⟨hneg, rfl⟩
  exact hneg

/-- Metadata carried across the exact external Gram-bundle boundary.  Typed
point and basis dimensions are fixed by the bundle parameters; declared counts
remain explicit so source-model mistakes are diagnosed rather than repaired. -/
structure ImportMetadataQ (p m : ℕ) where
  schemaVersion : Nat
  declaredPointCount : Nat
  declaredGramBasisCount : Nat
  declaredOrderedPairCount : Nat
  declaredAssumptionCount : Nat
  declaredPrimalFactorCount : Nat
  declaredUpperInterpTermCount : Nat
  declaredUpperAssumptionTermCount : Nat
  declaredDualFactorCount : Nat
  pointOrder : List String
  gramBasisOrder : List String
  assumptionOrder : List String
  sourceName : String
  sourceSha256 : String
  generatorVersion : String
  deriving DecidableEq, Repr

/-- Complete exact external Gram bundle. -/
structure ExactGramBundleQ (p m : ℕ) where
  metadata : ImportMetadataQ p m
  model : ModelQ p m
  primal : DataQ (Fin p) m
  primalFactor : PSDFactorCertQ m
  upper : UpperCertQ model

/-- Expected number of ordered interpolation constraints. -/
def expectedOrderedPairCountQ (p : ℕ) : Nat := p * p

/-- Exact metadata/count audit. -/
def checkImportMetadataQ {p m : ℕ} (b : ExactGramBundleQ p m) : Bool :=
  decide (b.metadata.schemaVersion = 1) &&
    (decide (b.metadata.declaredPointCount = p) &&
      (decide (b.metadata.declaredGramBasisCount = m) &&
        (decide
          (b.metadata.declaredOrderedPairCount = expectedOrderedPairCountQ p) &&
          (decide
            (b.metadata.declaredAssumptionCount = b.model.assumptions.length) &&
            (decide
              (b.metadata.declaredPrimalFactorCount =
                b.primalFactor.factors.length) &&
              (decide
                (b.metadata.declaredUpperInterpTermCount =
                  b.upper.interpTerms.length) &&
                (decide
                  (b.metadata.declaredUpperAssumptionTermCount =
                    b.upper.assumptionTerms.length) &&
                  (decide
                    (b.metadata.declaredDualFactorCount =
                      b.upper.dualFactor.factors.length) &&
                    (decide (b.metadata.pointOrder.length = p) &&
                      (decide (b.metadata.gramBasisOrder.length = m) &&
                        decide
                          (b.metadata.assumptionOrder.length =
                            b.model.assumptions.length)))))))))))

/-- Check every mathematical obligation in an exact external Gram bundle. -/
def checkExactGramBundleQ {p m : ℕ}
    (b : ExactGramBundleQ p m) : Bool :=
  checkImportMetadataQ b &&
    (checkDataRealizesModelQ b.model b.primal &&
      (checkPSDFactorQ b.primal.gram b.primalFactor &&
        (checkInterpolationFeasibleQ b.primal &&
          (checkAssumptionsFeasibleQ b.model b.primal &&
            (checkUpperCertQ b.upper &&
              decide (b.upper.objective.evalQ b.primal = b.upper.bound))))))

/-- Decompose successful exact bundle acceptance. -/
theorem checkExactGramBundleQ_components
    {p m : ℕ} (b : ExactGramBundleQ p m)
    (h : checkExactGramBundleQ b = true) :
    checkImportMetadataQ b = true ∧
      checkDataRealizesModelQ b.model b.primal = true ∧
      checkPSDFactorQ b.primal.gram b.primalFactor = true ∧
      checkInterpolationFeasibleQ b.primal = true ∧
      checkAssumptionsFeasibleQ b.model b.primal = true ∧
      checkUpperCertQ b.upper = true ∧
      b.upper.objective.evalQ b.primal = b.upper.bound := by
  simpa [checkExactGramBundleQ] using h

/-- Successful exact bundle acceptance reconstructs a real feasible attaining
primal witness and the universal real upper theorem for the imported model. -/
theorem checkExactGramBundleQ_sound_real
    {p m : ℕ} (b : ExactGramBundleQ p m)
    (h : checkExactGramBundleQ b = true) :
    checkImportMetadataQ b = true ∧
      RealizesModelQ b.model (castDataQ b.primal) ∧
      CoreFeasible (castDataQ b.primal) ∧
      AssumptionsFeasibleR b.model (castDataQ b.primal) ∧
      b.upper.objective.evalR (castDataQ b.primal) =
        (b.upper.bound : ℝ) ∧
      ∀ d : DataR (Fin p) m,
        RealizesModelQ b.model d →
        CoreFeasible d →
        AssumptionsFeasibleR b.model d →
        b.upper.objective.evalR d ≤ (b.upper.bound : ℝ) := by
  have hparts := checkExactGramBundleQ_components b h
  have hrealizesQ : RealizesModelExactQ b.model b.primal :=
    (checkDataRealizesModelQ_eq_true_iff _ _).mp hparts.2.1
  have hinterpQ : InterpolationFeasible b.primal :=
    (checkInterpolationFeasibleQ_eq_true_iff b.primal).mp hparts.2.2.2.1
  have hassumptionsQ : AssumptionsFeasibleQ b.model b.primal :=
    (checkAssumptionsFeasibleQ_eq_true_iff _ _).mp
      hparts.2.2.2.2.1
  have hcoreR : CoreFeasible (castDataQ b.primal) :=
    ⟨checkPSDFactorQ_sound_real b.primal.gram b.primalFactor
        hparts.2.2.1,
      interpolationFeasibleQ_toReal b.primal hinterpQ⟩
  refine ⟨hparts.1, realizesModelExactQ_toReal hrealizesQ,
    hcoreR, assumptionsFeasibleQ_toReal b.model b.primal hassumptionsQ,
    ?_, ?_⟩
  · calc
      b.upper.objective.evalR (castDataQ b.primal) =
          (b.upper.objective.evalQ b.primal : ℝ) :=
        LinearExprQ.evalR_castDataQ b.upper.objective b.primal
      _ = (b.upper.bound : ℝ) := by
        rw [hparts.2.2.2.2.2.2]
  · intro d hrealizes hcore hassumptions
    exact checkUpperCertQ_sound_real b.upper
      hparts.2.2.2.2.2.1 d hrealizes hcore hassumptions

/-- One metadata/count field. -/
inductive ImportMetadataFieldQ where
  | schemaVersion
  | pointCount
  | gramBasisCount
  | orderedPairCount
  | assumptionCount
  | primalFactorCount
  | upperInterpTermCount
  | upperAssumptionTermCount
  | dualFactorCount
  | pointOrderCount
  | gramBasisOrderCount
  | assumptionOrderCount
  deriving DecidableEq, Repr

/-- One exact natural-number metadata mismatch. -/
structure ImportMetadataMismatchQ where
  field : ImportMetadataFieldQ
  expected : Nat
  actual : Nat
  deriving DecidableEq, Repr

/-- Return a singleton metadata mismatch precisely when counts differ. -/
def importMetadataMismatchQ
    (field : ImportMetadataFieldQ)
    (expected actual : Nat) : List ImportMetadataMismatchQ :=
  if expected = actual then [] else
    [{ field := field, expected := expected, actual := actual }]

/-- Complete deterministic metadata mismatch report. -/
def importMetadataMismatchesQ {p m : ℕ}
    (b : ExactGramBundleQ p m) : List ImportMetadataMismatchQ :=
  importMetadataMismatchQ .schemaVersion 1 b.metadata.schemaVersion ++
    importMetadataMismatchQ .pointCount p b.metadata.declaredPointCount ++
    importMetadataMismatchQ .gramBasisCount m
      b.metadata.declaredGramBasisCount ++
    importMetadataMismatchQ .orderedPairCount
      (expectedOrderedPairCountQ p) b.metadata.declaredOrderedPairCount ++
    importMetadataMismatchQ .assumptionCount b.model.assumptions.length
      b.metadata.declaredAssumptionCount ++
    importMetadataMismatchQ .primalFactorCount b.primalFactor.factors.length
      b.metadata.declaredPrimalFactorCount ++
    importMetadataMismatchQ .upperInterpTermCount b.upper.interpTerms.length
      b.metadata.declaredUpperInterpTermCount ++
    importMetadataMismatchQ .upperAssumptionTermCount
      b.upper.assumptionTerms.length
      b.metadata.declaredUpperAssumptionTermCount ++
    importMetadataMismatchQ .dualFactorCount b.upper.dualFactor.factors.length
      b.metadata.declaredDualFactorCount ++
    importMetadataMismatchQ .pointOrderCount p b.metadata.pointOrder.length ++
    importMetadataMismatchQ .gramBasisOrderCount m
      b.metadata.gramBasisOrder.length ++
    importMetadataMismatchQ .assumptionOrderCount b.model.assumptions.length
      b.metadata.assumptionOrder.length

/-- Imported sampled-data field. -/
inductive ModelDataFieldQ where
  | position
  | gradient
  deriving DecidableEq, Repr

/-- One exact model/data coefficient mismatch. -/
structure ModelDataMismatchQ (p m : ℕ) where
  field : ModelDataFieldQ
  point : Fin p
  coordinate : Fin m
  expected : ℚ
  actual : ℚ
  deriving DecidableEq, Repr

/-- Complete exact model/data mismatch report. -/
def modelDataMismatchesQ {p m : ℕ}
    (model : ModelQ p m) (d : DataQ (Fin p) m) :
    List (ModelDataMismatchQ p m) :=
  (pointIndices p).flatMap (fun i =>
    (gramIndices m).flatMap (fun k =>
      let positionItems :=
        if model.position i k = d.position i k then [] else
          [{ field := ModelDataFieldQ.position,
             point := i, coordinate := k,
             expected := model.position i k,
             actual := d.position i k }]
      let gradientItems :=
        if model.gradient i k = d.gradient i k then [] else
          [{ field := ModelDataFieldQ.gradient,
             point := i, coordinate := k,
             expected := model.gradient i k,
             actual := d.gradient i k }]
      positionItems ++ gradientItems))

/-- Exact primal objective-attainment mismatch. -/
structure ObjectiveMismatchQ where
  witnessValue : ℚ
  certifiedBound : ℚ
  deriving DecidableEq, Repr

/-- Return the exact lower/upper mismatch, if any. -/
def objectiveMismatchesQ {p m : ℕ}
    {model : ModelQ p m} (c : UpperCertQ model)
    (d : DataQ (Fin p) m) : List ObjectiveMismatchQ :=
  let witnessValue := c.objective.evalQ d
  if witnessValue = c.bound then [] else
    [{ witnessValue := witnessValue, certifiedBound := c.bound }]

/-- Complete non-short-circuiting exact external Gram-bundle audit. -/
structure ExactGramBundleAuditReportQ (p m : ℕ) where
  accepted : Bool
  metadataMismatches : List ImportMetadataMismatchQ
  modelDataMismatches : List (ModelDataMismatchQ p m)
  primalPSDAudit : PSDFactorAuditReportQ m
  interpolationViolations : List (InterpolationViolationQ p)
  assumptionViolations : List AssumptionViolationQ
  upperAudit : UpperCertAuditReportQ p m
  objectiveMismatches : List ObjectiveMismatchQ
  deriving DecidableEq, Repr

/-- Audit every exact bundle obligation without changing the acceptance gate. -/
def auditExactGramBundleQ {p m : ℕ}
    (b : ExactGramBundleQ p m) : ExactGramBundleAuditReportQ p m :=
  { accepted := checkExactGramBundleQ b
    metadataMismatches := importMetadataMismatchesQ b
    modelDataMismatches := modelDataMismatchesQ b.model b.primal
    primalPSDAudit := auditPSDFactorQ b.primal.gram b.primalFactor
    interpolationViolations := interpolationViolationsQ b.primal
    assumptionViolations := assumptionViolationsQ b.model b.primal
    upperAudit := auditUpperCertQ b.upper
    objectiveMismatches := objectiveMismatchesQ b.upper b.primal }

/-- Audit acceptance uses exactly the Boolean exact-bundle checker. -/
theorem auditExactGramBundleQ_accepted_iff
    {p m : ℕ} (b : ExactGramBundleQ p m) :
    (auditExactGramBundleQ b).accepted = true ↔
      checkExactGramBundleQ b = true := by
  rfl

/-- Accepted structured audits inherit the complete real soundness theorem. -/
theorem auditExactGramBundleQ_sound_real
    {p m : ℕ} (b : ExactGramBundleQ p m)
    (h : (auditExactGramBundleQ b).accepted = true) :
    checkImportMetadataQ b = true ∧
      RealizesModelQ b.model (castDataQ b.primal) ∧
      CoreFeasible (castDataQ b.primal) ∧
      AssumptionsFeasibleR b.model (castDataQ b.primal) ∧
      b.upper.objective.evalR (castDataQ b.primal) =
        (b.upper.bound : ℝ) ∧
      ∀ d : DataR (Fin p) m,
        RealizesModelQ b.model d →
        CoreFeasible d →
        AssumptionsFeasibleR b.model d →
        b.upper.objective.evalR d ≤ (b.upper.bound : ℝ) := by
  exact checkExactGramBundleQ_sound_real b
    (by simpa [auditExactGramBundleQ] using h)

end GramPEP
end LeanPEP
