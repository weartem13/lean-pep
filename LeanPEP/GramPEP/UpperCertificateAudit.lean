import LeanPEP.GramPEP.UpperCertificateChecker

/-!
# Structured diagnostics for general Gram upper certificates

The Boolean checker in `UpperCertificateChecker.lean` remains the authoritative
mathematical acceptance gate.  This module adds a deterministic exact audit
report that collects every currently checkable failure category:

* all negative interpolation multipliers;
* all negative formulation-assumption multipliers;
* the complete nested dual PSD-factorization audit; and
* every affine-linear identity coefficient mismatch.

All values are exact rationals.  The report never changes the certificate and
never introduces a tolerance.
-/

namespace LeanPEP
namespace GramPEP

/-- One negative interpolation multiplier, retaining its certificate-list
position and ordered point pair. -/
structure NegativeInterpWeightQ (p : ℕ) where
  index : Nat
  weight : ℚ
  i : Fin p
  j : Fin p
  deriving DecidableEq, Repr

/-- Scan interpolation multipliers while retaining deterministic list indices. -/
def negativeInterpWeightsFromQ {p : ℕ} :
    Nat → List (InterpTermQ p) → List (NegativeInterpWeightQ p)
  | _, [] => []
  | k, t :: ts =>
      let rest := negativeInterpWeightsFromQ (k + 1) ts
      if t.weight < 0 then
        { index := k, weight := t.weight, i := t.i, j := t.j } :: rest
      else
        rest

/-- Complete report of negative interpolation multipliers. -/
def negativeInterpWeightsQ {p : ℕ}
    (terms : List (InterpTermQ p)) : List (NegativeInterpWeightQ p) :=
  negativeInterpWeightsFromQ 0 terms

/-- One negative formulation-assumption multiplier.  `index` is the term's
zero-based certificate-list position; `assumptionIndex` is the referenced
model-assumption index. -/
structure NegativeAssumptionWeightQ where
  index : Nat
  assumptionIndex : Nat
  weight : ℚ
  deriving DecidableEq, Repr

/-- Scan assumption multipliers while retaining deterministic list indices. -/
def negativeAssumptionWeightsFromQ
    {p m : ℕ} {model : ModelQ p m} :
    Nat → List (AssumptionTermQ model) →
      List NegativeAssumptionWeightQ
  | _, [] => []
  | k, t :: ts =>
      let rest := negativeAssumptionWeightsFromQ (k + 1) ts
      if t.weight < 0 then
        { index := k,
          assumptionIndex := t.index.val,
          weight := t.weight } :: rest
      else
        rest

/-- Complete report of negative formulation-assumption multipliers. -/
def negativeAssumptionWeightsQ
    {p m : ℕ} {model : ModelQ p m}
    (terms : List (AssumptionTermQ model)) :
    List NegativeAssumptionWeightQ :=
  negativeAssumptionWeightsFromQ 0 terms

/-- Location of one affine-linear coefficient. -/
inductive LinearCoeffLocationQ (p m : ℕ) where
  | const
  | value (i : Fin p)
  | gram (i j : Fin m)
  deriving DecidableEq, Repr

/-- Read one coefficient at a typed affine-linear location. -/
def linearCoeffAtQ {p m : ℕ}
    (e : LinearExprQ p m) : LinearCoeffLocationQ p m → ℚ
  | .const => e.constCoeff
  | .value i => e.valueCoeff i
  | .gram i j => e.gramCoeff i j

/-- Deterministic order of every affine-linear coefficient location. -/
def linearCoeffLocationsQ (p m : ℕ) :
    List (LinearCoeffLocationQ p m) :=
  [LinearCoeffLocationQ.const] ++
    (pointIndices p).map (fun i => LinearCoeffLocationQ.value i) ++
    (gramIndexPairs m).map
      (fun ij => LinearCoeffLocationQ.gram ij.1 ij.2)

/-- One exact affine-linear coefficient mismatch. -/
structure LinearCoeffMismatchQ (p m : ℕ) where
  location : LinearCoeffLocationQ p m
  expected : ℚ
  actual : ℚ
  deriving DecidableEq, Repr

/-- Return a singleton mismatch precisely when one coefficient differs. -/
def linearCoeffMismatchAtQ {p m : ℕ}
    (expected actual : LinearExprQ p m)
    (location : LinearCoeffLocationQ p m) :
    List (LinearCoeffMismatchQ p m) :=
  if linearCoeffAtQ expected location = linearCoeffAtQ actual location then
    []
  else
    [{ location := location,
       expected := linearCoeffAtQ expected location,
       actual := linearCoeffAtQ actual location }]

/-- Complete exact identity mismatch report in deterministic location order. -/
def linearExprMismatchesQ {p m : ℕ}
    (expected actual : LinearExprQ p m) :
    List (LinearCoeffMismatchQ p m) :=
  (linearCoeffLocationsQ p m).flatMap
    (linearCoeffMismatchAtQ expected actual)

/-- Complete deterministic general-upper-certificate audit report. -/
structure UpperCertAuditReportQ (p m : ℕ) where
  accepted : Bool
  negativeInterpWeights : List (NegativeInterpWeightQ p)
  negativeAssumptionWeights : List NegativeAssumptionWeightQ
  dualAudit : PSDFactorAuditReportQ m
  identityMismatches : List (LinearCoeffMismatchQ p m)
  deriving DecidableEq, Repr

/-- Audit every exact general Gram upper-certificate obligation. -/
def auditUpperCertQ {p m : ℕ} {model : ModelQ p m}
    (c : UpperCertQ model) : UpperCertAuditReportQ p m :=
  { accepted := checkUpperCertQ c
    negativeInterpWeights := negativeInterpWeightsQ c.interpTerms
    negativeAssumptionWeights :=
      negativeAssumptionWeightsQ c.assumptionTerms
    dualAudit := auditPSDFactorQ c.dualMatrix c.dualFactor
    identityMismatches :=
      linearExprMismatchesQ
        (upperTargetExprQ c.bound c.objective)
        (certificateRhsExprQ c) }

/-- Structured-audit acceptance has exactly the existing proposition-level
certificate meaning. -/
theorem auditUpperCertQ_accepted_iff
    {p m : ℕ} {model : ModelQ p m}
    (c : UpperCertQ model) :
    (auditUpperCertQ c).accepted = true ↔ UpperCertValidQ c := by
  simpa [auditUpperCertQ] using checkUpperCertQ_eq_true_iff c

/-- Acceptance of the structured report proves the same universal real upper
bound as Boolean checker acceptance. -/
theorem auditUpperCertQ_sound_real
    {p m : ℕ} {model : ModelQ p m}
    (c : UpperCertQ model)
    (haudit : (auditUpperCertQ c).accepted = true)
    (d : DataR (Fin p) m)
    (hrealizes : RealizesModelQ model d)
    (hcore : CoreFeasible d)
    (hassumptions : AssumptionsFeasibleR model d) :
    c.objective.evalR d ≤ (c.bound : ℝ) := by
  exact checkUpperCertQ_sound_real c
    (by simpa [auditUpperCertQ] using haudit)
    d hrealizes hcore hassumptions

/-- Every reported interpolation weight is strictly negative. -/
theorem mem_negativeInterpWeightsFromQ_sound
    {p : ℕ} (start : Nat) (terms : List (InterpTermQ p))
    (e : NegativeInterpWeightQ p)
    (h : e ∈ negativeInterpWeightsFromQ start terms) :
    e.weight < 0 := by
  induction terms generalizing start with
  | nil =>
      simp [negativeInterpWeightsFromQ] at h
  | cons t ts ih =>
      by_cases hneg : t.weight < 0
      · simp [negativeInterpWeightsFromQ, hneg] at h
        rcases h with h | h
        · subst e
          exact hneg
        · exact ih (start := start + 1) h
      · have hrest :
          e ∈ negativeInterpWeightsFromQ (start + 1) ts := by
            simpa [negativeInterpWeightsFromQ, hneg] using h
        exact ih (start := start + 1) hrest

/-- Every item in the complete interpolation-weight report is genuinely
negative. -/
theorem mem_negativeInterpWeightsQ_sound
    {p : ℕ} (terms : List (InterpTermQ p))
    (e : NegativeInterpWeightQ p)
    (h : e ∈ negativeInterpWeightsQ terms) :
    e.weight < 0 := by
  exact mem_negativeInterpWeightsFromQ_sound 0 terms e h

/-- Every reported formulation-assumption weight is strictly negative. -/
theorem mem_negativeAssumptionWeightsFromQ_sound
    {p m : ℕ} {model : ModelQ p m}
    (start : Nat) (terms : List (AssumptionTermQ model))
    (e : NegativeAssumptionWeightQ)
    (h : e ∈ negativeAssumptionWeightsFromQ start terms) :
    e.weight < 0 := by
  induction terms generalizing start with
  | nil =>
      simp [negativeAssumptionWeightsFromQ] at h
  | cons t ts ih =>
      by_cases hneg : t.weight < 0
      · simp [negativeAssumptionWeightsFromQ, hneg] at h
        rcases h with h | h
        · subst e
          exact hneg
        · exact ih (start := start + 1) h
      · have hrest :
          e ∈ negativeAssumptionWeightsFromQ (start + 1) ts := by
            simpa [negativeAssumptionWeightsFromQ, hneg] using h
        exact ih (start := start + 1) hrest

/-- Every item in the complete assumption-weight report is genuinely
negative. -/
theorem mem_negativeAssumptionWeightsQ_sound
    {p m : ℕ} {model : ModelQ p m}
    (terms : List (AssumptionTermQ model))
    (e : NegativeAssumptionWeightQ)
    (h : e ∈ negativeAssumptionWeightsQ terms) :
    e.weight < 0 := by
  exact mem_negativeAssumptionWeightsFromQ_sound 0 terms e h

/-- Every reported identity mismatch records the exact expected and actual
coefficients at its typed location. -/
theorem mem_linearExprMismatchesQ_sound
    {p m : ℕ} (expected actual : LinearExprQ p m)
    (e : LinearCoeffMismatchQ p m)
    (h : e ∈ linearExprMismatchesQ expected actual) :
    e.expected = linearCoeffAtQ expected e.location ∧
      e.actual = linearCoeffAtQ actual e.location ∧
      e.expected ≠ e.actual := by
  unfold linearExprMismatchesQ at h
  simp only [List.mem_flatMap] at h
  rcases h with ⟨location, _, hitem⟩
  by_cases heq :
      linearCoeffAtQ expected location = linearCoeffAtQ actual location
  · simp [linearCoeffMismatchAtQ, heq] at hitem
  · simp [linearCoeffMismatchAtQ, heq] at hitem
    subst e
    exact ⟨rfl, rfl, heq⟩

end GramPEP
end LeanPEP
