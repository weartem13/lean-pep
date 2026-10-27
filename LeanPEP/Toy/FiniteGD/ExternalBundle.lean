import LeanPEP.Toy.FiniteGD.UpperCertificateChecker

/-!
# Exact external bundle boundary for finite gradient-descent PEPs

This module is the Lean-side target of the external JSON importer.  The
external converter is deliberately untrusted: it only emits exact rational
Lean data.  Lean independently checks

* import metadata and declared finite dimensions;
* primal interpolation feasibility;
* the generic upper certificate; and
* equality between the witness objective and the certified bound.

Consequently, a successful bundle check closes an exact finite PEP lower/upper
loop without trusting floating-point tolerances or the converter's arithmetic.
-/

namespace LeanPEP
namespace Toy
namespace FiniteGD

/-- Metadata carried across the external import boundary.

The type parameter fixes the actual Lean trajectory length.  The declared
counts remain explicit so that index/count mistakes in an external format are
reported rather than silently repaired. -/
structure ImportMetadataQ (N : ℕ) where
  schemaVersion : Nat
  declaredSteps : Nat
  declaredPointCount : Nat
  declaredConstraintCount : Nat
  sourceName : String
  sourceSha256 : String
  generatorVersion : String
  deriving DecidableEq, Repr

/-- Number of finite points: the optimum plus iterates `0, ..., N`. -/
def expectedPointCountQ (N : ℕ) : Nat :=
  N + 2

/-- Number of ordered scalar interpolation constraints. -/
def expectedConstraintCountQ (N : ℕ) : Nat :=
  expectedPointCountQ N * expectedPointCountQ N

/-- Exact Boolean metadata audit. -/
def checkImportMetadataQ {N : ℕ} (m : ImportMetadataQ N) : Bool :=
  decide (m.schemaVersion = 1) &&
    (decide (m.declaredSteps = N) &&
      (decide (m.declaredPointCount = expectedPointCountQ N) &&
        decide
          (m.declaredConstraintCount = expectedConstraintCountQ N)))

/-- One metadata field that can disagree with the Lean semantics. -/
inductive MetadataFieldQ where
  | schemaVersion
  | steps
  | pointCount
  | constraintCount
  deriving DecidableEq, Repr

/-- One exact natural-number metadata mismatch. -/
structure MetadataMismatchQ where
  field : MetadataFieldQ
  expected : Nat
  actual : Nat
  deriving DecidableEq, Repr

/-- Emit one mismatch exactly when two natural numbers differ. -/
def metadataMismatchQ
    (field : MetadataFieldQ)
    (expected actual : Nat) : List MetadataMismatchQ :=
  if expected = actual then [] else
    [{ field := field, expected := expected, actual := actual }]

/-- Complete deterministic metadata mismatch report. -/
def metadataMismatchesQ {N : ℕ}
    (m : ImportMetadataQ N) : List MetadataMismatchQ :=
  metadataMismatchQ .schemaVersion 1 m.schemaVersion ++
    metadataMismatchQ .steps N m.declaredSteps ++
    metadataMismatchQ .pointCount
      (expectedPointCountQ N) m.declaredPointCount ++
    metadataMismatchQ .constraintCount
      (expectedConstraintCountQ N) m.declaredConstraintCount

/-- One imported exact lower/upper closed-loop candidate. -/
structure ExactBundleQ (N : ℕ) where
  metadata : ImportMetadataQ N
  primal : DataQ N
  upper : UpperCertQ N

/-- Check the complete imported closed loop.

The last equality ensures that the feasible primal witness attains the exact
bound proved by the upper certificate. -/
def checkExactBundleQ {N : ℕ} (b : ExactBundleQ N) : Bool :=
  checkImportMetadataQ b.metadata &&
    (checkFeasibleQ b.primal &&
      (checkUpperCertQ b.upper &&
        decide
          (b.primal.value b.upper.objective = b.upper.bound)))

/-- Decompose successful bundle acceptance into its four exact obligations. -/
theorem checkExactBundleQ_components
    {N : ℕ} (b : ExactBundleQ N)
    (h : checkExactBundleQ b = true) :
    checkImportMetadataQ b.metadata = true ∧
      checkFeasibleQ b.primal = true ∧
      checkUpperCertQ b.upper = true ∧
      b.primal.value b.upper.objective = b.upper.bound := by
  simpa [checkExactBundleQ] using h

/-- A successful external bundle check reconstructs the complete real closed
loop: a feasible real witness, exact attainment over `ℚ`, and a universal real
upper bound. -/
theorem checkExactBundleQ_sound_real
    {N : ℕ} (b : ExactBundleQ N)
    (h : checkExactBundleQ b = true) :
    checkImportMetadataQ b.metadata = true ∧
      Feasible (toRealData b.primal) ∧
      b.primal.value b.upper.objective = b.upper.bound ∧
      ∀ d : DataR N, Feasible d →
        d.value b.upper.objective ≤ (b.upper.bound : ℝ) := by
  have hparts := checkExactBundleQ_components b h
  refine ⟨hparts.1, ?_⟩
  refine ⟨checkFeasibleQ_sound_real b.primal hparts.2.1, ?_⟩
  refine ⟨hparts.2.2.2, ?_⟩
  intro d hd
  exact checkUpperCertQ_sound_real b.upper hparts.2.2.1 d hd

/-- Exact failure categories at the external bundle boundary. -/
inductive ExactBundleFailureQ (N : ℕ) where
  | metadataMismatch (differences : List MetadataMismatchQ)
  | primalRejected (violations : List (ViolationQ N))
  | upperRejected (failure : UpperCertFailureQ N)
  | objectiveMismatch
      (objective : Fin (N + 1))
      (witnessValue : ℚ)
      (certifiedBound : ℚ)
  deriving DecidableEq, Repr

/-- Executable audit result for a complete imported bundle. -/
inductive ExactBundleAuditQ (N : ℕ) where
  | accepted
  | rejected (failure : ExactBundleFailureQ N)
  deriving DecidableEq, Repr

/-- Audit metadata, primal data, upper certificate, and exact lower/upper
agreement in that order. -/
def auditExactBundleQ {N : ℕ}
    (b : ExactBundleQ N) : ExactBundleAuditQ N :=
  match metadataMismatchesQ b.metadata with
  | [] =>
      match allViolationsQ b.primal with
      | [] =>
          match auditUpperCertQ b.upper with
          | UpperCertAuditQ.accepted =>
              if b.primal.value b.upper.objective = b.upper.bound then
                ExactBundleAuditQ.accepted
              else
                ExactBundleAuditQ.rejected
                  (.objectiveMismatch
                    b.upper.objective
                    (b.primal.value b.upper.objective)
                    b.upper.bound)
          | UpperCertAuditQ.rejected failure =>
              ExactBundleAuditQ.rejected (.upperRejected failure)
      | violations =>
          ExactBundleAuditQ.rejected (.primalRejected violations)
  | differences =>
      ExactBundleAuditQ.rejected (.metadataMismatch differences)

end FiniteGD
end Toy
end LeanPEP
