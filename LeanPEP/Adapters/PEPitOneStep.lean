import Mathlib.Tactic
import LeanPEP.GramPEP.Coordinate
import LeanPEP.GramPEP.ApproximateAudit

/-!
# PEPit one-step gradient-descent source audit

This module audits the concrete source formulation emitted by the
`pepit-smooth-convex-gd-one-step-v1` adapter.  It checks both lightweight
producer/order metadata and a typed exact snapshot of the PEPit-native symbolic
formulation:

* sampled-point and gradient decompositions in PEPit's four-vector leaf basis;
* every prepared scalar constraint, including exact function-value and Gram
  coefficients;
* the performance objective; and
* the exact source-to-centered basis transformation used by the adapter.

The source audit is still not a mathematical certificate.  Adapted primal and
upper artifacts independently pass through the existing exact Gram-bundle
checker.  The purpose of this layer is formulation/provenance hardening: a
Python fingerprint string is not sufficient to make malformed symbolic source
data pass the Lean source audit.
-/

namespace LeanPEP.Adapters.PEPitOneStep

open LeanPEP.GramPEP

inductive FieldQ where
  | producerName
  | producerCommit
  | captureMode
  | adapterId
  | functionClass
  | smoothness
  | stepSize
  | steps
  | pointOrder
  | functionValueOrder
  | leafPointOrder
  | constraintOrder
  | modelFingerprint
  deriving Repr, DecidableEq

/-- PEPit source scalar-constraint category for this fixed adapter profile. -/
inductive SourceConstraintKindQ where
  | initial
  | interpolation
  deriving Repr, DecidableEq

/-- PEPit source scalar-constraint sense.  This profile uses expressions
normalized as `expr ≤ 0`. -/
inductive SourceConstraintSenseQ where
  | le
  deriving Repr, DecidableEq

/-- One exact PEPit-native scalar constraint over three sampled function values
and the four-vector PEPit leaf Gram basis `[x_star, x0, g0, g1]`. -/
structure SourceConstraintQ where
  label : String
  kind : SourceConstraintKindQ
  sense : SourceConstraintSenseQ
  i : Option (Fin 3)
  j : Option (Fin 3)
  expr : LinearExprQ 3 4

/-- Typed exact symbolic payload crossing the source adapter boundary. -/
structure SymbolicSourceQ where
  pointDecomposition : Matrix (Fin 3) (Fin 4) ℚ
  gradientDecomposition : Matrix (Fin 3) (Fin 4) ℚ
  constraints : Fin 7 → SourceConstraintQ
  objective : LinearExprQ 3 4
  nativeToCentered : Matrix (Fin 3) (Fin 4) ℚ

structure SourceQ where
  producerName : String
  producerCommit : String
  packageVersion : String
  wrapperName : String
  solverName : String
  solverStatus : String
  captureMode : String
  adapterId : String
  functionClass : String
  smoothness : String
  stepSize : String
  steps : Nat
  pointOrder : List String
  functionValueOrder : List String
  leafPointOrder : List String
  constraintOrder : List String
  modelFingerprint : String
  symbolic : SymbolicSourceQ
  sourceSha256 : String
  adaptedApproxSha256 : String
  adapterReportSha256 : String
  adapterManifestSha256 : String
  adapterGeneratorVersion : String

structure MismatchQ where
  field : FieldQ
  expected : String
  actual : String
  deriving Repr, DecidableEq

/-- Matrix-valued symbolic source fields share the same fixed `3 × 4` shape. -/
inductive SourceMatrixFieldQ where
  | pointDecomposition
  | gradientDecomposition
  | nativeToCentered
  deriving Repr, DecidableEq

/-- One exact rational mismatch in a typed source matrix. -/
structure SourceMatrixMismatchQ where
  field : SourceMatrixFieldQ
  row : Nat
  col : Nat
  expected : ℚ
  actual : ℚ
  deriving Repr, DecidableEq

inductive SourceConstraintHeaderFieldQ where
  | label
  | kind
  | sense
  | i
  | j
  deriving Repr, DecidableEq

/-- One exact header mismatch in the ordered source constraint array. -/
structure SourceConstraintHeaderMismatchQ where
  index : Nat
  field : SourceConstraintHeaderFieldQ
  expected : String
  actual : String
  deriving Repr, DecidableEq

/-- One exact affine coefficient mismatch attached to a source constraint. -/
structure SourceConstraintExprMismatchQ where
  constraintIndex : Nat
  coefficient : LinearCoeffMismatchQ 3 4
  deriving Repr, DecidableEq

structure AuditReportQ where
  accepted : Bool
  mismatches : List MismatchQ
  matrixMismatches : List SourceMatrixMismatchQ
  constraintHeaderMismatches : List SourceConstraintHeaderMismatchQ
  constraintExprMismatches : List SourceConstraintExprMismatchQ
  objectiveMismatches : List (LinearCoeffMismatchQ 3 4)
  deriving Repr, DecidableEq

def expectedProducerName : String := "PEPit"

def expectedProducerCommit : String :=
  "5a061a1b2dbe450b6bac42e2442942748f3b1f32"

def expectedCaptureModes : List String :=
  ["live_pepit", "deterministic_regression_fixture"]

def expectedAdapterId : String := "pepit-smooth-convex-gd-one-step-v1"

def expectedFunctionClass : String := "SmoothConvexFunction"

def expectedSmoothness : String := "1"

def expectedStepSize : String := "1"

def expectedSteps : Nat := 1

def expectedPointOrder : List String := ["star", "x0", "x1"]

def expectedFunctionValueOrder : List String := ["f_star", "f0", "f1"]

def expectedLeafPointOrder : List String := ["x_star", "x0", "g0", "g1"]

def expectedConstraintOrder : List String :=
  [ "initial_radius",
    "smooth_convexity:star:x0",
    "smooth_convexity:star:x1",
    "smooth_convexity:x0:star",
    "smooth_convexity:x0:x1",
    "smooth_convexity:x1:star",
    "smooth_convexity:x1:x0" ]

def expectedModelFingerprint : String :=
  "1d752930ba9e3395abd7e3d4b643a0a239b33bb2a2d2ec4ed50b4e4af863842a"

/-- Exact sampled-point decompositions in PEPit's native leaf order. -/
def expectedPointDecompositionQ : Matrix (Fin 3) (Fin 4) ℚ :=
  ![ ![(1 : ℚ), 0, 0, 0],
     ![0, 1, 0, 0],
     ![0, 1, -1, 0] ]

/-- Exact sampled-gradient decompositions in PEPit's native leaf order. -/
def expectedGradientDecompositionQ : Matrix (Fin 3) (Fin 4) ℚ :=
  ![ ![(0 : ℚ), 0, 0, 0],
     ![0, 0, 1, 0],
     ![0, 0, 0, 1] ]

/-- Exact basis map whose rows are `[x0-x_star, g0, g1]` in the PEPit leaf
basis `[x_star, x0, g0, g1]`. -/
def expectedNativeToCenteredQ : Matrix (Fin 3) (Fin 4) ℚ :=
  ![ ![(-1 : ℚ), 1, 0, 0],
     ![0, 0, 1, 0],
     ![0, 0, 0, 1] ]

def expectedSourcePointQ (i : Fin 3) : VecExpr 4 ℚ :=
  expectedPointDecompositionQ i

def expectedSourceGradientQ (i : Fin 3) : VecExpr 4 ℚ :=
  expectedGradientDecompositionQ i

/-- PEPit's exact smooth-convex interpolation expression, normalized as
`rhs - lhs ≤ 0`. -/
def expectedInterpolationExprQ (i j : Fin 3) : LinearExprQ 3 4 :=
  let xi := expectedSourcePointQ i
  let xj := expectedSourcePointQ j
  let gi := expectedSourceGradientQ i
  let gj := expectedSourceGradientQ j
  LinearExprQ.add
    (LinearExprQ.sub
      (LinearExprQ.valueVar (m := 4) j)
      (LinearExprQ.valueVar (m := 4) i))
    (LinearExprQ.add
      (LinearExprQ.gramBilinear (p := 3) gj (xi - xj))
      (LinearExprQ.scale ((1 : ℚ) / 2)
        (LinearExprQ.gramNorm (p := 3) (gi - gj))))

/-- Initial-radius source expression `||x0-x_star||² - 1 ≤ 0`. -/
def expectedInitialExprQ : LinearExprQ 3 4 :=
  LinearExprQ.add
    (LinearExprQ.const 3 4 (-1))
    (LinearExprQ.gramNorm (p := 3)
      (expectedSourcePointQ 1 - expectedSourcePointQ 0))

def expectedInitialConstraintQ : SourceConstraintQ :=
  { label := "initial_radius"
    kind := .initial
    sense := .le
    i := none
    j := none
    expr := expectedInitialExprQ }

def expectedInterpolationConstraintQ
    (i j : Fin 3) (label : String) : SourceConstraintQ :=
  { label := label
    kind := .interpolation
    sense := .le
    i := some i
    j := some j
    expr := expectedInterpolationExprQ i j }

/-- PEPit's prepared source constraint order after removing the separate
max-min performance constraint. -/
def expectedConstraintsQ : Fin 7 → SourceConstraintQ :=
  ![ expectedInitialConstraintQ,
     expectedInterpolationConstraintQ 0 1 "smooth_convexity:star:x0",
     expectedInterpolationConstraintQ 0 2 "smooth_convexity:star:x1",
     expectedInterpolationConstraintQ 1 0 "smooth_convexity:x0:star",
     expectedInterpolationConstraintQ 1 2 "smooth_convexity:x0:x1",
     expectedInterpolationConstraintQ 2 0 "smooth_convexity:x1:star",
     expectedInterpolationConstraintQ 2 1 "smooth_convexity:x1:x0" ]

/-- Source performance expression `f1 - f_star`. -/
def expectedObjectiveQ : LinearExprQ 3 4 :=
  LinearExprQ.sub
    (LinearExprQ.valueVar (m := 4) 2)
    (LinearExprQ.valueVar (m := 4) 0)

def joinLabels : List String → String
  | [] => ""
  | [x] => x
  | x :: xs => x ++ "|" ++ joinLabels xs

def mismatchString
    (field : FieldQ) (expected actual : String) : List MismatchQ :=
  if expected = actual then [] else [{ field := field, expected := expected, actual := actual }]

def mismatchNat
    (field : FieldQ) (expected actual : Nat) : List MismatchQ :=
  mismatchString field (toString expected) (toString actual)

def mismatchLabels
    (field : FieldQ) (expected actual : List String) : List MismatchQ :=
  mismatchString field (joinLabels expected) (joinLabels actual)

/-- Lightweight producer/order/fingerprint mismatches. -/
def sourceMismatchesQ (source : SourceQ) : List MismatchQ :=
  mismatchString .producerName expectedProducerName source.producerName ++
  mismatchString .producerCommit expectedProducerCommit source.producerCommit ++
  (if source.captureMode ∈ expectedCaptureModes then []
   else mismatchString .captureMode (joinLabels expectedCaptureModes) source.captureMode) ++
  mismatchString .adapterId expectedAdapterId source.adapterId ++
  mismatchString .functionClass expectedFunctionClass source.functionClass ++
  mismatchString .smoothness expectedSmoothness source.smoothness ++
  mismatchString .stepSize expectedStepSize source.stepSize ++
  mismatchNat .steps expectedSteps source.steps ++
  mismatchLabels .pointOrder expectedPointOrder source.pointOrder ++
  mismatchLabels .functionValueOrder expectedFunctionValueOrder source.functionValueOrder ++
  mismatchLabels .leafPointOrder expectedLeafPointOrder source.leafPointOrder ++
  mismatchLabels .constraintOrder expectedConstraintOrder source.constraintOrder ++
  mismatchString .modelFingerprint expectedModelFingerprint source.modelFingerprint

/-- Exact entrywise mismatch report for one fixed-shape symbolic matrix. -/
def sourceMatrixMismatchesAtQ
    (field : SourceMatrixFieldQ)
    (expected actual : Matrix (Fin 3) (Fin 4) ℚ) :
    List SourceMatrixMismatchQ :=
  (pointIndices 3).flatMap (fun i =>
    (gramIndices 4).flatMap (fun j =>
      if expected i j = actual i j then []
      else
        [{ field := field,
           row := i.val,
           col := j.val,
           expected := expected i j,
           actual := actual i j }]))

def sourceMatrixMismatchesQ (source : SourceQ) :
    List SourceMatrixMismatchQ :=
  sourceMatrixMismatchesAtQ .pointDecomposition
      expectedPointDecompositionQ source.symbolic.pointDecomposition ++
  sourceMatrixMismatchesAtQ .gradientDecomposition
      expectedGradientDecompositionQ source.symbolic.gradientDecomposition ++
  sourceMatrixMismatchesAtQ .nativeToCentered
      expectedNativeToCenteredQ source.symbolic.nativeToCentered

def kindString : SourceConstraintKindQ → String
  | .initial => "initial"
  | .interpolation => "interpolation"

def senseString : SourceConstraintSenseQ → String
  | .le => "le"

def optionPointString : Option (Fin 3) → String
  | none => "none"
  | some i => toString i.val

def constraintHeaderValueQ
    (c : SourceConstraintQ) : SourceConstraintHeaderFieldQ → String
  | .label => c.label
  | .kind => kindString c.kind
  | .sense => senseString c.sense
  | .i => optionPointString c.i
  | .j => optionPointString c.j

def sourceConstraintHeaderFieldsQ : List SourceConstraintHeaderFieldQ :=
  [.label, .kind, .sense, .i, .j]

def sourceConstraintIndicesQ : List (Fin 7) := List.finRange 7

/-- Exact ordered constraint-header mismatches. -/
def sourceConstraintHeaderMismatchesQ (source : SourceQ) :
    List SourceConstraintHeaderMismatchQ :=
  sourceConstraintIndicesQ.flatMap (fun k =>
    sourceConstraintHeaderFieldsQ.flatMap (fun field =>
      let expected := constraintHeaderValueQ (expectedConstraintsQ k) field
      let actual := constraintHeaderValueQ (source.symbolic.constraints k) field
      if expected = actual then []
      else
        [{ index := k.val,
           field := field,
           expected := expected,
           actual := actual }]))

/-- Exact ordered constraint-expression coefficient mismatches. -/
def sourceConstraintExprMismatchesQ (source : SourceQ) :
    List SourceConstraintExprMismatchQ :=
  sourceConstraintIndicesQ.flatMap (fun k =>
    (linearExprMismatchesQ
      (expectedConstraintsQ k).expr
      (source.symbolic.constraints k).expr).map (fun mismatch =>
        { constraintIndex := k.val,
          coefficient := mismatch }))

/-- Exact source objective coefficient mismatches. -/
def sourceObjectiveMismatchesQ (source : SourceQ) :
    List (LinearCoeffMismatchQ 3 4) :=
  linearExprMismatchesQ expectedObjectiveQ source.symbolic.objective

/-- Full source-formulation validity, including typed symbolic arrays. -/
def SourceValidQ (source : SourceQ) : Prop :=
  sourceMismatchesQ source = [] ∧
    sourceMatrixMismatchesQ source = [] ∧
    sourceConstraintHeaderMismatchesQ source = [] ∧
    sourceConstraintExprMismatchesQ source = [] ∧
    sourceObjectiveMismatchesQ source = []

def auditSourceQ (source : SourceQ) : AuditReportQ :=
  let mismatches := sourceMismatchesQ source
  let matrixMismatches := sourceMatrixMismatchesQ source
  let constraintHeaderMismatches := sourceConstraintHeaderMismatchesQ source
  let constraintExprMismatches := sourceConstraintExprMismatchesQ source
  let objectiveMismatches := sourceObjectiveMismatchesQ source
  { accepted :=
      mismatches.isEmpty &&
        matrixMismatches.isEmpty &&
        constraintHeaderMismatches.isEmpty &&
        constraintExprMismatches.isEmpty &&
        objectiveMismatches.isEmpty
    mismatches := mismatches
    matrixMismatches := matrixMismatches
    constraintHeaderMismatches := constraintHeaderMismatches
    constraintExprMismatches := constraintExprMismatches
    objectiveMismatches := objectiveMismatches }

def checkSourceQ (source : SourceQ) : Bool :=
  (auditSourceQ source).accepted

@[simp] theorem checkSourceQ_eq_audit (source : SourceQ) :
    checkSourceQ source = (auditSourceQ source).accepted := rfl

theorem checkSourceQ_eq_true_iff (source : SourceQ) :
    checkSourceQ source = true ↔ SourceValidQ source := by
  simp [checkSourceQ, auditSourceQ, SourceValidQ]
  constructor
  · rintro ⟨⟨⟨⟨hMetadata, hMatrices⟩, hHeaders⟩, hConstraints⟩, hObjective⟩
    exact ⟨hMetadata, hMatrices, hHeaders, hConstraints, hObjective⟩
  · rintro ⟨hMetadata, hMatrices, hHeaders, hConstraints, hObjective⟩
    exact ⟨⟨⟨⟨hMetadata, hMatrices⟩, hHeaders⟩, hConstraints⟩, hObjective⟩

/-- Combined source-formulation and downstream numerical audit.

The adapter is accepted only when the pinned source formulation is accepted
and a reconstructed exact Gram bundle is accepted.  Raw-track acceptance is
reported independently and is never inferred from reconstruction. -/
structure AdapterAuditReportQ where
  accepted : Bool
  sourceAudit : AuditReportQ
  numericalAudit : Option (LeanPEP.GramPEP.ApproxGramAuditComparisonQ 3 3)
  deriving Repr, DecidableEq

private def reconstructedAcceptedQ :
    Option (LeanPEP.GramPEP.ApproxGramAuditComparisonQ 3 3) → Bool
  | none => false
  | some comparison => comparison.reconstructedAudit.accepted

/-- Combine the exact source formulation audit with the existing dual-track
Gram auditor without changing either mathematical acceptance criterion. -/
def auditAdapterOptionalQ
    (source : SourceQ)
    (numerical : Option (LeanPEP.GramPEP.ApproxGramAuditComparisonQ 3 3)) :
    AdapterAuditReportQ :=
  let sourceAudit := auditSourceQ source
  { accepted := sourceAudit.accepted && reconstructedAcceptedQ numerical
    sourceAudit := sourceAudit
    numericalAudit := numerical }

end LeanPEP.Adapters.PEPitOneStep
