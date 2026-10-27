import LeanPEP.Adapters.ProximalGradientCoordinates
import LeanPEP.GramPEP.ExactReindexing

/-!
# D4: checked storage permutations before D3 origin elimination

Five independent inverse-array pairs describe basis, value, smooth-sample,
nonsmooth-sample, and constraint-row storage orders. Row-tag i/j are LOGICAL
sample identifiers in D2's convention, not storage offsets; they move with their
row. Center/section matrices retain D3's centered axis and permute ONLY their
native axis. This is an exact fixed-profile ordering adapter, not general PEPit
leaf elimination, row rescaling, redundant-row deletion, or live capture.
-/

namespace LeanPEP.Adapters.ProximalGradientOrdering

open LeanPEP.GramPEP LeanPEP.Profiles
open LeanPEP.GramPEP.ExactReindexing

abbrev valueCount (n : ℕ) := ProximalGradient.valueCount n
abbrev basisCount (n : ℕ) := ProximalGradientCoordinates.leafCount n
abbrev rowCount (n : ℕ) := (n+3)^2 + (n+2)^2 + 1

/-- Non-order metadata; all fields are passed unchanged to D3. -/
@[ext] structure MetadataQ where
  profileId : String
  coordinates : String
  steps : Nat
  valueCount : Nat
  basisCount : Nat
  smoothness : ℚ
  stepSize : ℚ
  radiusSquared : ℚ
  smoothClass : Composite.FunctionClassQ
  nonsmoothClass : Composite.FunctionClassQ
  sense : ProximalGradientSource.SenseQ
  deriving DecidableEq, Repr

/-- Every array has an exact profile-selected size. This is a typed payload,
not a claim about correctness of the untrusted JSON parser. No default get. -/
@[ext] structure SnapshotQ (n : ℕ) where
  metadata : MetadataQ
  basisLabels : Fin (basisCount n) → String
  valueLabels : Fin (valueCount n) → String
  rowTags : Fin (rowCount n) → ProximalGradientSource.RowTagQ
  centerMatrix : Matrix (Fin (ProximalGradient.basisCount n)) (Fin (basisCount n)) ℚ
  sectionMatrix : Matrix (Fin (basisCount n)) (Fin (ProximalGradient.basisCount n)) ℚ
  smoothSamples : Fin (n+3) → Composite.SampleQ (valueCount n) (basisCount n)
  nonsmoothSamples : Fin (n+2) → Composite.SampleQ (valueCount n) (basisCount n)
  constraints : Fin (rowCount n) → LinearExprQ (valueCount n) (basisCount n)
  objective : LinearExprQ (valueCount n) (basisCount n)

@[ext] structure OrderingQ (n : ℕ) where
  basis : IndexMapQ (basisCount n)
  values : IndexMapQ (valueCount n)
  smooth : IndexMapQ (n+3)
  nonsmooth : IndexMapQ (n+2)
  rows : IndexMapQ (rowCount n)

def OrderingQ.symm {n : ℕ} (o : OrderingQ n) : OrderingQ n :=
  { basis := o.basis.symm, values := o.values.symm, smooth := o.smooth.symm
    nonsmooth := o.nonsmooth.symm, rows := o.rows.symm }

def checkOrderingQ {n : ℕ} (o : OrderingQ n) : Bool :=
  checkQ o.basis && (checkQ o.values && (checkQ o.smooth &&
    (checkQ o.nonsmooth && checkQ o.rows)))

theorem checkOrderingQ_eq_true_iff {n : ℕ} (o : OrderingQ n) :
    checkOrderingQ o = true ↔ checkQ o.basis = true ∧ checkQ o.values = true ∧
      checkQ o.smooth = true ∧ checkQ o.nonsmooth = true ∧ checkQ o.rows = true := by
  simp only [checkOrderingQ, Bool.and_eq_true]

/-- Pure transport, not a reconstruction of the expected model. -/
def reorderSnapshotQ {n : ℕ} (o : OrderingQ n) (s : SnapshotQ n) : SnapshotQ n :=
  { metadata := s.metadata
    basisLabels := vec o.basis s.basisLabels
    valueLabels := vec o.values s.valueLabels
    rowTags := vec o.rows s.rowTags
    centerMatrix := fun i j => s.centerMatrix i (o.basis.toSource j)
    sectionMatrix := fun i j => s.sectionMatrix (o.basis.toSource i) j
    smoothSamples := fun i => sample o.values o.basis (s.smoothSamples (o.smooth.toSource i))
    nonsmoothSamples := fun i => sample o.values o.basis (s.nonsmoothSamples (o.nonsmooth.toSource i))
    constraints := fun i => expr o.values o.basis (s.constraints (o.rows.toSource i))
    objective := expr o.values o.basis s.objective }

/-- All metadata and entries return exactly: no information is lost by ordering.
This is separate from D3's rectangular quotient, whose round-trip guard remains. -/
theorem reorderSnapshotQ_roundtrip {n : ℕ} (o : OrderingQ n)
    (ho : checkOrderingQ o = true) (s : SnapshotQ n) :
    reorderSnapshotQ o.symm (reorderSnapshotQ o s) = s := by
  rcases (checkOrderingQ_eq_true_iff o).mp ho with ⟨hb, hv, hf, hh, hr⟩
  have hbi := ((checkQ_eq_true_iff o.basis).mp hb).2
  have hfi := ((checkQ_eq_true_iff o.smooth).mp hf).2
  have hhi := ((checkQ_eq_true_iff o.nonsmooth).mp hh).2
  have hri := ((checkQ_eq_true_iff o.rows).mp hr).2
  apply SnapshotQ.ext
  · rfl
  · exact vec_roundtrip o.basis hb s.basisLabels
  · exact vec_roundtrip o.values hv s.valueLabels
  · exact vec_roundtrip o.rows hr s.rowTags
  · funext i j
    change s.centerMatrix i (o.basis.toSource (o.basis.toCanonical j)) = s.centerMatrix i j
    rw [hbi j]
  · funext i j
    change s.sectionMatrix (o.basis.toSource (o.basis.toCanonical i)) j = s.sectionMatrix i j
    rw [hbi i]
  · funext i
    change sample o.values.symm o.basis.symm
      (sample o.values o.basis (s.smoothSamples (o.smooth.toSource (o.smooth.toCanonical i)))) =
      s.smoothSamples i
    rw [hfi i]
    exact sample_roundtrip o.values o.basis hv hb (s.smoothSamples i)
  · funext i
    change sample o.values.symm o.basis.symm
      (sample o.values o.basis (s.nonsmoothSamples (o.nonsmooth.toSource (o.nonsmooth.toCanonical i)))) =
      s.nonsmoothSamples i
    rw [hhi i]
    exact sample_roundtrip o.values o.basis hv hb (s.nonsmoothSamples i)
  · funext i
    change expr o.values.symm o.basis.symm
      (expr o.values o.basis (s.constraints (o.rows.toSource (o.rows.toCanonical i)))) =
      s.constraints i
    rw [hri i]
    exact expr_roundtrip o.values o.basis hv hb (s.constraints i)
  · exact expr_roundtrip o.values o.basis hv hb s.objective

/-- A source-row reference uses the inverse map, not the coefficient gather map. -/
theorem constraint_reference {n : ℕ} (o : OrderingQ n) (ho : checkOrderingQ o = true)
    (s : SnapshotQ n) (j : Fin (rowCount n)) :
    (reorderSnapshotQ o s).constraints (o.rows.toCanonical j) =
      expr o.values o.basis (s.constraints j) := by
  have hr := ((checkOrderingQ_eq_true_iff o).mp ho).2.2.2.2
  have hi := ((checkQ_eq_true_iff o.rows).mp hr).2 j
  change expr o.values o.basis (s.constraints (o.rows.toSource (o.rows.toCanonical j))) = _
  rw [hi]

/-- Lists are created from the whole typed arrays, with no truncation. -/
def SnapshotQ.toNative {n : ℕ} (s : SnapshotQ n) : ProximalGradientCoordinates.SourceQ n :=
  { header :=
      { profileId := s.metadata.profileId
        coordinates := s.metadata.coordinates
        steps := s.metadata.steps
        valueCount := s.metadata.valueCount
        basisCount := s.metadata.basisCount
        smoothness := s.metadata.smoothness
        stepSize := s.metadata.stepSize
        radiusSquared := s.metadata.radiusSquared
        smoothClass := s.metadata.smoothClass
        nonsmoothClass := s.metadata.nonsmoothClass
        sense := s.metadata.sense
        basisOrder := List.ofFn s.basisLabels
        valueOrder := List.ofFn s.valueLabels
        constraintOrder := List.ofFn s.rowTags }
    centerMatrix := s.centerMatrix
    sectionMatrix := s.sectionMatrix
    smoothSamples := List.ofFn s.smoothSamples
    nonsmoothSamples := List.ofFn s.nonsmoothSamples
    constraints := List.ofFn s.constraints
    objective := s.objective }

@[ext] structure SourceQ (n : ℕ) where
  ordering : OrderingQ n
  snapshot : SnapshotQ n

def SourceQ.model {n : ℕ} (s : SourceQ n) : ModelQ (valueCount n) (basisCount n) :=
  s.snapshot.toNative.model

def nativeSourceQ {n : ℕ} (s : SourceQ n) : ProximalGradientCoordinates.SourceQ n :=
  (reorderSnapshotQ s.ordering s.snapshot).toNative

def checkSourceQ {n : ℕ} (s : SourceQ n) : Bool :=
  checkOrderingQ s.ordering && ProximalGradientCoordinates.checkSourceQ (nativeSourceQ s)

theorem checkSourceQ_eq_true_iff {n : ℕ} (s : SourceQ n) :
    checkSourceQ s = true ↔ checkOrderingQ s.ordering = true ∧
      nativeSourceQ s = ProximalGradientCoordinates.expectedSourceQ n := by
  simp only [checkSourceQ, Bool.and_eq_true, ProximalGradientCoordinates.checkSourceQ_eq_expected]

theorem source_roundtrip {n : ℕ} (s : SourceQ n) (hs : checkSourceQ s = true) :
    reorderSnapshotQ s.ordering.symm (reorderSnapshotQ s.ordering s.snapshot) = s.snapshot :=
  reorderSnapshotQ_roundtrip s.ordering ((checkSourceQ_eq_true_iff s).mp hs).1 s.snapshot

/-- Get the actual source row index with its size proof, before reindexing. -/
def sourceRowQ {n : ℕ} (s : SourceQ n) (t : AssumptionTermQ s.model) : Fin (rowCount n) :=
  ⟨t.index.val, by
    simpa only [SourceQ.model, SnapshotQ.toNative, ProximalGradientCoordinates.SourceQ.model,
      List.length_ofFn] using t.index.isLt⟩

def nativeAssumptionQ {n : ℕ} (s : SourceQ n) (t : AssumptionTermQ s.model) :
    AssumptionTermQ (nativeSourceQ s).model :=
  { weight := t.weight
    index := ⟨(s.ordering.rows.toCanonical (sourceRowQ s t)).val, by
      simpa only [nativeSourceQ, SnapshotQ.toNative, ProximalGradientCoordinates.SourceQ.model,
        List.length_ofFn] using (s.ordering.rows.toCanonical (sourceRowQ s t)).isLt⟩ }

@[simp] theorem nativeAssumptionQ_weight {n : ℕ} (s : SourceQ n) (t : AssumptionTermQ s.model) :
    (nativeAssumptionQ s t).weight = t.weight := rfl

theorem nativeAssumptionQ_index {n : ℕ} (s : SourceQ n) (t : AssumptionTermQ s.model) :
    (nativeAssumptionQ s t).index.val = (s.ordering.rows.toCanonical (sourceRowQ s t)).val := rfl

/-- No term is dropped, including zero-weight implicit terms. -/
def nativeUpperQ {n : ℕ} (s : SourceQ n) (c : UpperCertQ s.model) :
    UpperCertQ (nativeSourceQ s).model :=
  { bound := c.bound
    objective := expr s.ordering.values s.ordering.basis c.objective
    interpTerms := c.interpTerms.map (fun t =>
      { weight := t.weight, i := s.ordering.values.toCanonical t.i,
        j := s.ordering.values.toCanonical t.j })
    assumptionTerms := c.assumptionTerms.map (nativeAssumptionQ s)
    dualMatrix := matrix s.ordering.basis c.dualMatrix
    dualFactor := psdFactor s.ordering.basis c.dualFactor }

@[simp] theorem nativeUpperQ_bound {n : ℕ} (s : SourceQ n) (c : UpperCertQ s.model) :
    (nativeUpperQ s c).bound = c.bound := rfl

theorem nativeUpperQ_assumption_count {n : ℕ} (s : SourceQ n) (c : UpperCertQ s.model) :
    (nativeUpperQ s c).assumptionTerms.length = c.assumptionTerms.length := by
  simp only [nativeUpperQ, List.length_map]

/-- Raw and transported complete certificates are BOTH checked. We do not claim
that the Python transport preserves validity without these independent checks. -/
def checkBoundQ {n : ℕ} (s : SourceQ n) (c : UpperCertQ s.model) : Bool :=
  checkSourceQ s && (checkUpperCertQ c && (decide (c.interpTerms = []) &&
    (checkLinearExprEqQ c.objective s.snapshot.objective &&
      ProximalGradientCoordinates.checkBoundQ (nativeSourceQ s) (nativeUpperQ s c))))

theorem checkBoundQ_eq_true_iff {n : ℕ} (s : SourceQ n) (c : UpperCertQ s.model) :
    checkBoundQ s c = true ↔ checkSourceQ s = true ∧ checkUpperCertQ c = true ∧
      c.interpTerms = [] ∧ c.objective = s.snapshot.objective ∧
      ProximalGradientCoordinates.checkBoundQ (nativeSourceQ s) (nativeUpperQ s c) = true := by
  simp only [checkBoundQ, Bool.and_eq_true, decide_eq_true_eq, checkLinearExprEqQ_eq_true_iff]

theorem checked_certificate {n : ℕ} (s : SourceQ n) (c : UpperCertQ s.model)
    (hc : checkBoundQ s c = true) :
    ∃ d : UpperCertQ (ProximalGradient.modelQ n),
      checkUpperCertQ d = true ∧ d.interpTerms = [] ∧
      d.objective = ProximalGradient.objectiveQ n ∧ d.bound = c.bound := by
  have ht := ((checkBoundQ_eq_true_iff s c).mp hc).2.2.2.2
  obtain ⟨d, hd, hi, ho, hb⟩ :=
    ProximalGradientCoordinates.checked_certificate (nativeSourceQ s) (nativeUpperQ s c) ht
  exact ⟨d, hd, hi, ho, hb⟩

end LeanPEP.Adapters.ProximalGradientOrdering
