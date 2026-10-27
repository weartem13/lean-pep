import LeanPEP.Adapters.ProximalGradientOrdering
import LeanPEP.GramPEP.RowNormalization
import Mathlib.Data.List.OfFn

/-!
# D5: source-order row directions and positive rescaling, before D4 reindexing

The raw snapshot contains the submitted polynomials. Per-row directions give
actual >=0 or <=0 semantics; the old checker sees their oriented >=0 expressions.
Positive scales are checked separately, including on zero/unused rows. The D4
source is produced by inverse-scaling oriented rows. The multiplier conversion
uses the scale of the SOURCE row before D4 changes its index.
-/
namespace LeanPEP.Adapters.ProximalGradientRows

open LeanPEP.GramPEP LeanPEP.GramPEP.RowNormalization
open LeanPEP.Adapters.ProximalGradientOrdering (OrderingQ SnapshotQ valueCount basisCount rowCount)

@[ext] structure SourceQ (n : ℕ) where
  ordering : OrderingQ n
  snapshot : SnapshotQ n
  rules : Fin (rowCount n) → RuleQ

def SourceQ.model {n : ℕ} (s : SourceQ n) : ModelQ (valueCount n) (basisCount n) :=
  { position := fun _ => 0
    gradient := fun _ => 0
    assumptions := List.ofFn (fun i => orientExprQ (s.rules i).sense (s.snapshot.constraints i)) }

def normalizedSourceQ {n : ℕ} (s : SourceQ n) : ProximalGradientOrdering.SourceQ n :=
  { ordering := s.ordering
    snapshot :=
      { s.snapshot with
        constraints := fun i => normalizeExprQ (s.rules i) (s.snapshot.constraints i) } }

def restoredSnapshotQ {n : ℕ} (s : SourceQ n) : SnapshotQ n :=
  { (normalizedSourceQ s).snapshot with
    constraints := fun i => encodeExprQ (s.rules i) ((normalizedSourceQ s).snapshot.constraints i) }

theorem snapshot_roundtrip {n : ℕ} (s : SourceQ n) (hr : checkRulesQ s.rules = true) :
    restoredSnapshotQ s = s.snapshot := by
  have hp := (checkRulesQ_eq_true_iff s.rules).mp hr
  apply SnapshotQ.ext <;> try rfl
  funext i
  exact encode_normalize (s.rules i) (ne_of_gt (hp i)) (s.snapshot.constraints i)

/-- Every real-data row inequality is preserved, not just the final objective. -/
theorem rows_feasible_iff {n : ℕ} (s : SourceQ n) (hr : checkRulesQ s.rules = true)
    (d : DataR (Fin (valueCount n)) (basisCount n)) :
    (∀ i, HoldsR (s.rules i).sense (s.snapshot.constraints i) d) ↔
      ∀ i, 0 ≤ ((normalizedSourceQ s).snapshot.constraints i).evalR d := by
  have hp := (checkRulesQ_eq_true_iff s.rules).mp hr
  constructor
  · intro h i
    exact (normalize_nonneg_iff (s.rules i) (hp i) (s.snapshot.constraints i) d).mpr (h i)
  · intro h i
    exact (normalize_nonneg_iff (s.rules i) (hp i) (s.snapshot.constraints i) d).mp (h i)

def checkSourceQ {n : ℕ} (s : SourceQ n) : Bool :=
  checkRulesQ s.rules && ProximalGradientOrdering.checkSourceQ (normalizedSourceQ s)

theorem checkSourceQ_eq_true_iff {n : ℕ} (s : SourceQ n) :
    checkSourceQ s = true ↔ checkRulesQ s.rules = true ∧
      ProximalGradientOrdering.checkSourceQ (normalizedSourceQ s) = true := by
  simp only [checkSourceQ, Bool.and_eq_true]

theorem source_binding {n : ℕ} (s : SourceQ n) (hs : checkSourceQ s = true) :
    ProximalGradientOrdering.nativeSourceQ (normalizedSourceQ s) =
      ProximalGradientCoordinates.expectedSourceQ n :=
  ((ProximalGradientOrdering.checkSourceQ_eq_true_iff _).mp
    ((checkSourceQ_eq_true_iff s).mp hs).2).2

def sourceRowQ {n : ℕ} (s : SourceQ n) (t : AssumptionTermQ s.model) : Fin (rowCount n) :=
  ⟨t.index.val, by simpa only [SourceQ.model, List.length_ofFn] using t.index.isLt⟩

def normalizedAssumptionQ {n : ℕ} (s : SourceQ n) (t : AssumptionTermQ s.model) :
    AssumptionTermQ (normalizedSourceQ s).model :=
  { weight := t.weight * (s.rules (sourceRowQ s t)).scale
    index := ⟨t.index.val, by
      have hi : t.index.val < rowCount n := (sourceRowQ s t).isLt
      simpa only [normalizedSourceQ, ProximalGradientOrdering.SourceQ.model, SnapshotQ.toNative,
        ProximalGradientCoordinates.SourceQ.model, List.length_ofFn] using hi⟩ }

@[simp] theorem normalizedAssumptionQ_weight {n : ℕ} (s : SourceQ n) (t : AssumptionTermQ s.model) :
    (normalizedAssumptionQ s t).weight = t.weight * (s.rules (sourceRowQ s t)).scale := rfl

@[simp] theorem normalizedAssumptionQ_index {n : ℕ} (s : SourceQ n) (t : AssumptionTermQ s.model) :
    (normalizedAssumptionQ s t).index.val = t.index.val := rfl

theorem source_get {n : ℕ} (s : SourceQ n) (t : AssumptionTermQ s.model) :
    s.model.assumptions.get t.index =
      orientExprQ (s.rules (sourceRowQ s t)).sense (s.snapshot.constraints (sourceRowQ s t)) := by
  exact List.get_ofFn
    (fun i => orientExprQ (s.rules i).sense (s.snapshot.constraints i)) t.index

theorem normalized_get {n : ℕ} (s : SourceQ n) (t : AssumptionTermQ s.model) :
    (normalizedSourceQ s).model.assumptions.get (normalizedAssumptionQ s t).index =
      normalizeExprQ (s.rules (sourceRowQ s t)) (s.snapshot.constraints (sourceRowQ s t)) := by
  exact List.get_ofFn
    (fun i => normalizeExprQ (s.rules i) (s.snapshot.constraints i))
    (normalizedAssumptionQ s t).index

/-- Preserve the complete symbolic assumption sum, including constants and both Gram axes. -/
theorem assumption_sum_preserved {n : ℕ} (s : SourceQ n) (hr : checkRulesQ s.rules = true)
    (ts : List (AssumptionTermQ s.model)) :
    assumptionExprSumQ (normalizedSourceQ s).model (ts.map (normalizedAssumptionQ s)) =
      assumptionExprSumQ s.model ts := by
  have hp := (checkRulesQ_eq_true_iff s.rules).mp hr
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp only [List.map_cons, assumptionExprSumQ, normalizedAssumptionQ_weight,
        normalized_get, source_get, ih]
      rw [weighted_normalize (s.rules (sourceRowQ s t)) (ne_of_gt (hp _))]

/-- No term or factor is synthesized, dropped, reordered, or silently rounded here. -/
def normalizedUpperQ {n : ℕ} (s : SourceQ n) (c : UpperCertQ s.model) :
    UpperCertQ (normalizedSourceQ s).model :=
  { bound := c.bound
    objective := c.objective
    interpTerms := c.interpTerms
    assumptionTerms := c.assumptionTerms.map (normalizedAssumptionQ s)
    dualMatrix := c.dualMatrix
    dualFactor := c.dualFactor }

@[simp] theorem normalizedUpperQ_bound {n : ℕ} (s : SourceQ n) (c : UpperCertQ s.model) :
    (normalizedUpperQ s c).bound = c.bound := rfl

theorem normalizedUpperQ_assumption_count {n : ℕ} (s : SourceQ n) (c : UpperCertQ s.model) :
    (normalizedUpperQ s c).assumptionTerms.length = c.assumptionTerms.length := by
  simp only [normalizedUpperQ, List.length_map]

theorem certificate_rhs_preserved {n : ℕ} (s : SourceQ n) (hr : checkRulesQ s.rules = true)
    (c : UpperCertQ s.model) (hi : c.interpTerms = []) :
    certificateRhsExprQ (normalizedUpperQ s c) = certificateRhsExprQ c := by
  simp only [certificateRhsExprQ, normalizedUpperQ, hi, interpExprSumQ]
  rw [assumption_sum_preserved s hr]

/-- A genuine preservation theorem for this normalization stage, in addition to
independent rechecking at the API boundary. The original checker is unchanged. -/
theorem normalizedUpper_check {n : ℕ} (s : SourceQ n) (hr : checkRulesQ s.rules = true)
    (c : UpperCertQ s.model) (hi : c.interpTerms = []) (hc : checkUpperCertQ c = true) :
    checkUpperCertQ (normalizedUpperQ s c) = true := by
  have hv := checkUpperCertQ_sound c hc
  have hp := (checkRulesQ_eq_true_iff s.rules).mp hr
  apply checkUpperCertQ_complete (normalizedUpperQ s c)
  refine
    { interpWeights := hv.interpWeights
      assumptionWeights := ?_
      dualValid := hv.dualValid
      identity := ?_ }
  · intro t ht
    change t ∈ c.assumptionTerms.map (normalizedAssumptionQ s) at ht
    rcases List.mem_map.mp ht with ⟨u, hu, rfl⟩
    exact normalized_weight_nonneg (s.rules (sourceRowQ s u)) (hp _) u.weight
      (hv.assumptionWeights u hu)
  · exact (certificate_rhs_preserved s hr c hi).trans hv.identity

/-- Signed raw semantics are oriented FIRST; positive normalization, raw checker,
empty implicit interpolation, objective binding, and all D4 guards remain mandatory. -/
def checkBoundQ {n : ℕ} (s : SourceQ n) (c : UpperCertQ s.model) : Bool :=
  checkSourceQ s && (checkUpperCertQ c && (decide (c.interpTerms = []) &&
    (checkLinearExprEqQ c.objective s.snapshot.objective &&
      ProximalGradientOrdering.checkBoundQ (normalizedSourceQ s) (normalizedUpperQ s c))))

theorem checkBoundQ_eq_true_iff {n : ℕ} (s : SourceQ n) (c : UpperCertQ s.model) :
    checkBoundQ s c = true ↔ checkSourceQ s = true ∧ checkUpperCertQ c = true ∧
      c.interpTerms = [] ∧ c.objective = s.snapshot.objective ∧
      ProximalGradientOrdering.checkBoundQ (normalizedSourceQ s) (normalizedUpperQ s c) = true := by
  simp only [checkBoundQ, Bool.and_eq_true, decide_eq_true_eq, checkLinearExprEqQ_eq_true_iff]

theorem checked_certificate {n : ℕ} (s : SourceQ n) (c : UpperCertQ s.model)
    (hc : checkBoundQ s c = true) :
    ∃ d : UpperCertQ (Profiles.ProximalGradient.modelQ n),
      checkUpperCertQ d = true ∧ d.interpTerms = [] ∧
      d.objective = Profiles.ProximalGradient.objectiveQ n ∧ d.bound = c.bound := by
  have ht := ((checkBoundQ_eq_true_iff s c).mp hc).2.2.2.2
  obtain ⟨d, hd, hi, ho, hb⟩ := ProximalGradientOrdering.checked_certificate
    (normalizedSourceQ s) (normalizedUpperQ s c) ht
  exact ⟨d, hd, hi, ho, hb⟩

end LeanPEP.Adapters.ProximalGradientRows
