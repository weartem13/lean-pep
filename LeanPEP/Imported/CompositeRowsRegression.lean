import LeanPEP.Imported.CompositeRows

/-! D5 acceptance/rejection proofs are separate from literal data generation.
Positive scales are required even for an unused zero diagonal pair. -/
namespace LeanPEP.Imported.CompositeRows

open LeanPEP.GramPEP LeanPEP.GramPEP.RowNormalization
open LeanPEP.Adapters.ProximalGradientRows

namespace PGOne

theorem rules_check : checkRulesQ rulesQ = true := by decide +kernel
theorem source_check : checkSourceQ sourceQ = true := by decide +kernel
theorem raw_upper_check : checkUpperCertQ upperQ = true := by decide +kernel
theorem normalized_upper_check : checkUpperCertQ (normalizedUpperQ sourceQ upperQ) = true :=
  normalizedUpper_check sourceQ rules_check upperQ rfl raw_upper_check
theorem normalized_bound_check :
    Adapters.ProximalGradientOrdering.checkBoundQ (normalizedSourceQ sourceQ)
      (normalizedUpperQ sourceQ upperQ) = true := by decide +kernel
theorem bound_check : checkBoundQ sourceQ upperQ = true := by decide +kernel

end PGOne
namespace PGTwo

theorem bound_check : checkBoundQ sourceQ upperQ = true := by decide +kernel

end PGTwo
namespace PGThree

theorem bound_check : checkBoundQ sourceQ upperQ = true := by decide +kernel

end PGThree
namespace PGUnit

theorem bound_check : checkBoundQ sourceQ upperQ = true := by decide +kernel

end PGUnit

/-- A zero self-pair stays zero after dividing by zero in Lean's field convention.
The source guard must still reject that forbidden scale. -/
def zeroScaleQ : SourceQ 0 :=
  { PGUnit.sourceQ with
    rules := fun i => { PGUnit.rulesQ i with scale := if i = 0 then 0 else (PGUnit.rulesQ i).scale } }

theorem zero_scale_normalized_passes :
    Adapters.ProximalGradientOrdering.checkSourceQ (normalizedSourceQ zeroScaleQ) = true := by
  decide +kernel

theorem zero_scale_rejected : checkSourceQ zeroScaleQ = false := by decide +kernel

def negativeScaleQ : SourceQ 0 :=
  { PGUnit.sourceQ with
    rules := fun i => { PGUnit.rulesQ i with scale := if i = 0 then -1 else (PGUnit.rulesQ i).scale } }

theorem negative_scale_normalized_passes :
    Adapters.ProximalGradientOrdering.checkSourceQ (normalizedSourceQ negativeScaleQ) = true := by
  decide +kernel

theorem negative_scale_rejected : checkSourceQ negativeScaleQ = false := by decide +kernel

/-- Wrong direction on a NONZERO ordered pair cannot pass source binding. -/
def wrongSenseQ : SourceQ 0 :=
  { PGUnit.sourceQ with
    rules := fun i => { PGUnit.rulesQ i with sense := if i = 1 then .leZero else (PGUnit.rulesQ i).sense } }

theorem wrong_sense_rejected : checkSourceQ wrongSenseQ = false := by decide +kernel

/-- Wrong positive scale on a nonzero row is not silently inferred/repaired. -/
def wrongScaleQ : SourceQ 0 :=
  { PGUnit.sourceQ with
    rules := fun i => { PGUnit.rulesQ i with scale := if i = 1 then 2 else (PGUnit.rulesQ i).scale } }

theorem wrong_scale_rejected : checkSourceQ wrongScaleQ = false := by decide +kernel

def wrongWeightsQ : UpperCertQ PGOne.sourceQ.model :=
  { PGOne.upperQ with
    assumptionTerms := PGOne.upperQ.assumptionTerms.map (fun t => { t with weight := 2*t.weight }) }

theorem wrong_weights_rejected : checkBoundQ PGOne.sourceQ wrongWeightsQ = false := by decide +kernel

/-- A zero-weight cross-component interpolation term is preserved, not erased. -/
def implicitQ : UpperCertQ PGOne.sourceQ.model :=
  { PGOne.upperQ with interpTerms := [{ weight := 0, i := 0, j := 1 }] }

theorem implicit_local_passes : checkUpperCertQ implicitQ = true := by decide +kernel
theorem implicit_joint_rejected : checkBoundQ PGOne.sourceQ implicitQ = false := by decide +kernel

/-- A correct local certificate of a forged problem still does not prove PG. -/
def forgedSourceQ : SourceQ 0 :=
  { PGUnit.sourceQ with
    snapshot :=
      { PGUnit.snapshotQ with
        constraints := fun i => if i = 0 then LinearExprQ.neg PGUnit.snapshotQ.objective
          else PGUnit.snapshotQ.constraints i } }

def forgedUpperQ : UpperCertQ forgedSourceQ.model :=
  { bound := 0
    objective := forgedSourceQ.snapshot.objective
    interpTerms := []
    assumptionTerms := [{ weight := 1, index := ⟨0, by decide +kernel⟩ }]
    dualMatrix := 0
    dualFactor := { factors := [] } }

theorem forged_local_passes : checkUpperCertQ forgedUpperQ = true := by decide +kernel
theorem forged_joint_rejected : checkBoundQ forgedSourceQ forgedUpperQ = false := by decide +kernel

theorem one_snapshot_roundtrip : restoredSnapshotQ PGOne.sourceQ = PGOne.snapshotQ :=
  snapshot_roundtrip PGOne.sourceQ PGOne.rules_check

theorem one_rhs_preserved :
    certificateRhsExprQ (normalizedUpperQ PGOne.sourceQ PGOne.upperQ) =
      certificateRhsExprQ PGOne.upperQ :=
  certificate_rhs_preserved PGOne.sourceQ PGOne.rules_check PGOne.upperQ rfl

end LeanPEP.Imported.CompositeRows
