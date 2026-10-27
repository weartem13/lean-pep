import LeanPEP.Imported.CompositeOrdering

/-! D4 proofs are independent of the literal data generator. The two inverse
maps are checked, even when an unused malformed inverse would leave the
normalized source unchanged. All negative tests keep the intended rejection. -/
namespace LeanPEP.Imported.CompositeOrdering

open LeanPEP.GramPEP LeanPEP.GramPEP.ExactReindexing
open LeanPEP.Adapters.ProximalGradientOrdering

namespace PGOne

theorem ordering_check : checkOrderingQ orderingQ = true := by decide +kernel
theorem source_check : checkSourceQ sourceQ = true := by decide +kernel
theorem raw_upper_check : checkUpperCertQ upperQ = true := by decide +kernel
theorem native_bound_check :
    Adapters.ProximalGradientCoordinates.checkBoundQ (nativeSourceQ sourceQ)
      (nativeUpperQ sourceQ upperQ) = true := by decide +kernel
theorem bound_check : checkBoundQ sourceQ upperQ = true := by decide +kernel

end PGOne
namespace PGTwo

theorem source_check : checkSourceQ sourceQ = true := by decide +kernel
theorem bound_check : checkBoundQ sourceQ upperQ = true := by decide +kernel

end PGTwo
namespace PGThree

theorem source_check : checkSourceQ sourceQ = true := by decide +kernel
theorem bound_check : checkBoundQ sourceQ upperQ = true := by decide +kernel

end PGThree
namespace PGIdentity

theorem source_check : checkSourceQ sourceQ = true := by decide +kernel
theorem bound_check : checkBoundQ sourceQ upperQ = true := by decide +kernel

end PGIdentity

/-- This source has a correct gather map but a false supplied inverse. -/
def badInverseQ : SourceQ 0 :=
  { PGOne.sourceQ with
    ordering :=
      { PGOne.orderingQ with
        basis := { PGOne.orderingQ.basis with toCanonical := fun _ => 0 } } }

theorem bad_inverse_native_passes :
    Adapters.ProximalGradientCoordinates.checkSourceQ (nativeSourceQ badInverseQ) = true := by
  decide +kernel

theorem bad_inverse_rejected : checkSourceQ badInverseQ = false := by decide +kernel

/-- Storage-order labels are audited, not just metadata to be overwritten. -/
def wrongLabelQ : SourceQ 0 :=
  { PGOne.sourceQ with
    snapshot :=
      { PGOne.snapshotQ with
        basisLabels := fun i => if i = 0 then "wrong_basis" else PGOne.snapshotQ.basisLabels i } }

theorem wrong_label_rejected : checkSourceQ wrongLabelQ = false := by decide +kernel

/-- Reordering the source does not license leaving multiplier row references wrong. -/
def wrongRowsQ : UpperCertQ PGOne.sourceQ.model :=
  { PGOne.upperQ with
    assumptionTerms := PGOne.upperQ.assumptionTerms.map (fun t =>
      { weight := t.weight, index := ⟨0, by decide +kernel⟩ }) }

theorem wrong_rows_local_rejected : checkUpperCertQ wrongRowsQ = false := by decide +kernel
theorem wrong_rows_joint_rejected : checkBoundQ PGOne.sourceQ wrongRowsQ = false := by decide +kernel

/-- Zero-weight cross-component implicit terms must not be silently deleted. -/
def implicitQ : UpperCertQ PGOne.sourceQ.model :=
  { PGOne.upperQ with interpTerms := [{ weight := 0, i := 0, j := 1 }] }

theorem implicit_local_passes : checkUpperCertQ implicitQ = true := by decide +kernel
theorem implicit_joint_rejected : checkBoundQ PGOne.sourceQ implicitQ = false := by decide +kernel

/-- A locally valid certificate of a forged problem is still rejected. -/
def forgedSourceQ : SourceQ 0 :=
  { PGOne.sourceQ with
    snapshot :=
      { PGOne.snapshotQ with
        constraints := fun i => if i = 0 then LinearExprQ.neg PGOne.snapshotQ.objective
          else PGOne.snapshotQ.constraints i } }

def forgedUpperQ : UpperCertQ forgedSourceQ.model :=
  { bound := 0
    objective := forgedSourceQ.snapshot.objective
    interpTerms := []
    assumptionTerms := [{ weight := 1, index := ⟨0, by decide +kernel⟩ }]
    dualMatrix := 0
    dualFactor := { factors := [] } }

theorem forged_local_passes : checkUpperCertQ forgedUpperQ = true := by decide +kernel
theorem forged_joint_rejected : checkBoundQ forgedSourceQ forgedUpperQ = false := by decide +kernel

/-- In this example the value map is a genuine cycle, not its own inverse. -/
theorem value_map_not_involution :
    PGOne.orderingQ.values.toSource 0 ≠ PGOne.orderingQ.values.toCanonical 0 := by
  decide +kernel

theorem payload_roundtrip :
    reorderSnapshotQ PGOne.orderingQ.symm (reorderSnapshotQ PGOne.orderingQ PGOne.snapshotQ) =
      PGOne.snapshotQ :=
  reorderSnapshotQ_roundtrip PGOne.orderingQ PGOne.ordering_check PGOne.snapshotQ

end LeanPEP.Imported.CompositeOrdering
