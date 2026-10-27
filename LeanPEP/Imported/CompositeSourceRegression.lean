import LeanPEP.Imported.CompositeSource

/-!
# D2 independent checker invocations and source/certificate separation

The imported file contains data only. Acceptance is proved here by the old
checker and the new proved source-binding layer. Rejection concerns a submitted
snapshot/certificate, never the falsity of an optimization theorem.
-/

namespace LeanPEP.Imported.CompositeSource
open LeanPEP.GramPEP LeanPEP.Adapters.ProximalGradientSource

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem PGOne.source_check : checkSourceQ PGOne.sourceQ = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem PGTwo.source_check : checkSourceQ PGTwo.sourceQ = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem PGThree.source_check : checkSourceQ PGThree.sourceQ = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem PGOne.upper_check : checkUpperCertQ PGOne.upperQ = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem PGTwo.upper_check : checkUpperCertQ PGTwo.upperQ = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem PGThree.upper_check : checkUpperCertQ PGThree.upperQ = true := by decide +kernel

theorem PGOne.bound_check : checkBoundQ PGOne.sourceQ PGOne.upperQ = true :=
  (checkBoundQ_eq_true_iff _ _).mpr ⟨PGOne.source_check, PGOne.upper_check, rfl, rfl⟩

theorem PGTwo.bound_check : checkBoundQ PGTwo.sourceQ PGTwo.upperQ = true :=
  (checkBoundQ_eq_true_iff _ _).mpr ⟨PGTwo.source_check, PGTwo.upper_check, rfl, rfl⟩

theorem PGThree.bound_check : checkBoundQ PGThree.sourceQ PGThree.upperQ = true :=
  (checkBoundQ_eq_true_iff _ _).mpr ⟨PGThree.source_check, PGThree.upper_check, rfl, rfl⟩

/-- A forged extra condition makes a zero bound valid for the WRONG formulation.
All coefficients, weights and factors are exact. Only source binding blocks it. -/
def forgedSourceQ : SourceQ 0 :=
  { PGOne.sourceQ with
    constraints :=
      LinearExprQ.neg PGOne.sourceQ.objective :: PGOne.sourceQ.constraints.tail }

def forgedUpperQ : UpperCertQ forgedSourceQ.model :=
  { bound := 0
    objective := forgedSourceQ.objective
    interpTerms := []
    assumptionTerms := [{ weight := 1, index := ⟨0, by decide +kernel⟩ }]
    dualMatrix := 0
    dualFactor := { factors := [] } }

theorem forged_local_certificate_accepted : checkUpperCertQ forgedUpperQ = true := by
  decide +kernel

theorem forged_source_rejected : checkSourceQ forgedSourceQ = false := by decide +kernel

theorem forged_bound_rejected : checkBoundQ forgedSourceQ forgedUpperQ = false := by decide +kernel

/-- A tautological zero objective is a valid local certificate, but not the PG goal. -/
def wrongObjectiveQ : UpperCertQ PGOne.sourceQ.model :=
  { bound := 0
    objective := LinearExprQ.zero _ _
    interpTerms := []
    assumptionTerms := []
    dualMatrix := 0
    dualFactor := { factors := [] } }

theorem wrong_objective_local_accepted : checkUpperCertQ wrongObjectiveQ = true := by decide +kernel

theorem wrong_objective_bound_rejected : checkBoundQ PGOne.sourceQ wrongObjectiveQ = false := by
  decide +kernel

/-- Even a zero-weight implicit interpolation term is excluded at this boundary. -/
def implicitTermQ : UpperCertQ PGOne.sourceQ.model :=
  { PGOne.upperQ with interpTerms := [{ weight := 0, i := 0, j := 3 }] }

theorem implicit_term_local_accepted : checkUpperCertQ implicitTermQ = true := by decide +kernel

theorem implicit_term_bound_rejected : checkBoundQ PGOne.sourceQ implicitTermQ = false := by
  decide +kernel

/-- Equal zero self-pair polynomials still have distinct semantic row tags. -/
def swappedTagsQ : SourceQ 0 :=
  { PGOne.sourceQ with
    header :=
      { PGOne.sourceQ.header with
        constraintOrder :=
          (PGOne.sourceQ.header.constraintOrder.set 0
            { kind := .smoothPair, i := some 1, j := some 1 }).set 4
            { kind := .smoothPair, i := some 0, j := some 0 } } }

theorem reordered_tags_rejected : checkSourceQ swappedTagsQ = false := by decide +kernel

def missingConstraintQ : SourceQ 0 :=
  { PGOne.sourceQ with constraints := PGOne.sourceQ.constraints.tail }

theorem missing_constraint_rejected : checkSourceQ missingConstraintQ = false := by decide +kernel

def reversedSenseQ : SourceQ 0 :=
  { PGOne.sourceQ with header := { PGOne.sourceQ.header with sense := .leZero } }

theorem reversed_sense_rejected : checkSourceQ reversedSenseQ = false := by decide +kernel

end LeanPEP.Imported.CompositeSource
