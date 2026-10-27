import LeanPEP.Imported.CompositePerformance

/-! D6: independent checker proofs on literal submitted data, including negative
cases which still pass AFTER projection. No native_decide, no new axioms. -/
namespace LeanPEP.Imported.CompositePerformance
open LeanPEP.GramPEP LeanPEP.GramPEP.PerformanceLift
open LeanPEP.Adapters.ProximalGradientPerformance

namespace PGOne
theorem lift_check : checkLiftQ sourceQ = true := by decide +kernel
theorem source_check : checkSourceQ sourceQ = true := by decide +kernel
theorem raw_check : checkUpperCertQ upperQ = true := by decide +kernel
theorem eliminated_check : checkUpperCertQ (eliminatedUpperQ sourceQ upperQ) = true :=
  eliminatedUpper_check sourceQ lift_check upperQ rfl raw_check
theorem bound_check : checkBoundQ sourceQ upperQ = true := by decide +kernel
theorem performance_mass : performanceMassQ sourceQ upperQ.assumptionTerms = 1 := by
  apply performance_mass_eq_one sourceQ lift_check upperQ rfl _ raw_check
  change sourceQ.objective = _
  exact ((checkLiftQ_eq_true_iff sourceQ).mp lift_check).2.2
end PGOne

namespace PGTwo
theorem lift_check : checkLiftQ sourceQ = true := by decide +kernel
theorem source_check : checkSourceQ sourceQ = true := by decide +kernel
theorem raw_check : checkUpperCertQ upperQ = true := by decide +kernel
theorem eliminated_check : checkUpperCertQ (eliminatedUpperQ sourceQ upperQ) = true :=
  eliminatedUpper_check sourceQ lift_check upperQ rfl raw_check
theorem bound_check : checkBoundQ sourceQ upperQ = true := by decide +kernel
theorem performance_mass : performanceMassQ sourceQ upperQ.assumptionTerms = 1 := by
  apply performance_mass_eq_one sourceQ lift_check upperQ rfl _ raw_check
  change sourceQ.objective = _
  exact ((checkLiftQ_eq_true_iff sourceQ).mp lift_check).2.2
end PGTwo

namespace PGThree
theorem lift_check : checkLiftQ sourceQ = true := by decide +kernel
theorem source_check : checkSourceQ sourceQ = true := by decide +kernel
theorem raw_check : checkUpperCertQ upperQ = true := by decide +kernel
theorem eliminated_check : checkUpperCertQ (eliminatedUpperQ sourceQ upperQ) = true :=
  eliminatedUpper_check sourceQ lift_check upperQ rfl raw_check
theorem bound_check : checkBoundQ sourceQ upperQ = true := by decide +kernel
theorem performance_mass : performanceMassQ sourceQ upperQ.assumptionTerms = 1 := by
  apply performance_mass_eq_one sourceQ lift_check upperQ rfl _ raw_check
  change sourceQ.objective = _
  exact ((checkLiftQ_eq_true_iff sourceQ).mp lift_check).2.2
end PGThree

namespace PGUnit
theorem lift_check : checkLiftQ sourceQ = true := by decide +kernel
theorem source_check : checkSourceQ sourceQ = true := by decide +kernel
theorem raw_check : checkUpperCertQ upperQ = true := by decide +kernel
theorem eliminated_check : checkUpperCertQ (eliminatedUpperQ sourceQ upperQ) = true :=
  eliminatedUpper_check sourceQ lift_check upperQ rfl raw_check
theorem bound_check : checkBoundQ sourceQ upperQ = true := by decide +kernel
theorem performance_mass : performanceMassQ sourceQ upperQ.assumptionTerms = 1 := by
  apply performance_mass_eq_one sourceQ lift_check upperQ rfl _ raw_check
  change sourceQ.objective = _
  exact ((checkLiftQ_eq_true_iff sourceQ).mp lift_check).2.2
end PGUnit

/-- Eliminating an arbitrary term that vanishes at tau=metric would conceal a
source error. The extended row is compared BEFORE that noninjective operation. -/
def hiddenTauQ : SourceQ 0 :=
  { PGUnit.sourceQ with
    rows := fun i => if i = 1 then LinearExprQ.add (PGUnit.sourceQ.rows i)
      (linkExprQ PGUnit.sourceQ.base.snapshot.objective) else PGUnit.sourceQ.rows i }

theorem hidden_tau_after_substitution_equal :
    checkLinearExprEqQ
      (substituteQ PGUnit.sourceQ.base.snapshot.objective (hiddenTauQ.rows 1))
      (substituteQ PGUnit.sourceQ.base.snapshot.objective (PGUnit.sourceQ.rows 1)) = true := by
  decide +kernel

theorem hidden_tau_source_rejected : checkSourceQ hiddenTauQ = false := by decide +kernel

/-- The base certificate does not see the removed link weight. The raw FULL
certificate check is mandatory and rejects doubling that weight. -/
def wrongPerformanceWeightQ : UpperCertQ PGOne.sourceQ.model :=
  { PGOne.upperQ with
    assumptionTerms := PGOne.upperQ.assumptionTerms.map
      (fun t => { t with weight := if t.index.val = 0 then 2*t.weight else t.weight }) }

theorem wrong_performance_eliminated_passes :
    Adapters.ProximalGradientRows.checkBoundQ PGOne.sourceQ.base
      (eliminatedUpperQ PGOne.sourceQ wrongPerformanceWeightQ) = true := by decide +kernel

theorem wrong_performance_raw_rejected : checkUpperCertQ wrongPerformanceWeightQ = false := by decide +kernel

theorem wrong_performance_joint_rejected :
    checkBoundQ PGOne.sourceQ wrongPerformanceWeightQ = false := by decide +kernel

def wrongSenseQ : SourceQ 0 :=
  { PGUnit.sourceQ with performanceRule := { sense := .leZero, scale := 1 } }

theorem wrong_sense_rejected : checkSourceQ wrongSenseQ = false := by decide +kernel

def zeroScaleQ : SourceQ 0 :=
  { PGUnit.sourceQ with performanceRule := { sense := .geZero, scale := 0 } }

theorem zero_scale_rejected : checkSourceQ zeroScaleQ = false := by decide +kernel

/-- The auxiliary value is NOT an extra point of the smooth function. Even
zero-weight implicit cross-value terms are disallowed rather than laundered. -/
def implicitQ : UpperCertQ PGOne.sourceQ.model :=
  { PGOne.upperQ with interpTerms := [{ weight := 0, i := 0, j := 1 }] }

theorem implicit_local_passes : checkUpperCertQ implicitQ = true := by decide +kernel

theorem implicit_joint_rejected : checkBoundQ PGOne.sourceQ implicitQ = false := by decide +kernel

def zeroObjectiveQ : UpperCertQ PGOne.sourceQ.model :=
  { bound := 0
    objective := LinearExprQ.zero _ _
    interpTerms := []
    assumptionTerms := []
    dualMatrix := 0
    dualFactor := { factors := [] } }

theorem zero_objective_local_passes : checkUpperCertQ zeroObjectiveQ = true := by decide +kernel

theorem zero_objective_joint_rejected : checkBoundQ PGOne.sourceQ zeroObjectiveQ = false := by decide +kernel

/-- Duplicate references in PGTwo are intentional, and neither alone has unit mass. -/
theorem split_performance_mass : performanceMassQ PGTwo.sourceQ PGTwo.upperQ.assumptionTerms = 1 :=
  PGTwo.performance_mass

theorem one_rhs_preserved :
    substituteQ PGOne.sourceQ.base.snapshot.objective (certificateRhsExprQ PGOne.upperQ) =
      certificateRhsExprQ (eliminatedUpperQ PGOne.sourceQ PGOne.upperQ) :=
  certificate_rhs_preserved PGOne.sourceQ PGOne.lift_check PGOne.upperQ rfl

end LeanPEP.Imported.CompositePerformance
