import LeanPEP.Imported.CompositeCoordinates

/-! D3 independent checks; the imported file contains data only.
Hidden origin terms demonstrate why zero-origin restriction alone is unsound
as a claim of equality of native source formulations. -/
namespace LeanPEP.Imported.CompositeCoordinates

open LeanPEP.GramPEP LeanPEP.GramPEP.OriginCoordinates
open LeanPEP.Adapters.ProximalGradientCoordinates

namespace PGOne

theorem source_check : checkSourceQ sourceQ = true := by decide +kernel
theorem native_upper_check : checkUpperCertQ upperQ = true := by decide +kernel
theorem centered_bound_check :
    Adapters.ProximalGradientSource.checkBoundQ (centeredSourceQ sourceQ)
      (centeredUpperQ sourceQ upperQ) = true := by decide +kernel
theorem bound_check : checkBoundQ sourceQ upperQ = true := by decide +kernel

end PGOne
namespace PGTwo

theorem source_check : checkSourceQ sourceQ = true := by decide +kernel
theorem native_upper_check : checkUpperCertQ upperQ = true := by decide +kernel
theorem centered_bound_check :
    Adapters.ProximalGradientSource.checkBoundQ (centeredSourceQ sourceQ)
      (centeredUpperQ sourceQ upperQ) = true := by decide +kernel
theorem bound_check : checkBoundQ sourceQ upperQ = true := by decide +kernel

end PGTwo
namespace PGThree

theorem source_check : checkSourceQ sourceQ = true := by decide +kernel
theorem native_upper_check : checkUpperCertQ upperQ = true := by decide +kernel
theorem centered_bound_check :
    Adapters.ProximalGradientSource.checkBoundQ (centeredSourceQ sourceQ)
      (centeredUpperQ sourceQ upperQ) = true := by decide +kernel
theorem bound_check : checkBoundQ sourceQ upperQ = true := by decide +kernel

end PGThree

/-- A source term vanishing at x_star=0 still changes the native formulation. -/
def hiddenOriginQ : SourceQ 0 :=
  { PGOne.sourceQ with
    constraints :=
      LinearExprQ.gramNorm (standardBasisExpr (0 : Fin 6)) :: PGOne.sourceQ.constraints.tail }

theorem hidden_origin_centered_passes :
    Adapters.ProximalGradientSource.checkSourceQ (centeredSourceQ hiddenOriginQ) = true := by
  decide +kernel

theorem hidden_origin_native_rejected : checkSourceQ hiddenOriginQ = false := by
  decide +kernel

def wrongPointOriginQ : SourceQ 0 :=
  { PGOne.sourceQ with
    smoothSamples :=
      PGOne.sourceQ.smoothSamples.map (fun s =>
        { s with position := fun i => if i = 0 then s.position i + 1 else s.position i }) }

theorem wrong_point_centered_passes :
    Adapters.ProximalGradientSource.checkSourceQ (centeredSourceQ wrongPointOriginQ) = true := by
  decide +kernel

theorem wrong_point_native_rejected : checkSourceQ wrongPointOriginQ = false := by
  decide +kernel

def wrongCenterQ : SourceQ 0 :=
  { PGOne.sourceQ with
    centerMatrix := fun i j => if i = 0 ∧ j = 0 then 1 else PGOne.sourceQ.centerMatrix i j }

def wrongSectionQ : SourceQ 0 :=
  { PGOne.sourceQ with
    sectionMatrix := fun i j => if i = 0 ∧ j = 0 then 1 else PGOne.sourceQ.sectionMatrix i j }

theorem wrong_center_rejected : checkSourceQ wrongCenterQ = false := by decide +kernel
theorem wrong_section_rejected : checkSourceQ wrongSectionQ = false := by decide +kernel

/-- A defective origin-origin dual entry vanishes under restriction. The native
upper checker must still reject it, even when the restricted certificate passes. -/
def wrongNativeDualQ : UpperCertQ PGOne.sourceQ.model :=
  { PGOne.upperQ with
    dualMatrix := fun i j =>
      if i = 0 ∧ j = 0 then PGOne.upperQ.dualMatrix i j + 1 else PGOne.upperQ.dualMatrix i j }

theorem wrong_native_dual_centered_passes :
    Adapters.ProximalGradientSource.checkBoundQ (centeredSourceQ PGOne.sourceQ)
      (centeredUpperQ PGOne.sourceQ wrongNativeDualQ) = true := by decide +kernel

theorem wrong_native_dual_local_rejected : checkUpperCertQ wrongNativeDualQ = false := by
  decide +kernel

theorem wrong_native_dual_joint_rejected : checkBoundQ PGOne.sourceQ wrongNativeDualQ = false := by
  decide +kernel

def implicitQ : UpperCertQ PGOne.sourceQ.model :=
  { PGOne.upperQ with interpTerms := [{ weight := 0, i := 0, j := 1 }] }

theorem implicit_local_passes : checkUpperCertQ implicitQ = true := by decide +kernel
theorem implicit_joint_rejected : checkBoundQ PGOne.sourceQ implicitQ = false := by decide +kernel

end LeanPEP.Imported.CompositeCoordinates
