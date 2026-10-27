import LeanPEP

namespace LeanPEP

-- A complete externally generated lower/upper bundle is accepted.
#eval Toy.FiniteGD.auditExactBundleQ Imported.TwoStepExact.bundleQ

-- Three independent import-boundary rejection paths.
#eval Toy.FiniteGD.auditExactBundleQ Imported.TwoStepBadMetadata.bundleQ
#eval Toy.FiniteGD.auditExactBundleQ Imported.TwoStepBadPrimal.bundleQ
#eval Toy.FiniteGD.auditExactBundleQ Imported.TwoStepBadBound.bundleQ

example :
    Toy.FiniteGD.checkExactBundleQ Imported.TwoStepExact.bundleQ = true := by
  exact Imported.TwoStepExact.bundleQ_check

example :
    Toy.FiniteGD.checkExactBundleQ Imported.TwoStepBadMetadata.bundleQ = false := by
  exact Imported.TwoStepBadMetadata.bundleQ_rejected

example :
    Toy.FiniteGD.checkExactBundleQ Imported.TwoStepBadPrimal.bundleQ = false := by
  exact Imported.TwoStepBadPrimal.bundleQ_rejected

example :
    Toy.FiniteGD.checkExactBundleQ Imported.TwoStepBadBound.bundleQ = false := by
  exact Imported.TwoStepBadBound.bundleQ_rejected

-- The accepted generated bundle reconstructs a real feasible witness.
example :
    Toy.FiniteGD.Feasible
      (Toy.FiniteGD.toRealData Imported.TwoStepExact.primalQ) := by
  exact Imported.TwoStepExact.bundleQ_sound_real.2.1

-- The same accepted generated bundle proves a universal real upper bound.
example
    (d : Toy.FiniteGD.DataR 2)
    (h : Toy.FiniteGD.Feasible d) :
    d.value Imported.TwoStepExact.upperCertQ.objective ≤
      (Imported.TwoStepExact.upperCertQ.bound : ℝ) := by
  exact Imported.TwoStepExact.bundleQ_sound_real.2.2.2 d h

-- Its primal objective agrees exactly with its upper bound over ℚ.
example :
    Imported.TwoStepExact.primalQ.value
        Imported.TwoStepExact.upperCertQ.objective =
      Imported.TwoStepExact.upperCertQ.bound := by
  exact Imported.TwoStepExact.bundleQ_sound_real.2.2.1

end LeanPEP
