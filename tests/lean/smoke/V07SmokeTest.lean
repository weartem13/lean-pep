import LeanPEP

namespace LeanPEP

-- One report displays both exact semantics.  The raw decimal interpretation is
-- rejected; the separately reconstructed exact candidate is accepted.
#eval Imported.TwoStepApproxComparison.comparisonQ

example :
    Toy.FiniteGD.checkExactBundleQ
      Imported.TwoStepApproxRaw.bundleQ = false := by
  exact Imported.TwoStepApproxComparison.rawBundleQ_rejected

example :
    Toy.FiniteGD.checkExactBundleQ
      Imported.TwoStepApproxReconstructed.bundleQ = true := by
  exact Imported.TwoStepApproxComparison.reconstructedBundleQ_check

-- The raw source is not merely "outside a tolerance": it has a concrete exact
-- interpolation residual of -1 / 5,000,000,000.
example :
    Toy.FiniteGD.slack Imported.TwoStepApproxRaw.primalQ
      (Toy.FiniteGD.Point.iter (N := 2) 0)
      (Toy.FiniteGD.Point.iter (N := 2) 1) =
        ((-1 : ℚ) / 5000000000) := by
  native_decide

example :
    Toy.FiniteGD.slack Imported.TwoStepApproxRaw.primalQ
      (Toy.FiniteGD.Point.iter (N := 2) 0)
      (Toy.FiniteGD.Point.iter (N := 2) 2) =
        ((-1 : ℚ) / 5000000000) := by
  native_decide

-- Acceptance of the reconstructed track retains the same exact real semantic
-- consequences as every schema-v1 exact bundle.
example :
    Toy.FiniteGD.Feasible
      (Toy.FiniteGD.toRealData
        Imported.TwoStepApproxReconstructed.primalQ) := by
  exact Imported.TwoStepApproxReconstructed.bundleQ_sound_real.2.1

example
    (d : Toy.FiniteGD.DataR 2)
    (h : Toy.FiniteGD.Feasible d) :
    d.value Imported.TwoStepApproxReconstructed.upperCertQ.objective ≤
      (Imported.TwoStepApproxReconstructed.upperCertQ.bound : ℝ) := by
  exact
    Imported.TwoStepApproxReconstructed.bundleQ_sound_real.2.2.2 d h

end LeanPEP
