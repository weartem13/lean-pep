import LeanPEP

#check LeanPEP.Toy.FiniteGD.ParametricUpper.slackPolyQ_valueCoeff
#check LeanPEP.Toy.FiniteGD.ParametricUpper.interpPolySumQ_valueCoeff
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdStarTermsQ_valueCoeff
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdChainTermsQ_valueCoeff
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdCertificateRhs_valueCoeff_flow
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdCertificate_valueCoeff
#check LeanPEP.Toy.FiniteGD.ParametricUpper.gdCertificate_valueCoefficients

namespace LeanPEP.Toy.FiniteGD.V12B5Smoke

open LeanPEP.Toy.FiniteGD.ParametricUpper

/-- An intermediate function value has coefficient zero. -/
example :
    (certificateRhsPolyQ (gdUpperCertQ 4)).valueCoeff ⟨2, by omega⟩ = 0 := by
  simpa [gdObjective, unitCoeff, Fin.ext_iff] using
    (gdCertificate_valueCoeff 4 ⟨2, by omega⟩)

/-- The final function value has coefficient minus one. -/
example :
    (certificateRhsPolyQ (gdUpperCertQ 4)).valueCoeff ⟨4, by omega⟩ = -1 := by
  simpa [gdObjective, unitCoeff, Fin.ext_iff] using
    (gdCertificate_valueCoeff 4 ⟨4, by omega⟩)

/-- The all-index function-value channel is available uniformly in `N`. -/
example (N : ℕ) :
    ∀ r : Fin (N + 1),
      (certificateRhsPolyQ (gdUpperCertQ N)).valueCoeff r =
        (upperTargetPolyQ (gdBoundQ N) (gdObjective N)).valueCoeff r :=
  gdCertificate_valueCoefficients N

end LeanPEP.Toy.FiniteGD.V12B5Smoke
