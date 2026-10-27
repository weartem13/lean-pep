import LeanPEP

#check LeanPEP.ActualFunction.FiniteGram.gramOfVectors
#check LeanPEP.ActualFunction.FiniteGram.realize
#check LeanPEP.ActualFunction.FiniteGram.gramInner_gramOfVectors
#check LeanPEP.ActualFunction.FiniteGram.gramOfVectors_posSemidef
#check LeanPEP.ActualFunction.FiniteGram.dataOfModel_realizes
#check LeanPEP.ActualFunction.FiniteGram.interpolationSlack_dataOfModel
#check LeanPEP.ActualFunction.FiniteGram.dataOfModel_coreFeasible
#check LeanPEP.ActualFunction.OneStepGram.oneStepData
#check LeanPEP.ActualFunction.OneStepGram.oneStepData_realizesModel
#check LeanPEP.ActualFunction.OneStepGram.oneStepData_coreFeasible
#check LeanPEP.ActualFunction.OneStepGram.oneStepData_assumptionsFeasible
#check LeanPEP.ActualFunction.OneStepGram.oneStepData_feasible

namespace LeanPEP.ActualFunction.V12A3Smoke

open LeanPEP.ActualFunction
open LeanPEP.GramPEP
open LeanPEP.GramPEP.UpperCertificateExamples

/-- The generic finite-vector construction exposes a genuine PSD Gram matrix. -/
example
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ} (base : Fin m → E) :
    IsGramPosSemidef (FiniteGram.gramOfVectors base) :=
  FiniteGram.gramOfVectors_posSemidef base

/-- The one-step bridge packages exactly the three hypotheses consumed by the
existing one-step certificate theorem. -/
example
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {g : E → E} {xStar x0 x1 : E}
    (hfun : IsOneSmoothConvexAnalytic f g)
    (hstationary : g xStar = 0)
    (hstep : x1 = x0 - g x0)
    (hradius : inner ℝ (x0 - xStar) (x0 - xStar) ≤ 1) :
    RealizesModelQ oneStepModelQ
        (OneStepGram.oneStepData f g xStar x0 x1) ∧
      CoreFeasible (OneStepGram.oneStepData f g xStar x0 x1) ∧
      AssumptionsFeasibleR oneStepModelQ
        (OneStepGram.oneStepData f g xStar x0 x1) :=
  OneStepGram.oneStepData_feasible
    hfun hstationary hstep hradius

end LeanPEP.ActualFunction.V12A3Smoke
