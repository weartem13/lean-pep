import LeanPEP

/-! D13 interface smoke ONLY. Existing simulated regression data exercise the
same theorem calls emitted by the new runner. This is NOT a live capture proof.
The per-run Replay.lean must also be checked for the actual captured data. -/
namespace LeanPEP.Imported.D13InterfaceSmoke
open scoped NNReal

#check LeanPEP.Adapters.ProximalGradientCapture.checkCapturedRawQ
#check LeanPEP.Adapters.ProximalGradientCapture.checkCapturedQ
#check LeanPEP.Adapters.ProximalGradientCompletion.checkCompletedQ
#check LeanPEP.GramPEP.UpperCoefficientBox.checked_no_accepted_in_budget

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem raw_route_upper
    {L : ℝ≥0} {R : ℝ} {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : LeanPEP.ActualFunction.IsSmoothConvexAnalytic L f g)
    (hh : ConvexOn ℝ Set.univ h) (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar + h xStar ≤ f y + h y)
    (hrun : LeanPEP.ActualFunction.ProximalGradientScaling.IsSmoothProxRun 1 L h g x)
    (hradius : ‖x 0 - xStar‖ ^ 2 ≤ R ^ 2) :
    f (x 1) + h (x 1) - (f xStar + h xStar) ≤ (L : ℝ) * R ^ 2 *
      (LeanPEP.Imported.CompositeCapture.PGOne.rawUpperQ.bound : ℝ) :=
  LeanPEP.ActualFunction.ProximalGradientCaptureAudit.raw_upper_firstOrder
    LeanPEP.Imported.CompositeCapture.PGOne.sourceQ
    LeanPEP.Imported.CompositeCapture.PGOne.traceQ
    LeanPEP.Imported.CompositeCapture.PGOne.rawUpperQ
    LeanPEP.Imported.CompositeCapture.PGOne.raw_check
    hf.toFirstOrder hh hL hR hmin hrun hradius

theorem reconstructed_route_upper
    {L : ℝ≥0} {R : ℝ} {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : LeanPEP.ActualFunction.IsSmoothConvexAnalytic L f g)
    (hh : ConvexOn ℝ Set.univ h) (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hmin : ∀ y, f xStar + h xStar ≤ f y + h y)
    (hrun : LeanPEP.ActualFunction.ProximalGradientScaling.IsSmoothProxRun 2 L h g x)
    (hradius : ‖x 0 - xStar‖ ^ 2 ≤ R ^ 2) :
    f (x 2) + h (x 2) - (f xStar + h xStar) ≤ (L : ℝ) * R ^ 2 *
      (LeanPEP.Imported.CompositeCapture.PGTwo.reconstructedUpperQ.bound : ℝ) :=
  LeanPEP.ActualFunction.ProximalGradientCaptureAudit.upper_analytic
    LeanPEP.Imported.CompositeCapture.PGTwo.sourceQ
    LeanPEP.Imported.CompositeCapture.PGTwo.traceQ
    LeanPEP.Imported.CompositeCapture.PGTwo.policyQ
    LeanPEP.Imported.CompositeCapture.PGTwo.rawUpperQ
    LeanPEP.Imported.CompositeCapture.PGTwo.reconstructedUpperQ
    LeanPEP.Imported.CompositeCapture.PGTwo.reconstructed_check
    hf hh hL hR hmin hrun hradius

#print axioms raw_route_upper
#print axioms reconstructed_route_upper
#print axioms LeanPEP.Imported.CompiledCompletion.Budget.no_fixed_certificate_in_budget

end LeanPEP.Imported.D13InterfaceSmoke
