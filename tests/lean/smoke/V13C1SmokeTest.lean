import LeanPEP

open LeanPEP
open LeanPEP.ActualFunction

#check GramPEP.checkUpperCertQ_sound_real_explicit
#check Profiles.Composite.FunctionClassQ
#check Profiles.Composite.SampleQ
#check Profiles.Composite.ComponentQ
#check Profiles.Composite.ProfileQ
#check Profiles.Composite.compileModelQ
#check Profiles.Composite.evalR_interpolationExprQ_convex
#check Profiles.Composite.evalR_interpolationExprQ_smooth
#check Profiles.Composite.compileModelQ_feasible
#check Profiles.Composite.certificate_upper
#check Proximal.SubgradientAt
#check Proximal.IsUnitProxPoint
#check Proximal.isUnitProxPoint_iff_norm
#check Proximal.isUnitProxPoint_iff_subgradient
#check Proximal.forwardBackwardStep_of_prox
#check Proximal.IsUnitForwardBackwardStep.prox
#check Proximal.composite_globalMin
#check Composite.eval_convex
#check Composite.eval_smooth
#check Composite.convex_pair_nonneg
#check Composite.smooth_pair_nonneg
#check Profiles.ProximalGradientOneStep.modelQ_constraints
#check Profiles.ProximalGradientOneStep.upperCertQ_check
#check Profiles.ProximalGradientOneStep.certificate_identity
#check Profiles.ProximalGradientOneStep.primalQ_constraints_check
#check Profiles.ProximalGradientOneStep.primalQ_implicit_interpolation_rejected
#check Profiles.ProximalGradientOneStep.finite_tight
#check ProximalGradientOneStep.smoothSamples_denote
#check ProximalGradientOneStep.nonsmoothSamples_denote
#check ProximalGradientOneStep.actualData_constraints
#check ProximalGradientOneStep.upper_firstOrder
#check ProximalGradientOneStep.upper_of_prox
#check ProximalGradientOneStep.upper_analytic
#check ProximalGradientOneStepWitness.actual_prox
#check ProximalGradientOneStepWitness.attains
#check ProximalGradientOneStepWitness.smooth_gradient_at_star_ne_zero
#check ProximalGradientOneStepWitness.oneDimensional_analytic_tight
#check ProximalGradientOneStepWitness.analytic_upper_and_oneDimensional_tight

example : GramPEP.checkUpperCertQ Profiles.ProximalGradientOneStep.upperCertQ = true :=
  Profiles.ProximalGradientOneStep.upperCertQ_check

example : GramPEP.checkUpperCertQ Profiles.ProximalGradientOneStep.wrongObjectiveQ = false :=
  Profiles.ProximalGradientOneStep.wrongObjectiveQ_rejected

example : GramPEP.checkUpperCertQ Profiles.ProximalGradientOneStep.wrongBoundQ = false :=
  Profiles.ProximalGradientOneStep.wrongBoundQ_rejected

example : Profiles.ProximalGradientOneStep.modelQ.assumptions.length = 14 :=
  Profiles.ProximalGradientOneStep.modelQ_constraint_count

-- The old implicit all-slot smooth model is intentionally not used.
example : GramPEP.checkInterpolationFeasibleQ Profiles.ProximalGradientOneStep.primalQ = false :=
  Profiles.ProximalGradientOneStep.primalQ_implicit_interpolation_rejected

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {h : E → ℝ} {v x : E} (hh : ConvexOn ℝ Set.univ h) :
    Proximal.IsUnitProxPoint h v x ↔ Proximal.SubgradientAt h (v - x) x :=
  Proximal.isUnitProxPoint_iff_subgradient hh

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f h : E → ℝ} {g : E → E} {xStar x0 x1 : E}
    (hf : IsOneSmoothConvexAnalytic f g) (hh : ConvexOn ℝ Set.univ h)
    (hs : Proximal.SubgradientAt h (-g xStar) xStar)
    (hp : Proximal.IsUnitProxPoint h (x0 - g x0) x1)
    (hradius : ‖x0 - xStar‖ ^ 2 ≤ 1) :
    (f x1 + h x1) - (f xStar + h xStar) ≤ (1 : ℝ) / 4 :=
  ProximalGradientOneStep.upper_analytic hf hh hs hp hradius

example : IsGreatest Profiles.ProximalGradientOneStep.finiteValues ((1 : ℝ) / 4) :=
  Profiles.ProximalGradientOneStep.finite_tight

example : IsGreatest ProximalGradientOneStepWitness.oneDimensionalAnalyticValues ((1 : ℝ) / 4) :=
  ProximalGradientOneStepWitness.oneDimensional_analytic_tight

#print axioms GramPEP.checkUpperCertQ_sound_real_explicit
#print axioms Proximal.isUnitProxPoint_iff_subgradient
#print axioms Profiles.ProximalGradientOneStep.upperCertQ_check
#print axioms ProximalGradientOneStep.actualData_constraints
#print axioms ProximalGradientOneStep.upper_analytic
#print axioms ProximalGradientOneStepWitness.oneDimensional_analytic_tight
