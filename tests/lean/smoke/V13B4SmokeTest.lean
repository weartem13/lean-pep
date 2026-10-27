import LeanPEP

open scoped NNReal
open LeanPEP LeanPEP.ActualFunction
open LeanPEP.Profiles.Momentum (ScheduleQ outputModelQ outputObjectiveQ)
open LeanPEP.Profiles.GramCompilation (unitRadiusNormalizationQ)
open LeanPEP.Profiles.NesterovPilot (nesterovScheduleQ)

#check MomentumScaling.smoothState_succ
#check MomentumScaling.smoothQuery_succ
#check MomentumScaling.IsSmoothRun
#check MomentumScaling.isSmoothRun_of_updates
#check MomentumScaling.eq_of_isSmoothRun
#check MomentumScaling.scaledPoint_sub_smul
#check MomentumScaling.scaledPoint_extrapolate
#check MomentumScaling.isRun_affine
#check MomentumScaling.affine_trajectory
#check MomentumScaling.normalizedInitial_normSq
#check MomentumScaling.normalizedInitial_radius
#check MomentumScaling.normalized_trajectory
#check MomentumScaling.stationary_trajectory
#check MomentumScaling.certificate_upper_of_pos_radius
#check MomentumScaling.certificate_upper
#check MomentumScaling.certificate_upper_exact_radius
#check MomentumScaling.certificate_upper_analytic
#check MomentumScaling.certificate_upper_of_isSmoothRun
#check NesterovPilotScaling.iterate_succ
#check NesterovPilotScaling.query_succ
#check NesterovPilotScaling.iterate_one
#check NesterovPilotScaling.query_one
#check NesterovPilotScaling.upper_firstOrder
#check NesterovPilotScaling.upper_analytic
#check NesterovPilotScaling.upper_analytic_exact_radius
#check NesterovPilotScaling.upper_analytic_of_isSmoothRun
#check HuberWitness.amplitudeScaled_analytic
#check NesterovPilotWitnessScaling.analytic
#check NesterovPilotWitnessScaling.scaledWitnessFunction_scale_point
#check NesterovPilotWitnessScaling.scaledWitnessGradient_scale_point
#check NesterovPilotWitnessScaling.scaled_trajectory
#check NesterovPilotWitnessScaling.iterate_four
#check NesterovPilotWitnessScaling.query_four
#check NesterovPilotWitnessScaling.terminal_state_ne_query
#check NesterovPilotWitnessScaling.attains
#check NesterovPilotWitnessScaling.final_query_gap
#check NesterovPilotWitnessScaling.zeroRadius_trajectory
#check NesterovPilotWitnessScaling.attains_of_isSmoothRun
#check NesterovPilotWitnessScaling.analytic_lower_witness
#check NesterovPilotWitnessScaling.oneDimensional_analytic_tight
#check NesterovPilotWitnessScaling.analytic_upper_and_oneDimensional_tight

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- No positivity is needed for purely structural affine transport.
example (s : ScheduleQ) (g g' : E → E) (center z0 : E) (R : ℝ)
    (h : ∀ z, g' (SmoothScaling.scaledPoint center R z) = R • g z) (k : ℕ) :
    MomentumActual.state s g' (SmoothScaling.scaledPoint center R z0) k =
      SmoothScaling.scaledPoint center R (MomentumActual.state s g z0 k) :=
  (MomentumScaling.affine_trajectory s g g' center R z0 h k).1

-- Zero steps and even a zero smoothness parameter are structurally defined.
-- This is NOT a convergence theorem at L=0.
example (s : ScheduleQ) (g : E → E) (x0 : E) :
    MomentumScaling.smoothState s 0 g x0 0 = x0 := rfl

-- The external-run interface is built solely from ordinary physical updates.
example {N : ℕ} {s : ScheduleQ} {L : ℝ≥0} {g : E → E}
    {x0 : E} {x y : ℕ → E}
    (hx : x 0 = x0) (hy : y 0 = x0)
    (hs : ∀ k, k < N → x (k + 1) = y k - ((s.step k : ℝ) / (L : ℝ)) • g (y k))
    (hm : ∀ k, k < N → y (k + 1) = x (k + 1) +
      (s.momentum k : ℝ) • (x (k + 1) - x k)) :
    MomentumScaling.IsSmoothRun N s L g x0 x y :=
  MomentumScaling.isSmoothRun_of_updates hx hy hs hm

-- Generic theorem: any schedule, with its OWN accepted, objective-matched certificate.
example {N : ℕ} {s : ScheduleQ}
    (c : GramPEP.UpperCertQ (outputModelQ N s unitRadiusNormalizationQ))
    (hc : GramPEP.checkUpperCertQ c = true)
    (ho : c.objective = outputObjectiveQ N s unitRadiusNormalizationQ)
    {L : ℝ≥0} {R : ℝ} {f : E → ℝ} {g : E → E} {xStar x0 : E}
    (hf : IsSmoothConvexFirstOrder L f g) (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hs : g xStar = 0) (hr : ‖x0 - xStar‖ ^ 2 ≤ R ^ 2) :
    f (MomentumScaling.smoothState s L g x0 N) - f xStar ≤
      (L : ℝ) * R ^ 2 * (c.bound : ℝ) :=
  MomentumScaling.certificate_upper c hc ho hf hL hR hs hr

example [CompleteSpace E] {L : ℝ≥0} {R : ℝ}
    {f : E → ℝ} {g : E → E} {xStar x0 : E}
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hs : g xStar = 0) (hr : ‖x0 - xStar‖ ^ 2 ≤ R ^ 2) :
    f (NesterovPilotScaling.iterate L g x0 4) - f xStar ≤ (L : ℝ) * R ^ 2 / 21 :=
  NesterovPilotScaling.upper_analytic hf hL hR hs hr

example [CompleteSpace E] {L : ℝ≥0} {R : ℝ}
    {f : E → ℝ} {g : E → E} {xStar x0 : E} {x y : ℕ → E}
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hs : g xStar = 0) (hr : ‖x0 - xStar‖ ^ 2 ≤ R ^ 2)
    (hrun : MomentumScaling.IsSmoothRun 4 nesterovScheduleQ L g x0 x y) :
    f (x 4) - f xStar ≤ (L : ℝ) * R ^ 2 / 21 :=
  NesterovPilotScaling.upper_analytic_of_isSmoothRun hf hL hR hs hr hrun

example (g : E → E) (x0 : E) (k : ℕ) :
    NesterovPilotScaling.iterate 1 g x0 k = NesterovPilotUpper.iterate g x0 k :=
  NesterovPilotScaling.iterate_one g x0 k
end

-- Positive radius and arbitrary smoothness; no finite-primal hypothesis.
example {L : ℝ≥0} {R : ℝ} (hL : 0 < (L : ℝ)) (hR : 0 ≤ R) :
    IsGreatest (NesterovPilotWitnessScaling.oneDimensionalAnalyticValues L R)
      ((L : ℝ) * R ^ 2 / 21) :=
  NesterovPilotWitnessScaling.oneDimensional_analytic_tight hL hR

-- Zero radius is part of the same actual tightness theorem.
example {L : ℝ≥0} (hL : 0 < (L : ℝ)) :
    IsGreatest (NesterovPilotWitnessScaling.oneDimensionalAnalyticValues L 0) 0 := by
  simpa using NesterovPilotWitnessScaling.oneDimensional_analytic_tight hL (le_refl (0 : ℝ))

example {L : ℝ≥0} (hL : 0 < (L : ℝ)) (k : ℕ) :
    NesterovPilotScaling.iterate L (NesterovPilotWitnessScaling.scaledWitnessGradient L 0) 0 k = 0 :=
  (NesterovPilotWitnessScaling.zeroRadius_trajectory hL k).1

-- Nonunit numeric scale: 3 * 2^2 / 21 = 4/7, proved through the general theorem.
example : NesterovPilotWitnessScaling.scaledWitnessFunction 3 2
    (NesterovPilotScaling.iterate 3 (NesterovPilotWitnessScaling.scaledWitnessGradient 3 2) 2 4) -
      NesterovPilotWitnessScaling.scaledWitnessFunction 3 2 0 = (4 : ℝ) / 7 := by
  have h := NesterovPilotWitnessScaling.attains (L := 3) (R := 2) (by norm_num) (by norm_num)
  norm_num at h ⊢ <;> exact h

example {L : ℝ≥0} {R : ℝ} (hL : 0 < (L : ℝ)) (hR : 0 < R) :
    NesterovPilotScaling.iterate L (NesterovPilotWitnessScaling.scaledWitnessGradient L R) R 4 ≠
      NesterovPilotScaling.query L (NesterovPilotWitnessScaling.scaledWitnessGradient L R) R 4 :=
  NesterovPilotWitnessScaling.terminal_state_ne_query hL hR

#print axioms MomentumScaling.affine_trajectory
#print axioms MomentumScaling.certificate_upper
#print axioms NesterovPilotScaling.upper_analytic
#print axioms NesterovPilotWitnessScaling.scaled_trajectory
#print axioms NesterovPilotWitnessScaling.attains
#print axioms NesterovPilotWitnessScaling.oneDimensional_analytic_tight
