import LeanPEP

open LeanPEP
open LeanPEP.ActualFunction
open LeanPEP.Profiles.GramCompilation
open LeanPEP.Profiles.Momentum
open LeanPEP.Profiles.NesterovPilot

#check ProfileGram.orderedSamples_pointIndex
#check ProfileGram.realize_standardBasisQ
#check ProfileGram.realize_affineVecQ
#check ProfileGram.realize_initialBasisQ
#check ProfileGram.realize_sampledGradientBasisQ
#check ProfileGram.RealizesProfile
#check ProfileGram.realizesProfile_iff_updates
#check ProfileGram.realizesActualSamples
#check ProfileGram.profileData_realizesModel
#check ProfileGram.profileData_interpolationSlack
#check ProfileGram.profileData_coreFeasible
#check ProfileGram.profileData_initialRadius_eval
#check ProfileGram.profileData_assumptionsFeasible
#check ProfileGram.profileData_objective_eval
#check ProfileGram.profileData_feasible
#check ProfileGram.certificate_upper
#check ProfileGram.certificate_upper_analytic
#check MomentumActual.iteratePair
#check MomentumActual.state_succ
#check MomentumActual.query_succ
#check MomentumActual.IsRun
#check MomentumActual.eq_of_isRun
#check MomentumActual.outputPoints_before_final
#check MomentumActual.outputPoints_final
#check MomentumActual.evalVector_stateAffineQ_succ
#check MomentumActual.evalVector_queryAffineQ_succ
#check MomentumActual.affineTrajectory_realization
#check MomentumActual.outputPoints_realizesProfile
#check MomentumActual.outputData_feasible
#check MomentumActual.outputData_objective_eval
#check MomentumActual.certificate_upper
#check MomentumActual.certificate_upper_analytic
#check MomentumActual.certificate_upper_of_isRun
#check NesterovPilotUpper.iterate_succ
#check NesterovPilotUpper.query_succ
#check NesterovPilotUpper.upper_firstOrder
#check NesterovPilotUpper.upper_analytic
#check NesterovPilotUpper.upper_analytic_of_isRun

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- All horizons and arbitrary rational schedules, with no smoothness assumption
-- needed for the structural trajectory theorem.
example (N : ℕ) (s : ScheduleQ) (g : E → E) (xStar x0 : E) :
    ProfileGram.RealizesProfile (outputProfileQ N s) g xStar x0
      (MomentumActual.outputPoints N s g x0) :=
  MomentumActual.outputPoints_realizesProfile N s g xStar x0

-- Explicit zero-horizon boundary case.
example (s : ScheduleQ) (g : E → E) (x0 : E) :
    MomentumActual.outputPoints 0 s g x0 (Fin.last 0) = x0 := by
  rw [MomentumActual.outputPoints_final, MomentumActual.state_zero]

-- The observation at the last index denotes state x_N, not query y_N.
example (N : ℕ) (s : ScheduleQ) (g : E → E) (x0 : E) :
    MomentumActual.outputPoints N s g x0 (Fin.last N) = MomentumActual.state s g x0 N :=
  MomentumActual.outputPoints_final N s g x0

-- First-order entry point does not require CompleteSpace.
example {f : E → ℝ} {g : E → E} {xStar x0 : E}
    (h : IsOneSmoothConvexFirstOrder f g)
    (hs : g xStar = 0) (hr : ‖x0 - xStar‖ ^ 2 ≤ 1) :
    f (NesterovPilotUpper.iterate g x0 4) - f xStar ≤ (1 : ℝ) / 21 :=
  NesterovPilotUpper.upper_firstOrder h hs hr

variable [CompleteSpace E]

-- Actual analytic assumptions discharge the finite Gram premises automatically.
example {f : E → ℝ} {g : E → E} {xStar x0 : E}
    (h : IsOneSmoothConvexAnalytic f g)
    (hs : g xStar = 0) (hr : ‖x0 - xStar‖ ^ 2 ≤ 1) :
    f (NesterovPilotUpper.iterate g x0 4) - f xStar ≤ (1 : ℝ) / 21 :=
  NesterovPilotUpper.upper_analytic h hs hr

-- External sequence definitions can use the same theorem via ordinary updates.
example {f : E → ℝ} {g : E → E} {xStar x0 : E} {x y : ℕ → E}
    (h : IsOneSmoothConvexAnalytic f g)
    (hs : g xStar = 0) (hr : ‖x0 - xStar‖ ^ 2 ≤ 1)
    (hrun : MomentumActual.IsRun 4 nesterovScheduleQ g x0 x y) :
    f (x 4) - f xStar ≤ (1 : ℝ) / 21 :=
  NesterovPilotUpper.upper_analytic_of_isRun h hs hr hrun

end

#print axioms ProfileGram.certificate_upper
#print axioms MomentumActual.affineTrajectory_realization
#print axioms NesterovPilotUpper.upper_analytic
#print axioms NesterovPilotUpper.upper_analytic_of_isRun
