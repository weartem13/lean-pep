import LeanPEP

open LeanPEP
open LeanPEP.ActualFunction
open LeanPEP.Profiles.Momentum
open LeanPEP.Profiles.NesterovPilot (nesterovScheduleQ)

#check MomentumActual.isRun_of_oracle_eq_on_queries
#check MomentumActual.eq_of_oracle_eq_on_queries
#check MomentumActual.outputPoints_eq_of_oracle_eq_on_queries
#check NesterovPilotWitness.threshold_pos
#check NesterovPilotWitness.analytic
#check NesterovPilotWitness.firstOrder
#check NesterovPilotWitness.witnessFunction_zero
#check NesterovPilotWitness.witnessGradient_zero
#check NesterovPilotWitness.zero_isGlobalMin
#check NesterovPilotWitness.reference_state_values
#check NesterovPilotWitness.reference_query_values
#check NesterovPilotWitness.threshold_le_referenceQuery
#check NesterovPilotWitness.gradient_referenceQuery
#check NesterovPilotWitness.actual_trajectory
#check NesterovPilotWitness.iterate_four
#check NesterovPilotWitness.query_four
#check NesterovPilotWitness.terminal_state_ne_query
#check NesterovPilotWitness.attains
#check NesterovPilotWitness.final_query_gap
#check NesterovPilotWitness.attains_of_isRun
#check NesterovPilotWitness.normalized_analytic_lower_witness
#check NesterovPilotWitness.oneDimensionalAnalyticValues
#check NesterovPilotWitness.bound_mem_oneDimensionalAnalyticValues
#check NesterovPilotWitness.oneDimensional_analytic_tight
#check NesterovPilotWitness.analytic_upper_and_oneDimensional_tight

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- Structural lemma: arbitrary schedule, arbitrary oracles, no function class.
example (N : ℕ) (s : ScheduleQ) (g g' : E → E) (x0 : E)
    (hqueries : ∀ k, k < N →
      g' (MomentumActual.query s g x0 k) = g (MomentumActual.query s g x0 k)) :
    MomentumActual.state s g' x0 N = MomentumActual.state s g x0 N :=
  (MomentumActual.eq_of_oracle_eq_on_queries N s g g' x0 hqueries N (le_refl N)).1

-- Zero steps require no oracle agreement anywhere.
example (s : ScheduleQ) (g g' : E → E) (x0 : E) :
    MomentumActual.state s g' x0 0 = MomentumActual.state s g x0 0 ∧
      MomentumActual.query s g' x0 0 = MomentumActual.query s g x0 0 :=
  MomentumActual.eq_of_oracle_eq_on_queries 0 s g g' x0
    (by intro k hk; omega) 0 (le_refl 0)

-- The universal actual-function upper theorem is unchanged by the lower witness.
example [CompleteSpace E] {f : E → ℝ} {g : E → E} {xStar x0 : E}
    (hfun : IsOneSmoothConvexAnalytic f g)
    (hs : g xStar = 0) (hr : ‖x0 - xStar‖ ^ 2 ≤ 1) :
    f (NesterovPilotUpper.iterate g x0 4) - f xStar ≤ (1 : ℝ) / 21 :=
  NesterovPilotUpper.upper_analytic hfun hs hr
end

-- Genuine function-class membership and actual attainment, not finite feasibility.
example : IsOneSmoothConvexAnalytic
    NesterovPilotWitness.witnessFunction NesterovPilotWitness.witnessGradient :=
  NesterovPilotWitness.analytic

example : NesterovPilotWitness.witnessFunction
    (NesterovPilotUpper.iterate NesterovPilotWitness.witnessGradient 1 4) -
      NesterovPilotWitness.witnessFunction 0 = (1 : ℝ) / 21 :=
  NesterovPilotWitness.attains

example {x y : ℕ → ℝ}
    (h : MomentumActual.IsRun 4 nesterovScheduleQ
      NesterovPilotWitness.witnessGradient 1 x y) :
    NesterovPilotWitness.witnessFunction (x 4) -
      NesterovPilotWitness.witnessFunction 0 = (1 : ℝ) / 21 :=
  NesterovPilotWitness.attains_of_isRun h

example : IsGreatest NesterovPilotWitness.oneDimensionalAnalyticValues ((1 : ℝ) / 21) :=
  NesterovPilotWitness.oneDimensional_analytic_tight

-- This explicitly distinguishes the unused final query from the output state.
example : NesterovPilotUpper.iterate NesterovPilotWitness.witnessGradient 1 4 ≠
    NesterovPilotUpper.query NesterovPilotWitness.witnessGradient 1 4 :=
  NesterovPilotWitness.terminal_state_ne_query

#print axioms MomentumActual.eq_of_oracle_eq_on_queries
#print axioms NesterovPilotWitness.actual_trajectory
#print axioms NesterovPilotWitness.attains
#print axioms NesterovPilotWitness.oneDimensional_analytic_tight
#print axioms NesterovPilotWitness.analytic_upper_and_oneDimensional_tight
