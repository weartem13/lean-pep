import LeanPEP.ActualFunction.MomentumOracleAgreement
import LeanPEP.ActualFunction.NesterovPilotUpper
import LeanPEP.ActualFunction.HuberWitnessAnalytic

/-!
# Actual Huber attainment and tightness for the four-step Nesterov pilot

For the unchanged schedule `step(k) = 1`, `momentum(k) = k/(k+3)`, let
`a = 2/21`, `f = HuberWitness.huberFunction a`, and
`g = HuberWitness.huberGradient a`.  Starting at one, every required query
lies on the constant-gradient branch.  A reference run driven by the constant
field `a` therefore agrees with the ACTUAL Huber run through step four.
Its final state is `23/42` and its objective gap is exactly `1/21`.

Regularity, stationarity, and global minimality reuse the existing Huber
analysis.  Tightness combines this explicit actual witness with B2's universal
actual upper theorem.  It does not infer actual lower attainment from B1's
finite primal or invoke interpolation completeness.

Here `analytic` means the project's differentiability/convexity/Lipschitz-
gradient contract, not power-series analyticity.  Only the normalized FOUR-
step schedule is treated.  No arbitrary-horizon accelerated rate, general
`L,R` scaling, or cross-universe supremum is asserted.
-/

noncomputable section

namespace LeanPEP.ActualFunction.NesterovPilotWitness

open LeanPEP.Profiles.NesterovPilot (nesterovScheduleQ)

/-- The threshold of the actual four-step extremal witness. -/
def threshold : ℝ := 2 / 21

def witnessFunction : ℝ → ℝ := HuberWitness.huberFunction threshold

def witnessGradient : ℝ → ℝ := HuberWitness.huberGradient threshold

theorem threshold_pos : 0 < threshold := by
  norm_num [threshold]

/-- Full existing analysis-facing contract, not just a finite interpolation check. -/
theorem analytic : IsOneSmoothConvexAnalytic witnessFunction witnessGradient :=
  HuberWitness.analytic threshold

theorem firstOrder : IsOneSmoothConvexFirstOrder witnessFunction witnessGradient :=
  HuberWitness.firstOrder threshold

@[simp] theorem witnessFunction_zero : witnessFunction 0 = 0 :=
  HuberWitness.huberFunction_zero (le_of_lt threshold_pos)

@[simp] theorem witnessGradient_zero : witnessGradient 0 = 0 :=
  HuberWitness.huberGradient_zero (le_of_lt threshold_pos)

theorem zero_isGlobalMin (x : ℝ) : witnessFunction 0 ≤ witnessFunction x :=
  HuberWitness.zero_isGlobalMin (le_of_lt threshold_pos) x

/-- Reference state driven by the constant field.  This is only an auxiliary
trajectory; the constant field is not asserted to have a stationary minimizer. -/
def referenceState (k : ℕ) : ℝ :=
  MomentumActual.state nesterovScheduleQ (fun _ : ℝ => threshold) 1 k

/-- Reference query driven by the same auxiliary constant field. -/
def referenceQuery (k : ℕ) : ℝ :=
  MomentumActual.query nesterovScheduleQ (fun _ : ℝ => threshold) 1 k

/-- Exact state values of the reference recursion, including the initial point. -/
theorem reference_state_values :
    referenceState 0 = 1 ∧
      referenceState 1 = 19 / 21 ∧
      referenceState 2 = 17 / 21 ∧
      referenceState 3 = 29 / 42 ∧
      referenceState 4 = 23 / 42 := by
  norm_num [referenceState, MomentumActual.state, MomentumActual.iteratePair,
    nesterovScheduleQ, threshold, smul_eq_mul]

/-- The unused final query is `10/21`, not the output state `23/42`. -/
theorem reference_query_values :
    referenceQuery 0 = 1 ∧
      referenceQuery 1 = 19 / 21 ∧
      referenceQuery 2 = 11 / 14 ∧
      referenceQuery 3 = 9 / 14 ∧
      referenceQuery 4 = 10 / 21 := by
  norm_num [referenceQuery, MomentumActual.query, MomentumActual.iteratePair,
    nesterovScheduleQ, threshold, smul_eq_mul]

/-- Every required query lies on the constant-gradient branch.  The stronger
endpoint-inclusive statement is convenient, but only `k < 4` drives updates. -/
theorem threshold_le_referenceQuery (k : ℕ) (hk : k ≤ 4) :
    threshold ≤ referenceQuery k := by
  interval_cases k <;>
    norm_num [referenceQuery, MomentumActual.query, MomentumActual.iteratePair,
      nesterovScheduleQ, threshold, smul_eq_mul]

theorem gradient_referenceQuery (k : ℕ) (hk : k ≤ 4) :
    witnessGradient (referenceQuery k) = threshold :=
  HuberWitness.huberGradient_of_ge (threshold_le_referenceQuery k hk)

/-- Identification of BOTH actual sequences with the auxiliary reference run.
No gradient value at a state is substituted for an oracle call at a query. -/
theorem actual_trajectory (k : ℕ) (hk : k ≤ 4) :
    NesterovPilotUpper.iterate witnessGradient 1 k = referenceState k ∧
      NesterovPilotUpper.query witnessGradient 1 k = referenceQuery k := by
  have hqueries : ∀ j, j < 4 →
      witnessGradient (MomentumActual.query nesterovScheduleQ
        (fun _ : ℝ => threshold) 1 j) = threshold := by
    intro j hj
    exact gradient_referenceQuery j (Nat.le_of_lt hj)
  exact MomentumActual.eq_of_oracle_eq_on_queries
    4 nesterovScheduleQ (fun _ : ℝ => threshold) witnessGradient 1 hqueries k hk

/-- Final state of the actual Huber-gradient run. -/
theorem iterate_four :
    NesterovPilotUpper.iterate witnessGradient 1 4 = (23 : ℝ) / 42 := by
  rw [(actual_trajectory 4 (le_refl 4)).1]
  exact reference_state_values.2.2.2.2

theorem query_four :
    NesterovPilotUpper.query witnessGradient 1 4 = (10 : ℝ) / 21 := by
  rw [(actual_trajectory 4 (le_refl 4)).2]
  exact reference_query_values.2.2.2.2

/-- Explicitly rule out confusing the output state with the final extrapolation. -/
theorem terminal_state_ne_query :
    NesterovPilotUpper.iterate witnessGradient 1 4 ≠
      NesterovPilotUpper.query witnessGradient 1 4 := by
  rw [iterate_four, query_four]
  norm_num

/-- The explicit actual function attains the same normalized bound as the
unchanged B1 certificate and the B2 actual upper theorem. -/
theorem attains :
    witnessFunction (NesterovPilotUpper.iterate witnessGradient 1 4) -
      witnessFunction 0 = (1 : ℝ) / 21 := by
  rw [iterate_four, witnessFunction_zero]
  norm_num [witnessFunction, HuberWitness.huberFunction, threshold]

/-- A distinct exact value for the unused query makes the endpoint distinction
observable at the objective level as well. -/
theorem final_query_gap :
    witnessFunction (NesterovPilotUpper.query witnessGradient 1 4) -
      witnessFunction 0 = (2 : ℝ) / 49 := by
  rw [query_four, witnessFunction_zero]
  norm_num [witnessFunction, HuberWitness.huberFunction, threshold]

/-- The same attainment statement for any external implementation satisfying
B2's ordinary two-sequence run equations. -/
theorem attains_of_isRun {x y : ℕ → ℝ}
    (hrun : MomentumActual.IsRun 4 nesterovScheduleQ witnessGradient 1 x y) :
    witnessFunction (x 4) - witnessFunction 0 = (1 : ℝ) / 21 := by
  rw [(MomentumActual.eq_of_isRun hrun 4 (le_refl 4)).1]
  exact attains

/-- All actual lower-witness obligations, including genuine analytic regularity
and global minimality, assembled independently of finite primal feasibility. -/
theorem normalized_analytic_lower_witness :
    IsOneSmoothConvexAnalytic witnessFunction witnessGradient ∧
      witnessGradient 0 = 0 ∧
      (∀ x : ℝ, witnessFunction 0 ≤ witnessFunction x) ∧
      ‖(1 : ℝ) - 0‖ ^ 2 ≤ 1 ∧
      witnessFunction (NesterovPilotUpper.iterate witnessGradient 1 4) -
        witnessFunction 0 = (1 : ℝ) / 21 := by
  refine ⟨analytic, witnessGradient_zero, zero_isGlobalMin, ?_, attains⟩
  norm_num

/-- Values of genuine one-dimensional normalized smooth-convex instances,
executing the actual four-step recurrence, not the finite Gram relaxation. -/
def oneDimensionalAnalyticValues : Set ℝ :=
  { value | ∃ (f g : ℝ → ℝ) (xStar x0 : ℝ),
      IsOneSmoothConvexAnalytic f g ∧
      g xStar = 0 ∧
      ‖x0 - xStar‖ ^ 2 ≤ 1 ∧
      f (NesterovPilotUpper.iterate g x0 4) - f xStar = value }

theorem bound_mem_oneDimensionalAnalyticValues :
    (1 : ℝ) / 21 ∈ oneDimensionalAnalyticValues := by
  refine ⟨witnessFunction, witnessGradient, 0, 1,
    analytic, witnessGradient_zero, ?_, attains⟩
  norm_num

/-- Exact one-dimensional ACTUAL-function worst-case value. -/
theorem oneDimensional_analytic_tight :
    IsGreatest oneDimensionalAnalyticValues ((1 : ℝ) / 21) := by
  constructor
  · exact bound_mem_oneDimensionalAnalyticValues
  · intro value hvalue
    rcases hvalue with ⟨f, g, xStar, x0, hfun, hstationary, hradius, hattain⟩
    rw [← hattain]
    exact NesterovPilotUpper.upper_analytic hfun hstationary hradius

/-- Universal upper bound in an arbitrary real Hilbert space, together with
one-dimensional actual attainment.  No cross-universe supremum is defined. -/
theorem analytic_upper_and_oneDimensional_tight
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    (∀ {f : E → ℝ} {g : E → E} {xStar x0 : E},
      IsOneSmoothConvexAnalytic f g →
      g xStar = 0 →
      ‖x0 - xStar‖ ^ 2 ≤ 1 →
      f (NesterovPilotUpper.iterate g x0 4) - f xStar ≤ (1 : ℝ) / 21) ∧
      IsGreatest oneDimensionalAnalyticValues ((1 : ℝ) / 21) := by
  constructor
  · intro f g xStar x0 hfun hstationary hradius
    exact NesterovPilotUpper.upper_analytic hfun hstationary hradius
  · exact oneDimensional_analytic_tight

end LeanPEP.ActualFunction.NesterovPilotWitness
