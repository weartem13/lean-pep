import LeanPEP.Profiles.Momentum
import LeanPEP.GramPEP.ExternalBundle

/-!
# Rational Nesterov momentum pilot in the unchanged Gram core

Use unit steps and momentum `k / (k + 3)`, for zero-based `k`.  This is the
rational simplified fast-gradient schedule, not the square-root FISTA schedule.

The four-step model has sample order `(star, y_0, y_1, y_2, y_3, x_4)` and
basis `(x_0-star, g(y_0), g(y_1), g(y_2), g(y_3), g(x_4))`.
Only the first four gradients drive updates.  The terminal gradient is used
only in smooth-convex interpolation.  In particular

```
y_3 - y_2 = -(1/10) g_1 - (7/5) g_2.
```

Thus this pilot exercises genuine historical-gradient mixing.  The bound
`1/21` and a matching exact rank-one finite primal are checked by the EXISTING
general Gram checkers.  The final `IsGreatest` is for the finite real Gram
formulation; this module does not assert a generic actual-function bridge,
interpolation completeness, or an arbitrary-horizon accelerated rate.
-/

namespace LeanPEP.Profiles.NesterovPilot

open LeanPEP.Profiles.Momentum
open LeanPEP.Profiles.GramCompilation
open LeanPEP.GramPEP

/-- Rational simplified fast-gradient schedule (zero-based step index). -/
def nesterovScheduleQ : ScheduleQ :=
  { step := fun _ => 1
    momentum := fun k => (k : ℚ) / ((k : ℚ) + 3) }

/-- Every horizon uses the same verified profile/compiler interface. -/
def nesterovModelQ (N : ℕ) : ModelQ (N + 2) (N + 2) :=
  outputModelQ N nesterovScheduleQ unitRadiusNormalizationQ

/-- Objective at the final state `x_N`, not at the extrapolated query `y_N`. -/
def nesterovObjectiveQ (N : ℕ) : LinearExprQ (N + 2) (N + 2) :=
  outputObjectiveQ N nesterovScheduleQ unitRadiusNormalizationQ

/-- Four-step compiler-generated model. -/
def pilotModelQ : ModelQ 6 6 := nesterovModelQ 4

/-- Four-step terminal-state gap. -/
def pilotObjectiveQ : LinearExprQ 6 6 := nesterovObjectiveQ 4

/-- The full position array is an equality about the compiler output, not a
second hand-written model used in place of that output. -/
theorem pilot_positions :
    pilotModelQ.position = ![
      ![(0 : ℚ), 0, 0, 0, 0, 0],
      ![(1 : ℚ), 0, 0, 0, 0, 0],
      ![(1 : ℚ), -1, 0, 0, 0, 0],
      ![(1 : ℚ), -1, -(5/4), 0, 0, 0],
      ![(1 : ℚ), -1, -(27/20), -(7/5), 0, 0],
      ![(1 : ℚ), -1, -(27/20), -(7/5), -1, 0]] := by
  funext i
  apply (checkVecExprEqQ_eq_true_iff _ _).mp
  fin_cases i <;> decide +kernel

/-- The first nontrivial momentum mix contains an older oracle answer. -/
theorem pilot_historical_gradient_mix :
    pilotModelQ.position 4 - pilotModelQ.position 3 =
      ![(0 : ℚ), 0, -(1/10), -(7/5), 0, 0] := by
  apply (checkVecExprEqQ_eq_true_iff _ _).mp
  decide +kernel

/-- The state and unused extrapolated query at the final iteration differ. -/
theorem pilot_terminal_state_not_query :
    stateCoeffQ nesterovScheduleQ 4 3 ≠ queryCoeffQ nesterovScheduleQ 4 3 := by
  decide +kernel

/-- No iterate uses the terminal gradient observation. -/
theorem pilot_terminal_gradient_unused (i : Fin 5) :
    pilotModelQ.position (pointIndex (LeanPEP.Toy.FiniteGD.Point.iter i))
      (gradientBasisIndex (Fin.last 4)) = 0 :=
  outputModelQ_terminal_gradient_unused nesterovScheduleQ unitRadiusNormalizationQ i

/-- The five star weights sum to one; the four forward-chain weights supply
exact value-coefficient cancellation. -/
def pilotInterpTermsQ : List (InterpTermQ 6) :=
  [ { weight := 2/19, i := 0, j := 1 }
  , { weight := 553/3230, i := 0, j := 2 }
  , { weight := 1187/4930, i := 0, j := 3 }
  , { weight := 206/667, i := 0, j := 4 }
  , { weight := 4/23, i := 0, j := 5 }
  , { weight := 2/19, i := 1, j := 2 }
  , { weight := 47/170, i := 2, j := 3 }
  , { weight := 15/29, i := 3, j := 4 }
  , { weight := 19/23, i := 4, j := 5 } ]

/-- One centering square and ten gradient-difference squares.  All weights
are exact positive rationals; no floating-point eigendecomposition is used. -/
def pilotDualFactorsQ : List (RankOneFactorQ 6) :=
  [ { weight := 1/21,
      vector := ![1, -(21/19), -(11613/6460), -(24927/9860), -(2163/667), -(42/23)] }
  , { weight := 553/61370, vector := ![0, 1, -1, 0, 0, 0] }
  , { weight := 1187/93670, vector := ![0, 1, 0, -1, 0, 0] }
  , { weight := 206/12673, vector := ![0, 1, 0, 0, -1, 0] }
  , { weight := 4/437, vector := ![0, 1, 0, 0, 0, -1] }
  , { weight := 68909/2196400, vector := ![0, 0, 1, -1, 0, 0] }
  , { weight := 6429/148580, vector := ![0, 0, 1, 0, -1, 0] }
  , { weight := 1446/37145, vector := ![0, 0, 1, 0, 0, -1] }
  , { weight := 465329/6576620, vector := ![0, 0, 0, 1, -1, 0] }
  , { weight := 11123/113390, vector := ![0, 0, 0, 1, 0, -1] }
  , { weight := 2992/15341, vector := ![0, 0, 0, 0, 1, -1] } ]

/-- Exact dual PSD matrix, reconstructed using the shared factor semantics. -/
def pilotDualMatrixQ : Gram 6 ℚ := factorGramQ pilotDualFactorsQ

/-- The compiled normalization has exactly one assumption. -/
def pilotRadiusIndex : Fin pilotModelQ.assumptions.length :=
  ⟨0, by decide +kernel⟩

/-- Exact certificate submitted directly to the unchanged general checker. -/
def pilotUpperCertQ : UpperCertQ pilotModelQ :=
  { bound := 1/21
    objective := pilotObjectiveQ
    interpTerms := pilotInterpTermsQ
    assumptionTerms := [{ weight := 1/21, index := pilotRadiusIndex }]
    dualMatrix := pilotDualMatrixQ
    dualFactor := { factors := pilotDualFactorsQ } }

/-- Closed exact computation, checked by Lean's ordinary kernel reduction. -/
theorem pilotUpperCertQ_check : checkUpperCertQ pilotUpperCertQ = true := by
  decide +kernel

/-- Proposition-level certificate validity through the existing checker. -/
theorem pilotUpperCertQ_valid : UpperCertValidQ pilotUpperCertQ :=
  checkUpperCertQ_sound pilotUpperCertQ pilotUpperCertQ_check

/-- The full expression identity, including the radius inequality multiplier. -/
theorem pilot_certificate_identity :
    certificateRhsExprQ pilotUpperCertQ =
      upperTargetExprQ (1/21) pilotObjectiveQ :=
  pilotUpperCertQ_valid.identity

@[simp] theorem pilotObjectiveQ_evalR (d : DataR (Fin 6) 6) :
    pilotObjectiveQ.evalR d = d.value 5 - d.value 0 := by
  exact outputObjectiveQ_evalR nesterovScheduleQ unitRadiusNormalizationQ d

/-- Universal upper theorem for this finite real Gram formulation. -/
theorem pilot_upper (d : DataR (Fin 6) 6)
    (hrealizes : RealizesModelQ pilotModelQ d)
    (hcore : CoreFeasible d)
    (hassumptions : AssumptionsFeasibleR pilotModelQ d) :
    pilotObjectiveQ.evalR d ≤ (1 : ℝ) / 21 := by
  simpa [pilotUpperCertQ] using
    checkUpperCertQ_sound_real pilotUpperCertQ pilotUpperCertQ_check
      d hrealizes hcore hassumptions

/-- Rank-one primal basis values.  The initial displacement is one and every
sampled gradient is `2/21`. -/
def pilotPrimalFactorQ : PSDFactorCertQ 6 :=
  { factors := [{ weight := 1, vector := ![1, 2/21, 2/21, 2/21, 2/21, 2/21] }] }

/-- Exact sampled values match `a*x - a^2/2`, with `a=2/21`, at every
non-star point.  These are finite data, not an asserted analytic interpolant. -/
def pilotPrimalQ : DataQ (Fin 6) 6 :=
  { gram := factorGramQ pilotPrimalFactorQ.factors
    position := pilotModelQ.position
    gradient := pilotModelQ.gradient
    value := ![0, 40/441, 4/49, 31/441, 25/441, 1/21] }

theorem pilotPrimalQ_realizes : RealizesModelExactQ pilotModelQ pilotPrimalQ :=
  ⟨fun _ => rfl, fun _ => rfl⟩

theorem pilotPrimalQ_psd_check :
    checkPSDFactorQ pilotPrimalQ.gram pilotPrimalFactorQ = true := by
  decide +kernel

/-- Every one of the 36 ordered interpolation constraints is checked. -/
theorem pilotPrimalQ_interpolation_check :
    checkInterpolationFeasibleQ pilotPrimalQ = true := by
  decide +kernel

theorem pilotPrimalQ_assumptions_check :
    checkAssumptionsFeasibleQ pilotModelQ pilotPrimalQ = true := by
  decide +kernel

/-- Exact objective attainment, not a numerical approximation. -/
theorem pilotPrimalQ_value :
    pilotObjectiveQ.evalQ pilotPrimalQ = (1 : ℚ) / 21 := by
  decide +kernel

/-- The existing rational-to-real bridges supply real primal feasibility. -/
theorem pilotPrimalQ_feasible_real :
    RealizesModelQ pilotModelQ (castDataQ pilotPrimalQ) ∧
      CoreFeasible (castDataQ pilotPrimalQ) ∧
      AssumptionsFeasibleR pilotModelQ (castDataQ pilotPrimalQ) := by
  refine ⟨realizesModelExactQ_toReal pilotPrimalQ_realizes, ?_, ?_⟩
  · exact ⟨checkPSDFactorQ_sound_real _ _ pilotPrimalQ_psd_check,
      interpolationFeasibleQ_toReal pilotPrimalQ
        ((checkInterpolationFeasibleQ_eq_true_iff _).mp
          pilotPrimalQ_interpolation_check)⟩
  · exact assumptionsFeasibleQ_toReal pilotModelQ pilotPrimalQ
      ((checkAssumptionsFeasibleQ_eq_true_iff _ _).mp
        pilotPrimalQ_assumptions_check)

/-- The real cast of the exact primal attains the certified value. -/
theorem pilotPrimalQ_value_real :
    pilotObjectiveQ.evalR (castDataQ pilotPrimalQ) = (1 : ℝ) / 21 := by
  rw [LinearExprQ.evalR_castDataQ, pilotPrimalQ_value]
  norm_num

/-- Attainable objective values in the finite real Gram formulation. -/
def pilotFiniteValues : Set ℝ :=
  {r | ∃ d : DataR (Fin 6) 6,
    RealizesModelQ pilotModelQ d ∧ CoreFeasible d ∧
      AssumptionsFeasibleR pilotModelQ d ∧ pilotObjectiveQ.evalR d = r}

/-- Matching primal and dual close the finite PEP exactly at `1/21`.
This is deliberately not an actual-function or arbitrary-horizon claim. -/
theorem pilot_finite_tight : IsGreatest pilotFiniteValues ((1 : ℝ) / 21) := by
  constructor
  · exact ⟨castDataQ pilotPrimalQ, pilotPrimalQ_feasible_real.1,
      pilotPrimalQ_feasible_real.2.1, pilotPrimalQ_feasible_real.2.2,
      pilotPrimalQ_value_real⟩
  · intro r hr
    rcases hr with ⟨d, hrealizes, hcore, hassumptions, hvalue⟩
    rw [← hvalue]
    exact pilot_upper d hrealizes hcore hassumptions

/-! ## Exact rejection regressions

A rejected certificate is not a proof that its claimed bound is false.
These mutations test certificate identity, sign, factorization, and objective
routing, independently of any floating-point tolerance.
-/

def wrongBoundCertQ : UpperCertQ pilotModelQ :=
  { pilotUpperCertQ with bound := 1/20 }

def wrongObjectiveCertQ : UpperCertQ pilotModelQ :=
  { pilotUpperCertQ with
    objective := LinearExprQ.sub (LinearExprQ.valueVar 4) (LinearExprQ.valueVar 0) }

def negativeInterpCertQ : UpperCertQ pilotModelQ :=
  { pilotUpperCertQ with interpTerms := [{ weight := -1, i := 0, j := 1 }] }

def missingDualFactorsCertQ : UpperCertQ pilotModelQ :=
  { pilotUpperCertQ with dualFactor := { factors := [] } }

theorem wrongBoundCertQ_rejected : checkUpperCertQ wrongBoundCertQ = false := by
  decide +kernel

theorem wrongObjectiveCertQ_rejected : checkUpperCertQ wrongObjectiveCertQ = false := by
  decide +kernel

theorem negativeInterpCertQ_rejected : checkUpperCertQ negativeInterpCertQ = false := by
  decide +kernel

theorem missingDualFactorsCertQ_rejected :
    checkUpperCertQ missingDualFactorsCertQ = false := by
  decide +kernel

end LeanPEP.Profiles.NesterovPilot
