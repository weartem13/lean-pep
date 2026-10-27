import LeanPEP.Profiles.Composite
import LeanPEP.GramPEP.ExternalBundle

/-!
# One-step proximal-gradient composite certificate

Normalized `L = 1`, step `1`, initial squared radius at most `1`.
Value order: `(f_star, f_0, f_1, h_star, h_1)`.
Gram basis: `(x_0-x_star, g_star, g_0, g_1, s_1)`.
Update: `x_1 = x_0 - g_0 - s_1`. Composite stationarity is
`s_star = -g_star`, NOT `g_star = 0` and NOT `s_star = 0`.

There are 9 smooth pairs, 4 nonsmooth pairs, and 1 radius inequality.
The exact bound is `1/4`. Every nonzero coefficient is rational.
-/

namespace LeanPEP.Profiles.ProximalGradientOneStep

open LeanPEP.GramPEP

/-- Positions and oracle vectors share one five-dimensional coefficient basis. -/
def initialVecQ : VecExpr 5 ℚ := ![1, 0, 0, 0, 0]
def starGradientQ : VecExpr 5 ℚ := ![0, 1, 0, 0, 0]
def initialGradientQ : VecExpr 5 ℚ := ![0, 0, 1, 0, 0]
def finalGradientQ : VecExpr 5 ℚ := ![0, 0, 0, 1, 0]
def finalSubgradientQ : VecExpr 5 ℚ := ![0, 0, 0, 0, 1]

def finalVecQ : VecExpr 5 ℚ := initialVecQ - initialGradientQ - finalSubgradientQ

def smoothSamplesQ : Fin 3 → Composite.SampleQ 5 5 :=
  ![{ valueIndex := 0, position := 0, oracle := starGradientQ },
    { valueIndex := 1, position := initialVecQ, oracle := initialGradientQ },
    { valueIndex := 2, position := finalVecQ, oracle := finalGradientQ }]

def nonsmoothSamplesQ : Fin 2 → Composite.SampleQ 5 5 :=
  ![{ valueIndex := 3, position := 0, oracle := -starGradientQ },
    { valueIndex := 4, position := finalVecQ, oracle := finalSubgradientQ }]

def smoothComponentQ : Composite.ComponentQ 5 5 :=
  { functionClass := .oneSmoothConvex
    samples := (List.finRange 3).map smoothSamplesQ }

def nonsmoothComponentQ : Composite.ComponentQ 5 5 :=
  { functionClass := .convex
    samples := (List.finRange 2).map nonsmoothSamplesQ }

def radiusExprQ : LinearExprQ 5 5 :=
  LinearExprQ.sub (LinearExprQ.const 5 5 1) (LinearExprQ.gramNorm initialVecQ)

def objectiveQ : LinearExprQ 5 5 :=
  LinearExprQ.sub
    (LinearExprQ.add (LinearExprQ.valueVar 2) (LinearExprQ.valueVar 4))
    (LinearExprQ.add (LinearExprQ.valueVar 0) (LinearExprQ.valueVar 3))

def profileQ : Composite.ProfileQ 5 5 :=
  { components := [smoothComponentQ, nonsmoothComponentQ]
    assumptions := [radiusExprQ]
    objective := objectiveQ }

def modelQ : ModelQ 5 5 := Composite.compileModelQ profileQ

@[simp] theorem modelQ_constraint_count : modelQ.assumptions.length = 14 := by
  decide +kernel

/-- This is a compiler-output identity, not an alternative model. -/
theorem modelQ_constraints : modelQ.assumptions =
    ((List.finRange 3).flatMap fun i => (List.finRange 3).map fun j =>
      Composite.interpolationExprQ .oneSmoothConvex (smoothSamplesQ i) (smoothSamplesQ j)) ++
    ((List.finRange 2).flatMap fun i => (List.finRange 2).map fun j =>
      Composite.interpolationExprQ .convex (nonsmoothSamplesQ i) (nonsmoothSamplesQ j)) ++
    [radiusExprQ] := by
  rfl

/-- Three exact positive weighted squares. The dual matrix is singular. -/
def dualFactorsQ : List (RankOneFactorQ 5) :=
  [ { weight := 1/4, vector := ![1, 0, -1, -1, -2] }
  , { weight := 1/2, vector := ![0, 1, -(1/2), -(1/2), 0] }
  , { weight := 1/8, vector := ![0, 0, 1, -1, 0] } ]

def upperCertQ : UpperCertQ modelQ :=
  { bound := 1/4
    objective := objectiveQ
    interpTerms := []
    assumptionTerms :=
      [ { weight := 1/2, index := ⟨1, by decide +kernel⟩ }
      , { weight := 1/2, index := ⟨5, by decide +kernel⟩ }
      , { weight := 1/2, index := ⟨2, by decide +kernel⟩ }
      , { weight := 1, index := ⟨10, by decide +kernel⟩ }
      , { weight := 1/4, index := ⟨13, by decide +kernel⟩ } ]
    dualMatrix := factorGramQ dualFactorsQ
    dualFactor := { factors := dualFactorsQ } }

theorem upperCertQ_check : checkUpperCertQ upperCertQ = true := by
  decide +kernel

theorem upperCertQ_valid : UpperCertValidQ upperCertQ :=
  checkUpperCertQ_sound upperCertQ upperCertQ_check

theorem certificate_identity : certificateRhsExprQ upperCertQ =
    upperTargetExprQ (1/4) objectiveQ := upperCertQ_valid.identity

@[simp] theorem objectiveQ_evalR (d : DataR (Fin 5) 5) :
    objectiveQ.evalR d = (d.value 2 + d.value 4) - (d.value 0 + d.value 3) := by
  simp [objectiveQ]

/-- No single-function `CoreFeasible` assumption is appropriate here. -/
theorem upper (d : DataR (Fin 5) 5) (hpsd : IsGramPosSemidef d.gram)
    (hconstraints : AssumptionsFeasibleR modelQ d) :
    objectiveQ.evalR d ≤ (1 : ℝ) / 4 := by
  convert checkUpperCertQ_sound_real_explicit upperCertQ upperCertQ_check rfl
    d hpsd hconstraints using 1 <;> norm_num [upperCertQ]

/-- Finite primal with nonzero smooth gradient and cancelling star subgradient. -/
def primalFactorQ : PSDFactorCertQ 5 :=
  { factors := [{ weight := 1, vector := ![1, 1, 1, 1, -(1/2)] }] }

def primalQ : DataQ (Fin 5) 5 :=
  { gram := factorGramQ primalFactorQ.factors
    position := modelQ.position
    gradient := modelQ.gradient
    value := ![0, 1, 1/2, 0, -(1/4)] }

theorem primalQ_psd_check : checkPSDFactorQ primalQ.gram primalFactorQ = true := by
  decide +kernel

theorem primalQ_constraints_check : checkAssumptionsFeasibleQ modelQ primalQ = true := by
  decide +kernel

theorem primalQ_value : objectiveQ.evalQ primalQ = (1 : ℚ) / 4 := by
  decide +kernel

/-- The old all-slot smooth interpolation test MUST reject this datum:
its slots belong to different functions. We do not claim `CoreFeasible`. -/
theorem primalQ_implicit_interpolation_rejected :
    checkInterpolationFeasibleQ primalQ = false := by
  decide +kernel

theorem primalQ_feasible_real :
    IsGramPosSemidef (castDataQ primalQ).gram ∧
      AssumptionsFeasibleR modelQ (castDataQ primalQ) := by
  constructor
  · exact checkPSDFactorQ_sound_real _ _ primalQ_psd_check
  · exact assumptionsFeasibleQ_toReal modelQ primalQ
      ((checkAssumptionsFeasibleQ_eq_true_iff _ _).mp primalQ_constraints_check)

theorem primalQ_value_real : objectiveQ.evalR (castDataQ primalQ) = (1 : ℝ) / 4 := by
  rw [LinearExprQ.evalR_castDataQ, primalQ_value]
  norm_num

def finiteValues : Set ℝ :=
  {r | ∃ d : DataR (Fin 5) 5, IsGramPosSemidef d.gram ∧
    AssumptionsFeasibleR modelQ d ∧ objectiveQ.evalR d = r}

theorem finite_tight : IsGreatest finiteValues ((1 : ℝ) / 4) := by
  constructor
  · exact ⟨castDataQ primalQ, primalQ_feasible_real.1,
      primalQ_feasible_real.2, primalQ_value_real⟩
  · intro r hr
    rcases hr with ⟨d, hp, hc, hv⟩
    rw [← hv]
    exact upper d hp hc

/-- A lower bound candidate is not an accepted upper certificate. -/
def wrongBoundQ : UpperCertQ modelQ := { upperCertQ with bound := 1/5 }

def wrongObjectiveQ : UpperCertQ modelQ :=
  { upperCertQ with
    objective := LinearExprQ.sub (LinearExprQ.valueVar 2) (LinearExprQ.valueVar 0) }

theorem wrongBoundQ_rejected : checkUpperCertQ wrongBoundQ = false := by
  decide +kernel

theorem wrongObjectiveQ_rejected : checkUpperCertQ wrongObjectiveQ = false := by
  decide +kernel

end LeanPEP.Profiles.ProximalGradientOneStep
