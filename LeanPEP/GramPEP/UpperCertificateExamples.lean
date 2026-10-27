import LeanPEP.GramPEP.UpperCertificateChecker
import LeanPEP.GramPEP.Coordinate

/-!
# General Gram upper-certificate examples

A two-point, two-coordinate model exercises all three nonnegative certificate
components in one exact identity:

* one ordered interpolation slack;
* one normalization assumption `1 - G₀₀ ≥ 0`; and
* one dual PSD term `G₁₁ ≥ 0` certified by `e₁e₁ᵀ`.

The accepted certificate proves

`(f₁ - f₀) + G₀₀ - G₁₁ ≤ 1`.

This is a deliberately small regression for the general checker. It is not a
claim about a complete optimization algorithm or a PEPit model.
-/

namespace LeanPEP
namespace GramPEP
namespace UpperCertificateExamples

/-- First coordinate expression in dimension two. -/
def e0Q : VecExpr 2 ℚ := standardBasisExpr (𝕜 := ℚ) 0

/-- Second coordinate expression in dimension two. -/
def e1Q : VecExpr 2 ℚ := standardBasisExpr (𝕜 := ℚ) 1

/-- Normalization constraint `1 - G₀₀`. -/
def normalizationQ : LinearExprQ 2 2 :=
  LinearExprQ.sub
    (LinearExprQ.const 2 2 1)
    (LinearExprQ.gramNorm (p := 2) e0Q)

/-- Two points with zero symbolic positions and gradients. -/
def twoPointModelQ : ModelQ 2 2 :=
  { position := fun _ => 0
    gradient := fun _ => 0
    assumptions := [normalizationQ] }

/-- Objective `(f₁ - f₀) + G₀₀ - G₁₁`. -/
def objectiveQ : LinearExprQ 2 2 :=
  LinearExprQ.add
    (LinearExprQ.sub
      (LinearExprQ.valueVar (m := 2) 1)
      (LinearExprQ.valueVar (m := 2) 0))
    (LinearExprQ.sub
      (LinearExprQ.gramNorm (p := 2) e0Q)
      (LinearExprQ.gramNorm (p := 2) e1Q))

/-- Dual matrix `e₁e₁ᵀ`. -/
def dualMatrixQ : Gram 2 ℚ :=
  weightedOuterQ { weight := 1, vector := e1Q }

/-- Exact one-factor PSD certificate for `dualMatrixQ`. -/
def dualFactorQ : PSDFactorCertQ 2 :=
  { factors := [{ weight := 1, vector := e1Q }] }

/-- Index of the sole formulation assumption in `twoPointModelQ`. -/
def twoPointAssumption0 : Fin twoPointModelQ.assumptions.length :=
  ⟨0, by simp [twoPointModelQ]⟩

/-- Exact certificate identity

`1 - objective = slack(0,1) + normalization + ⟨e₁e₁ᵀ,G⟩`.
-/
def upperCertQ : UpperCertQ twoPointModelQ :=
  { bound := 1
    objective := objectiveQ
    interpTerms := [{ weight := 1, i := 0, j := 1 }]
    assumptionTerms := [{ weight := 1, index := twoPointAssumption0 }]
    dualMatrix := dualMatrixQ
    dualFactor := dualFactorQ }

/-- The general checker accepts the exact certificate. -/
theorem upperCertQ_check : checkUpperCertQ upperCertQ = true := by
  native_decide

/-- The accepted certificate proves the claimed universal real upper bound. -/
theorem upper_bound
    (d : DataR (Fin 2) 2)
    (hrealizes : RealizesModelQ twoPointModelQ d)
    (hcore : CoreFeasible d)
    (hassumptions : AssumptionsFeasibleR twoPointModelQ d) :
    objectiveQ.evalR d ≤ (1 : ℝ) := by
  simpa [upperCertQ] using
    checkUpperCertQ_sound_real upperCertQ upperCertQ_check
      d hrealizes hcore hassumptions

/-- A negative interpolation multiplier is rejected. -/
def negativeInterpCertQ : UpperCertQ twoPointModelQ :=
  { upperCertQ with
    interpTerms := [{ weight := -1, i := 0, j := 1 }] }

/-- A negative assumption multiplier is rejected. -/
def negativeAssumptionCertQ : UpperCertQ twoPointModelQ :=
  { upperCertQ with
    assumptionTerms := [{ weight := -1, index := twoPointAssumption0 }] }

/-- A dual factor with a negative weight is rejected. -/
def negativeDualCertQ : UpperCertQ twoPointModelQ :=
  { upperCertQ with
    dualMatrix := weightedOuterQ { weight := -1, vector := e1Q }
    dualFactor := { factors := [{ weight := -1, vector := e1Q }] } }

/-- A wrong claimed bound is rejected by exact coefficient comparison. -/
def wrongBoundCertQ : UpperCertQ twoPointModelQ :=
  { upperCertQ with bound := 2 }

example : checkUpperCertQ negativeInterpCertQ = false := by native_decide
example : checkUpperCertQ negativeAssumptionCertQ = false := by native_decide
example : checkUpperCertQ negativeDualCertQ = false := by native_decide
example : checkUpperCertQ wrongBoundCertQ = false := by native_decide

/-! ## A genuine one-step Gram-PEP upper certificate -/

/-- Abstract Gram basis `(x₀, g₀, g₁)`. -/
def oneX0Q : VecExpr 3 ℚ := ![(1 : ℚ), 0, 0]
def oneG0Q : VecExpr 3 ℚ := ![(0 : ℚ), 1, 0]
def oneG1Q : VecExpr 3 ℚ := ![(0 : ℚ), 0, 1]

/-- Normalization `1 - ‖x₀‖²_G ≥ 0`. -/
def oneNormalizationQ : LinearExprQ 3 3 :=
  LinearExprQ.sub
    (LinearExprQ.const 3 3 1)
    (LinearExprQ.gramNorm (p := 3) oneX0Q)

/-- General-dimensional one-step GD model with points `(x★, x₀, x₁)` and
`x₁ = x₀ - g₀`. -/
def oneStepModelQ : ModelQ 3 3 :=
  { position := ![
      ![(0 : ℚ), 0, 0],
      ![(1 : ℚ), 0, 0],
      ![(1 : ℚ), -1, 0]]
    gradient := ![
      ![(0 : ℚ), 0, 0],
      ![(0 : ℚ), 1, 0],
      ![(0 : ℚ), 0, 1]]
    assumptions := [oneNormalizationQ] }

/-- Objective gap `f₁ - f★`. -/
def oneStepObjectiveQ : LinearExprQ 3 3 :=
  LinearExprQ.sub
    (LinearExprQ.valueVar (m := 3) 2)
    (LinearExprQ.valueVar (m := 3) 0)

/-- Dual factors corresponding to the three exact vector-square terms. -/
def oneStepDualFactorQ : PSDFactorCertQ 3 :=
  { factors :=
      [ { weight := (1 : ℚ) / 4,
          vector := ![-((1 : ℚ) / 3), 1, 0] }
      , { weight := (1 : ℚ) / 4,
          vector := ![-((1 : ℚ) / 3), 0, 1] }
      , { weight := (1 : ℚ) / 4,
          vector := ![-((2 : ℚ) / 3), 1, 1] } ] }

/-- Exact rational dual PSD matrix reconstructed from its factors. -/
def oneStepDualMatrixQ : Gram 3 ℚ :=
  factorGramQ oneStepDualFactorQ.factors

/-- Index of the sole formulation assumption in `oneStepModelQ`. -/
def oneStepAssumption0 : Fin oneStepModelQ.assumptions.length :=
  ⟨0, by simp [oneStepModelQ]⟩

/-- General-dimensional exact certificate for the normalized one-step bound
`f₁ - f★ ≤ 1/6`. -/
def oneStepUpperCertQ : UpperCertQ oneStepModelQ :=
  { bound := (1 : ℚ) / 6
    objective := oneStepObjectiveQ
    interpTerms :=
      [ { weight := (1 : ℚ) / 2, i := 0, j := 2 }
      , { weight := (1 : ℚ) / 2, i := 0, j := 1 }
      , { weight := (1 : ℚ) / 2, i := 1, j := 2 } ]
    assumptionTerms :=
      [{ weight := (1 : ℚ) / 6, index := oneStepAssumption0 }]
    dualMatrix := oneStepDualMatrixQ
    dualFactor := oneStepDualFactorQ }

/-- The same general checker accepts the genuine one-step Gram certificate. -/
theorem oneStepUpperCertQ_check :
    checkUpperCertQ oneStepUpperCertQ = true := by
  native_decide

@[simp] theorem oneStepObjectiveQ_evalR
    (d : DataR (Fin 3) 3) :
    oneStepObjectiveQ.evalR d = d.value 2 - d.value 0 := by
  simp [oneStepObjectiveQ]

/-- An accepted exact certificate proves the normalized general-dimensional
one-step finite Gram-PEP upper bound. -/
theorem oneStep_upper
    (d : DataR (Fin 3) 3)
    (hrealizes : RealizesModelQ oneStepModelQ d)
    (hcore : CoreFeasible d)
    (hassumptions : AssumptionsFeasibleR oneStepModelQ d) :
    d.value 2 - d.value 0 ≤ (1 : ℝ) / 6 := by
  simpa [oneStepUpperCertQ] using
    checkUpperCertQ_sound_real oneStepUpperCertQ
      oneStepUpperCertQ_check d hrealizes hcore hassumptions

end UpperCertificateExamples
end GramPEP
end LeanPEP
