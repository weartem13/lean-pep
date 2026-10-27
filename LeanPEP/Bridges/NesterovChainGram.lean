import LeanPEP.GramPEP.RationalBridge
import LeanPEP.HardInstances.NesterovChain.SmallTrajectory
import LeanPEP.Toy.FiniteGD.Core

/-!
# Exact Gram-PEP witnesses from small Nesterov-chain trajectories

This module converts the already formalized dimension-3 one-step and
 dimension-5 two-step Nesterov-chain executions into exact Gram-PEP sampled
 data.

The abstract Gram basis is the ambient standard coordinate basis.  Therefore
 the PEP Gram matrix is the identity matrix; it is not the Nesterov Hessian
 structure matrix.  Exact rational position, gradient, and value samples are
 checked against every ordered interpolation inequality, while the identity
 Gram matrix is independently accepted by the exact PSD factorization checker.
-/

namespace LeanPEP
namespace Bridges
namespace NesterovChainGram

open GramPEP

open HardInstances.NesterovChain
open scoped Matrix

abbrev Dim3Point := Toy.FiniteGD.Point 1
abbrev Dim5Point := Toy.FiniteGD.Point 2

/-! ## Dimension 3, one unit GD step -/

/-- Exact rational coordinate positions: optimum, initial point, and first
iterate. -/
def dim3PositionQ : Dim3Point → VecExpr 3 ℚ
  | .star => ![(3 : ℚ) / 4, (1 : ℚ) / 2, (1 : ℚ) / 4]
  | .iter k =>
      ![![(0 : ℚ), 0, 0],
        ![(1 : ℚ) / 4, 0, 0]] k

/-- Exact rational gradient samples in dimension 3. -/
def dim3GradientQ : Dim3Point → VecExpr 3 ℚ
  | .star => ![(0 : ℚ), 0, 0]
  | .iter k =>
      ![![-((1 : ℚ) / 4), 0, 0],
        ![-((1 : ℚ) / 8), -((1 : ℚ) / 16), 0]] k

/-- Exact rational function values in dimension 3. -/
def dim3ValueQ : Dim3Point → ℚ
  | .star => -((3 : ℚ) / 32)
  | .iter k => ![(0 : ℚ), -((3 : ℚ) / 64)] k

/-- Exact Gram-PEP data for the dimension-3 trajectory. -/
def dim3DataQ : DataQ Dim3Point 3 :=
  { gram := standardGram
    position := dim3PositionQ
    gradient := dim3GradientQ
    value := dim3ValueQ }

/-- Canonical standard-basis PSD certificate for the dimension-3 Gram matrix. -/
def dim3PSDCertQ : PSDFactorCertQ 3 :=
  standardFactorCertQ 3

/-- The exact PSD checker accepts the dimension-3 identity Gram matrix. -/
theorem dim3PSDCertQ_check :
    checkPSDFactorQ dim3DataQ.gram dim3PSDCertQ = true := by
  native_decide

/-- Every ordered dimension-3 smooth-convex interpolation slack is nonnegative. -/
theorem dim3InterpolationFeasibleQ :
    InterpolationFeasible dim3DataQ := by
  intro i j
  fin_cases i <;> fin_cases j <;> native_decide

/-- The exact rational dimension-3 Gram witness is core feasible. -/
theorem dim3CoreFeasibleQ :
    CoreFeasible dim3DataQ :=
  ⟨checkPSDFactorQ_sound _ _ dim3PSDCertQ_check,
    dim3InterpolationFeasibleQ⟩

/-- The encoded point update is exactly one unit gradient-descent step. -/
theorem dim3TrajectoryQ :
    dim3DataQ.position (.iter 1) =
      dim3DataQ.position (.iter 0) - dim3DataQ.gradient (.iter 0) := by
  native_decide

/-- Exact initial distance represented by the Gram witness. -/
theorem dim3InitialDistanceSqQ :
    gramNormSq dim3DataQ.gram
        (dim3DataQ.position (.iter 0) - dim3DataQ.position .star) =
      (7 : ℚ) / 8 := by
  native_decide

/-- Exact final objective gap represented by the Gram witness. -/
theorem dim3ObjectiveGapQ :
    dim3DataQ.value (.iter 1) - dim3DataQ.value .star =
      (3 : ℚ) / 64 := by
  native_decide

/-- The exact normalized Gram-witness performance is `3 / 56`. -/
theorem dim3NormalizedPerformanceQ :
    (dim3DataQ.value (.iter 1) - dim3DataQ.value .star) /
        gramNormSq dim3DataQ.gram
          (dim3DataQ.position (.iter 0) - dim3DataQ.position .star) =
      (3 : ℚ) / 56 := by
  native_decide

/-- Real cast of the exact rational dimension-3 Gram witness. -/
noncomputable def dim3DataR : DataR Dim3Point 3 :=
  castDataQ dim3DataQ

/-- The cast dimension-3 witness remains core feasible over the reals. -/
theorem dim3CoreFeasibleR :
    CoreFeasible dim3DataR := by
  constructor
  · simpa [dim3DataR, dim3DataQ] using
      (standardGram_posSemidef (m := 3) (𝕜 := ℝ))
  · exact interpolationFeasibleQ_toReal dim3DataQ dim3InterpolationFeasibleQ

/-- Exact final gradient of the dimension-3 one-step trajectory. -/
noncomputable def dim3G1 : Vector 2 :=
  ![-((1 : ℝ) / 8), -((1 : ℝ) / 16), 0]

/-- Polarization against the first dimension-3 iterate. -/
theorem energyInner_dim3X1 (z : Vector 2) :
    energyInner dim3X1 z =
      ((1 : ℝ) / 2) * z 0 - ((1 : ℝ) / 4) * z 1 := by
  unfold energyInner
  rw [Fin.sum_univ_two]
  simp [edgeDiff, Fin.last]
  ring

/-- The exact final gradient used by the Gram witness is the real function's
actual gradient. -/
theorem dim3_gradient_after_one :
    gradient 2 1 dim3X1 = dim3G1 := by
  classical
  funext i
  have h := gradient_dot (n := 2) 1 dim3X1 (Pi.single i 1)
  rw [energyInner_dim3X1] at h
  fin_cases i <;>
    norm_num [dim3G1, Pi.single_apply] at h ⊢ <;>
    exact h

/-- Actual real sampled data from the formalized dimension-3 chain execution. -/
noncomputable def dim3ActualDataR : DataR Dim3Point 3 :=
  { gram := standardGram
    position := fun p =>
      match p with
      | .star => minimizer 2
      | .iter k => dim3Path k
    gradient := fun p =>
      match p with
      | .star => gradient 2 1 (minimizer 2)
      | .iter k => gradient 2 1 (dim3Path k)
    value := fun p =>
      match p with
      | .star => function 2 1 (minimizer 2)
      | .iter k => function 2 1 (dim3Path k) }

/-- The cast rational Gram witness agrees entrywise with the already formalized
real dimension-3 function samples. -/
theorem dim3DataR_eq_actual :
    dim3DataR = dim3ActualDataR := by
  apply Data.ext
  · simpa [dim3DataR, dim3DataQ, dim3ActualDataR, castDataQ] using
      (castGramQ_standardGram (m := 3))
  · funext p i
    cases p with
    | star =>
        fin_cases i <;>
          norm_num [dim3DataR, dim3DataQ, dim3PositionQ,
            dim3ActualDataR, castDataQ, castVecQ, minimizer]
    | iter k =>
        fin_cases k <;> fin_cases i <;>
          norm_num [dim3DataR, dim3DataQ, dim3PositionQ,
            dim3ActualDataR, castDataQ, castVecQ,
            dim3Path, dim3X0, dim3X1]
  · funext p i
    cases p with
    | star =>
        change dim3DataR.gradient .star i = gradient 2 1 (minimizer 2) i
        rw [gradient_minimizer]
        fin_cases i <;>
          norm_num [dim3DataR, dim3DataQ, dim3GradientQ,
            castDataQ, castVecQ]
    | iter k =>
        fin_cases k
        · change dim3DataR.gradient (.iter 0) i =
            gradient 2 1 dim3X0 i
          rw [dim3_gradient_start]
          fin_cases i <;>
            norm_num [dim3DataR, dim3DataQ, dim3GradientQ,
              dim3ActualDataR, castDataQ, castVecQ, dim3G0]
        · change dim3DataR.gradient (.iter 1) i =
            gradient 2 1 dim3X1 i
          rw [dim3_gradient_after_one]
          fin_cases i <;>
            norm_num [dim3DataR, dim3DataQ, dim3GradientQ,
              dim3ActualDataR, castDataQ, castVecQ, dim3G1]
  · funext p
    cases p with
    | star =>
        change dim3DataR.value .star = function 2 1 (minimizer 2)
        rw [dim3_function_minimum]
        norm_num [dim3DataR, dim3DataQ, dim3ValueQ, castDataQ]
    | iter k =>
        fin_cases k
        · change dim3DataR.value (.iter 0) = function 2 1 dim3X0
          rw [dim3_function_start]
          norm_num [dim3DataR, dim3DataQ, dim3ValueQ,
            dim3ActualDataR, castDataQ]
        · change dim3DataR.value (.iter 1) = function 2 1 dim3X1
          rw [dim3_function_after_one]
          norm_num [dim3DataR, dim3DataQ, dim3ValueQ,
            dim3ActualDataR, castDataQ]

/-! ## Dimension 5, two unit GD steps -/

/-- Exact rational coordinate positions: optimum and three iterates. -/
def dim5PositionQ : Dim5Point → VecExpr 5 ℚ
  | .star =>
      ![(5 : ℚ) / 6, (2 : ℚ) / 3, (1 : ℚ) / 2,
        (1 : ℚ) / 3, (1 : ℚ) / 6]
  | .iter k =>
      ![![(0 : ℚ), 0, 0, 0, 0],
        ![(1 : ℚ) / 4, 0, 0, 0, 0],
        ![(3 : ℚ) / 8, (1 : ℚ) / 16, 0, 0, 0]] k

/-- Exact rational gradient samples in dimension 5. -/
def dim5GradientQ : Dim5Point → VecExpr 5 ℚ
  | .star => ![(0 : ℚ), 0, 0, 0, 0]
  | .iter k =>
      ![![-((1 : ℚ) / 4), 0, 0, 0, 0],
        ![-((1 : ℚ) / 8), -((1 : ℚ) / 16), 0, 0, 0],
        ![-((5 : ℚ) / 64), -((1 : ℚ) / 16),
          -((1 : ℚ) / 64), 0, 0]] k

/-- Exact rational function values in dimension 5. -/
def dim5ValueQ : Dim5Point → ℚ
  | .star => -((5 : ℚ) / 48)
  | .iter k =>
      ![(0 : ℚ), -((3 : ℚ) / 64), -((65 : ℚ) / 1024)] k

/-- Exact Gram-PEP data for the dimension-5 trajectory. -/
def dim5DataQ : DataQ Dim5Point 5 :=
  { gram := standardGram
    position := dim5PositionQ
    gradient := dim5GradientQ
    value := dim5ValueQ }

/-- Canonical standard-basis PSD certificate for the dimension-5 Gram matrix. -/
def dim5PSDCertQ : PSDFactorCertQ 5 :=
  standardFactorCertQ 5

/-- The exact PSD checker accepts the dimension-5 identity Gram matrix. -/
theorem dim5PSDCertQ_check :
    checkPSDFactorQ dim5DataQ.gram dim5PSDCertQ = true := by
  native_decide

/-- Every ordered dimension-5 smooth-convex interpolation slack is nonnegative. -/
theorem dim5InterpolationFeasibleQ :
    InterpolationFeasible dim5DataQ := by
  intro i j
  fin_cases i <;> fin_cases j <;> native_decide

/-- The exact rational dimension-5 Gram witness is core feasible. -/
theorem dim5CoreFeasibleQ :
    CoreFeasible dim5DataQ :=
  ⟨checkPSDFactorQ_sound _ _ dim5PSDCertQ_check,
    dim5InterpolationFeasibleQ⟩

/-- The first encoded update is exactly one unit GD step. -/
theorem dim5TrajectoryStep0Q :
    dim5DataQ.position (.iter 1) =
      dim5DataQ.position (.iter 0) - dim5DataQ.gradient (.iter 0) := by
  native_decide

/-- The second encoded update is exactly one unit GD step. -/
theorem dim5TrajectoryStep1Q :
    dim5DataQ.position (.iter 2) =
      dim5DataQ.position (.iter 1) - dim5DataQ.gradient (.iter 1) := by
  native_decide

/-- Exact initial distance represented by the dimension-5 Gram witness. -/
theorem dim5InitialDistanceSqQ :
    gramNormSq dim5DataQ.gram
        (dim5DataQ.position (.iter 0) - dim5DataQ.position .star) =
      (55 : ℚ) / 36 := by
  native_decide

/-- Exact final objective gap represented by the dimension-5 Gram witness. -/
theorem dim5ObjectiveGapQ :
    dim5DataQ.value (.iter 2) - dim5DataQ.value .star =
      (125 : ℚ) / 3072 := by
  native_decide

/-- The exact normalized dimension-5 Gram-witness performance is `75 / 2816`. -/
theorem dim5NormalizedPerformanceQ :
    (dim5DataQ.value (.iter 2) - dim5DataQ.value .star) /
        gramNormSq dim5DataQ.gram
          (dim5DataQ.position (.iter 0) - dim5DataQ.position .star) =
      (75 : ℚ) / 2816 := by
  native_decide

/-- Real cast of the exact rational dimension-5 Gram witness. -/
noncomputable def dim5DataR : DataR Dim5Point 5 :=
  castDataQ dim5DataQ

/-- The cast dimension-5 witness remains core feasible over the reals. -/
theorem dim5CoreFeasibleR :
    CoreFeasible dim5DataR := by
  constructor
  · simpa [dim5DataR, dim5DataQ] using
      (standardGram_posSemidef (m := 5) (𝕜 := ℝ))
  · exact interpolationFeasibleQ_toReal dim5DataQ dim5InterpolationFeasibleQ

/-- Exact final gradient of the dimension-5 two-step trajectory. -/
noncomputable def dim5G2 : Vector 4 :=
  ![-((5 : ℝ) / 64), -((1 : ℝ) / 16), -((1 : ℝ) / 64), 0, 0]

/-- Polarization against the second dimension-5 iterate. -/
theorem energyInner_dim5X2 (z : Vector 4) :
    energyInner dim5X2 z =
      ((11 : ℝ) / 16) * z 0 - ((1 : ℝ) / 4) * z 1
        - ((1 : ℝ) / 16) * z 2 := by
  unfold energyInner
  rw [Fin.sum_univ_four]
  simp [edgeDiff, Fin.last]
  ring

/-- The exact final gradient used by the Gram witness is the real function's
actual gradient. -/
theorem dim5_gradient_after_two :
    gradient 4 1 dim5X2 = dim5G2 := by
  classical
  funext i
  have h := gradient_dot (n := 4) 1 dim5X2 (Pi.single i 1)
  rw [energyInner_dim5X2] at h
  fin_cases i <;>
    norm_num [dim5G2, Pi.single_apply, Fin.ext_iff] at h ⊢ <;>
    exact h

/-- Actual real sampled data from the formalized dimension-5 chain execution. -/
noncomputable def dim5ActualDataR : DataR Dim5Point 5 :=
  { gram := standardGram
    position := fun p =>
      match p with
      | .star => minimizer 4
      | .iter k => dim5Path k
    gradient := fun p =>
      match p with
      | .star => gradient 4 1 (minimizer 4)
      | .iter k => gradient 4 1 (dim5Path k)
    value := fun p =>
      match p with
      | .star => function 4 1 (minimizer 4)
      | .iter k => function 4 1 (dim5Path k) }

/-- The cast rational Gram witness agrees entrywise with the already formalized
real dimension-5 function samples. -/
theorem dim5DataR_eq_actual :
    dim5DataR = dim5ActualDataR := by
  apply Data.ext
  · simpa [dim5DataR, dim5DataQ, dim5ActualDataR, castDataQ] using
      (castGramQ_standardGram (m := 5))
  · funext p i
    cases p with
    | star =>
        fin_cases i <;>
          norm_num [dim5DataR, dim5DataQ, dim5PositionQ,
            dim5ActualDataR, castDataQ, castVecQ, minimizer]
    | iter k =>
        fin_cases k <;> fin_cases i <;>
          norm_num [dim5DataR, dim5DataQ, dim5PositionQ,
            dim5ActualDataR, castDataQ, castVecQ,
            dim5Path, dim5X0, dim5X1, dim5X2]
  · funext p i
    cases p with
    | star =>
        change dim5DataR.gradient .star i = gradient 4 1 (minimizer 4) i
        rw [gradient_minimizer]
        fin_cases i <;>
          norm_num [dim5DataR, dim5DataQ, dim5GradientQ,
            castDataQ, castVecQ]
    | iter k =>
        fin_cases k
        · change dim5DataR.gradient (.iter 0) i =
            gradient 4 1 dim5X0 i
          rw [dim5_gradient_start]
          fin_cases i <;>
            norm_num [dim5DataR, dim5DataQ, dim5GradientQ,
              dim5ActualDataR, castDataQ, castVecQ, dim5G0]
        · change dim5DataR.gradient (.iter 1) i =
            gradient 4 1 dim5X1 i
          rw [dim5_gradient_after_one]
          fin_cases i <;>
            norm_num [dim5DataR, dim5DataQ, dim5GradientQ,
              dim5ActualDataR, castDataQ, castVecQ, dim5G1]
        · change dim5DataR.gradient (.iter 2) i =
            gradient 4 1 dim5X2 i
          rw [dim5_gradient_after_two]
          fin_cases i <;>
            norm_num [dim5DataR, dim5DataQ, dim5GradientQ,
              dim5ActualDataR, castDataQ, castVecQ, dim5G2,
              Matrix.cons_val_two]
  · funext p
    cases p with
    | star =>
        change dim5DataR.value .star = function 4 1 (minimizer 4)
        rw [dim5_function_minimum]
        norm_num [dim5DataR, dim5DataQ, dim5ValueQ, castDataQ]
    | iter k =>
        fin_cases k
        · change dim5DataR.value (.iter 0) = function 4 1 dim5X0
          rw [dim5_function_start]
          norm_num [dim5DataR, dim5DataQ, dim5ValueQ,
            dim5ActualDataR, castDataQ]
        · change dim5DataR.value (.iter 1) = function 4 1 dim5X1
          rw [dim5_function_after_one]
          norm_num [dim5DataR, dim5DataQ, dim5ValueQ,
            dim5ActualDataR, castDataQ]
        · change dim5DataR.value (.iter 2) = function 4 1 dim5X2
          rw [dim5_function_after_two]
          norm_num [dim5DataR, dim5DataQ, dim5ValueQ,
            dim5ActualDataR, castDataQ, Matrix.cons_val_two]

end NesterovChainGram
end Bridges
end LeanPEP
