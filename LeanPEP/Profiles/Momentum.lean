import LeanPEP.Profiles.GramCompilation

/-!
# Causal two-sequence momentum compilation

A schedule describes the two distinct sequences

```
x_0 = y_0 = initial
x_(k+1) = y_k - step(k) g_k
y_(k+1) = x_(k+1) + momentum(k) (x_(k+1) - x_k).
```

Here `g_k` is sampled at the query point `y_k`, not at `x_k`.
The recurrence is compiled over exact rational coefficients, then lowered to
`FixedStepFirstOrder.ProfileQ` and the existing Gram compiler.  Causality is
proved for arbitrary schedules; no sign restriction on the schedule is needed
for this structural property (or asserted as a convergence guarantee).

`outputProfileQ N` samples `y_0, ..., y_(N-1), x_N`.  In particular the last
sample is a terminal observation of the state, NOT the unused query `y_N`.
Its gradient is available for interpolation but is not used in any update.
At `N = 0` the sole non-star sample is the initial state.
-/

namespace LeanPEP.Profiles.Momentum

open LeanPEP.Toy.FiniteGD
open LeanPEP.Profiles.FixedStepFirstOrder
open LeanPEP.Profiles.GramCompilation
open LeanPEP.GramPEP

/-- Exact predetermined step and momentum schedules. -/
structure ScheduleQ where
  step : ℕ → ℚ
  momentum : ℕ → ℚ

/-- Cumulative gradient coefficients of `(state, query)` after `k` steps.
Positions are `initial - sum_j coefficient(j) * g_j`. -/
def coefficientStateQ (s : ScheduleQ) : ℕ → (ℕ → ℚ) × (ℕ → ℚ)
  | 0 => ((fun _ => 0), (fun _ => 0))
  | k + 1 =>
      let old := coefficientStateQ s k
      let newState : ℕ → ℚ := fun j =>
        old.2 j + if j = k then s.step k else 0
      (newState, fun j =>
        (1 + s.momentum k) * newState j - s.momentum k * old.1 j)

/-- Coefficients of the state point `x_k`. -/
def stateCoeffQ (s : ScheduleQ) (k j : ℕ) : ℚ :=
  (coefficientStateQ s k).1 j

/-- Coefficients of the query point `y_k`. -/
def queryCoeffQ (s : ScheduleQ) (k j : ℕ) : ℚ :=
  (coefficientStateQ s k).2 j

@[simp] theorem stateCoeffQ_zero (s : ScheduleQ) (j : ℕ) :
    stateCoeffQ s 0 j = 0 := rfl

@[simp] theorem queryCoeffQ_zero (s : ScheduleQ) (j : ℕ) :
    queryCoeffQ s 0 j = 0 := rfl

/-- Gradient-step coefficient recurrence. -/
theorem stateCoeffQ_succ (s : ScheduleQ) (k j : ℕ) :
    stateCoeffQ s (k + 1) j =
      queryCoeffQ s k j + if j = k then s.step k else 0 := rfl

/-- Momentum coefficient recurrence. -/
theorem queryCoeffQ_succ (s : ScheduleQ) (k j : ℕ) :
    queryCoeffQ s (k + 1) j =
      (1 + s.momentum k) * stateCoeffQ s (k + 1) j -
        s.momentum k * stateCoeffQ s k j := rfl

/-- Both sequences only depend on strictly earlier oracle answers. -/
theorem coefficientStateQ_causal (s : ScheduleQ) :
    ∀ k j : ℕ, k ≤ j →
      stateCoeffQ s k j = 0 ∧ queryCoeffQ s k j = 0 := by
  intro k
  induction k with
  | zero =>
      intro j hj
      exact ⟨rfl, rfl⟩
  | succ k ih =>
      intro j hj
      have hkj : k ≤ j := by omega
      have hne : j ≠ k := by omega
      rcases ih j hkj with ⟨hx, hy⟩
      constructor
      · rw [stateCoeffQ_succ]
        simp [hy, hne]
      · rw [queryCoeffQ_succ, stateCoeffQ_succ]
        simp [hy, hx, hne]

/-- State-sequence causality. -/
theorem stateCoeffQ_causal (s : ScheduleQ) (k j : ℕ) (h : k ≤ j) :
    stateCoeffQ s k j = 0 :=
  (coefficientStateQ_causal s k j h).1

/-- Query-sequence causality. -/
theorem queryCoeffQ_causal (s : ScheduleQ) (k j : ℕ) (h : k ≤ j) :
    queryCoeffQ s k j = 0 :=
  (coefficientStateQ_causal s k j h).2

/-- State coefficients in the existing affine syntax. -/
def stateAffineQ (N : ℕ) (s : ScheduleQ) (k : ℕ) : GradAffineQ N :=
  { constCoeff := 1
    gradCoeff := fun j => -stateCoeffQ s k j.val }

/-- Query coefficients in the existing affine syntax. -/
def queryAffineQ (N : ℕ) (s : ScheduleQ) (k : ℕ) : GradAffineQ N :=
  { constCoeff := 1
    gradCoeff := fun j => -queryCoeffQ s k j.val }

/-- Compilation respects the actual two-sequence gradient-step equation. -/
theorem stateAffineQ_succ {N : ℕ} (s : ScheduleQ) (k : Fin (N + 1)) :
    stateAffineQ N s (k.val + 1) =
      GradAffineQ.sub (queryAffineQ N s k.val)
        (GradAffineQ.scale (s.step k.val) (GradAffineQ.basis k)) := by
  apply GradAffineQ.ext
  · simp [stateAffineQ, queryAffineQ, GradAffineQ.sub, GradAffineQ.add,
      GradAffineQ.neg, GradAffineQ.scale, GradAffineQ.basis]
  · funext j
    by_cases h : j = k
    · subst j
      simp [stateAffineQ, queryAffineQ, stateCoeffQ_succ,
        GradAffineQ.sub, GradAffineQ.add, GradAffineQ.neg,
        GradAffineQ.scale, GradAffineQ.basis, unitCoeff] <;> ring
    · have hv : j.val ≠ k.val := by
        intro heq
        exact h (Fin.ext heq)
      simp [stateAffineQ, queryAffineQ, stateCoeffQ_succ,
        GradAffineQ.sub, GradAffineQ.add, GradAffineQ.neg,
        GradAffineQ.scale, GradAffineQ.basis, unitCoeff, h, hv]

/-- Compilation respects momentum mixing of consecutive state points. -/
theorem queryAffineQ_succ (N : ℕ) (s : ScheduleQ) (k : ℕ) :
    queryAffineQ N s (k + 1) =
      GradAffineQ.add (stateAffineQ N s (k + 1))
        (GradAffineQ.scale (s.momentum k)
          (GradAffineQ.sub (stateAffineQ N s (k + 1))
            (stateAffineQ N s k))) := by
  apply GradAffineQ.ext
  · simp [queryAffineQ, stateAffineQ, GradAffineQ.add, GradAffineQ.scale,
      GradAffineQ.sub, GradAffineQ.neg]
  · funext j
    simp only [queryAffineQ, stateAffineQ, queryCoeffQ_succ,
      GradAffineQ.add, GradAffineQ.scale, GradAffineQ.sub, GradAffineQ.neg]
    ring

/-- Scalar evaluation of the compiled state update. -/
theorem evalR_stateAffineQ_succ {N : ℕ} (s : ScheduleQ)
    (k : Fin (N + 1)) (d : LeanPEP.Toy.FiniteGD.DataR N) :
    (stateAffineQ N s (k.val + 1)).evalR d =
      (queryAffineQ N s k.val).evalR d -
        (s.step k.val : ℝ) * d.grad k := by
  rw [stateAffineQ_succ]
  simp

/-- Scalar evaluation of the compiled momentum update. -/
theorem evalR_queryAffineQ_succ {N : ℕ} (s : ScheduleQ)
    (k : ℕ) (d : LeanPEP.Toy.FiniteGD.DataR N) :
    (queryAffineQ N s (k + 1)).evalR d =
      (stateAffineQ N s (k + 1)).evalR d +
        (s.momentum k : ℝ) *
          ((stateAffineQ N s (k + 1)).evalR d -
            (stateAffineQ N s k).evalR d) := by
  rw [queryAffineQ_succ]
  simp

/-- Lower the query sequence to the established fixed-step profile. -/
def queryProfileQ (N : ℕ) (s : ScheduleQ) : ProfileQ N :=
  { stepCoeff := fun i j => queryCoeffQ s i.val j.val
    causal := fun i j h => queryCoeffQ_causal s i.val j.val h }

/-- Lower the queried points and terminal state to the established profile.
The final gradient is an observation only, never a fifth/future update. -/
def outputProfileQ (N : ℕ) (s : ScheduleQ) : ProfileQ N :=
  { stepCoeff := fun i j =>
      if i.val = N then stateCoeffQ s N j.val
      else queryCoeffQ s i.val j.val
    causal := by
      intro i j hij
      by_cases h : i.val = N
      · simpa [h] using stateCoeffQ_causal s N j.val (by omega)
      · simpa [h] using queryCoeffQ_causal s i.val j.val hij }

/-- Before the terminal index the output profile contains query points. -/
theorem outputProfileQ_before_final {N : ℕ} (s : ScheduleQ)
    (i j : Fin (N + 1)) (hi : i.val < N) :
    (outputProfileQ N s).stepCoeff i j = queryCoeffQ s i.val j.val := by
  simp [outputProfileQ, Nat.ne_of_lt hi]

/-- The terminal index contains the state, not the extrapolated query. -/
@[simp] theorem outputProfileQ_final {N : ℕ} (s : ScheduleQ)
    (j : Fin (N + 1)) :
    (outputProfileQ N s).stepCoeff (Fin.last N) j = stateCoeffQ s N j.val := by
  simp [outputProfileQ]

/-- Exact affine realization of the query-only profile. -/
theorem iterateAffineQ_queryProfileQ {N : ℕ} (s : ScheduleQ)
    (i : Fin (N + 1)) :
    iterateAffineQ (queryProfileQ N s) i = queryAffineQ N s i.val := by
  apply GradAffineQ.ext
  · exact iterateAffineQ_constCoeff _ _
  · funext j
    exact iterateAffineQ_gradCoeff _ _ _

/-- Exact affine realization of nonterminal queries in the output profile. -/
theorem iterateAffineQ_outputProfileQ_before_final {N : ℕ} (s : ScheduleQ)
    (i : Fin (N + 1)) (hi : i.val < N) :
    iterateAffineQ (outputProfileQ N s) i = queryAffineQ N s i.val := by
  apply GradAffineQ.ext
  · exact iterateAffineQ_constCoeff _ _
  · funext j
    rw [iterateAffineQ_gradCoeff, outputProfileQ_before_final s i j hi]
    rfl

/-- Exact affine realization of the terminal state. -/
theorem iterateAffineQ_outputProfileQ_final {N : ℕ} (s : ScheduleQ) :
    iterateAffineQ (outputProfileQ N s) (Fin.last N) = stateAffineQ N s N := by
  apply GradAffineQ.ext
  · exact iterateAffineQ_constCoeff _ _
  · funext j
    rw [iterateAffineQ_gradCoeff, outputProfileQ_final]
    rfl

/-- Compose the momentum output profile with the existing normalization and
objective profiles; no new Gram semantics are introduced. -/
def outputPEPProfileQ (N : ℕ) (s : ScheduleQ)
    (normalization : NormalizationProfileQ) : PEPProfileQ N :=
  { algorithm := outputProfileQ N s
    normalization := normalization
    objective := finalGapObjectiveProfileQ N }

/-- General Gram formulation with points `(star, y_0, ..., y_(N-1), x_N)`. -/
def outputModelQ (N : ℕ) (s : ScheduleQ)
    (normalization : NormalizationProfileQ) : ModelQ (N + 2) (N + 2) :=
  compileModelQ (outputPEPProfileQ N s normalization)

/-- Final state-value objective, compiled by the established objective layer. -/
def outputObjectiveQ (N : ℕ) (s : ScheduleQ)
    (normalization : NormalizationProfileQ) : LinearExprQ (N + 2) (N + 2) :=
  compileObjectiveQ (outputPEPProfileQ N s normalization)

/-- Nonterminal sampled positions are exactly the homogenized queries. -/
theorem outputModelQ_position_before_final {N : ℕ} (s : ScheduleQ)
    (normalization : NormalizationProfileQ) (i : Fin (N + 1)) (hi : i.val < N) :
    (outputModelQ N s normalization).position (pointIndex (Point.iter i)) =
      affineVecQ (queryAffineQ N s i.val) := by
  change (compileModelQ (outputPEPProfileQ N s normalization)).position
      (pointIndex (Point.iter i)) = _
  rw [compileModelQ_position_pointIndex]
  change affineVecQ (iterateAffineQ (outputProfileQ N s) i) = _
  rw [iterateAffineQ_outputProfileQ_before_final s i hi]

/-- The final sampled position is exactly the homogenized state. -/
theorem outputModelQ_position_final {N : ℕ} (s : ScheduleQ)
    (normalization : NormalizationProfileQ) :
    (outputModelQ N s normalization).position (pointIndex (Point.iter (Fin.last N))) =
      affineVecQ (stateAffineQ N s N) := by
  change (compileModelQ (outputPEPProfileQ N s normalization)).position
      (pointIndex (Point.iter (Fin.last N))) = _
  rw [compileModelQ_position_pointIndex]
  change affineVecQ (iterateAffineQ (outputProfileQ N s) (Fin.last N)) = _
  rw [iterateAffineQ_outputProfileQ_final]

/-- Gram compilation retains causality for arbitrary momentum schedules. -/
theorem outputModelQ_causal {N : ℕ} (s : ScheduleQ)
    (normalization : NormalizationProfileQ)
    (i j : Fin (N + 1)) (hij : i.val ≤ j.val) :
    (outputModelQ N s normalization).position (pointIndex (Point.iter i))
      (gradientBasisIndex j) = 0 :=
  compileModelQ_iter_gradient_coordinate_of_le
    (outputPEPProfileQ N s normalization) i j hij

/-- The terminal gradient observation is unused in all sampled positions. -/
theorem outputModelQ_terminal_gradient_unused {N : ℕ} (s : ScheduleQ)
    (normalization : NormalizationProfileQ) (i : Fin (N + 1)) :
    (outputModelQ N s normalization).position (pointIndex (Point.iter i))
      (gradientBasisIndex (Fin.last N)) = 0 := by
  apply outputModelQ_causal
  have hi := i.isLt
  simp only [Fin.val_last]
  omega

/-- The objective evaluates to the function gap at the terminal state sample. -/
@[simp] theorem outputObjectiveQ_evalR {N : ℕ} (s : ScheduleQ)
    (normalization : NormalizationProfileQ)
    (d : LeanPEP.GramPEP.DataR (Fin (N + 2)) (N + 2)) :
    (outputObjectiveQ N s normalization).evalR d =
      d.value (pointIndex (Point.iter (Fin.last N))) -
        d.value (pointIndex (Point.star : Point N)) := by
  simp [outputObjectiveQ, outputPEPProfileQ, compileObjectiveQ,
    finalGapObjectiveProfileQ]

end LeanPEP.Profiles.Momentum
