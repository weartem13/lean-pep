import LeanPEP.ActualFunction.ProfileGram
import LeanPEP.Profiles.Momentum

/-!
# Actual two-sequence momentum and its compiled Gram realization

The recursion below evaluates the actual oracle at the query, not at the
state.  It is independent of any certificate or finite Gram data.  We prove
that its state/query pair realizes the already verified affine coefficient
recurrence for every `k <= N`, then select `(y_0,...,y_(N-1),x_N)` exactly as
the output profile does.  The terminal gradient is only an observation.

All schedules are rational and arbitrary.  Structural realization needs no
sign restrictions and asserts no convergence rate without an accepted
certificate.  An independent `IsRun` interface supports externally defined
state/query sequences via a proved uniqueness theorem.
-/

namespace LeanPEP.ActualFunction.MomentumActual

open LeanPEP.Toy.FiniteGD (GradAffineQ Point)
open LeanPEP.Profiles.FixedStepFirstOrder
open LeanPEP.Profiles.GramCompilation
open LeanPEP.Profiles.Momentum
open LeanPEP.GramPEP
open LeanPEP.ActualFunction.ParametricGDHilbert (evalVector linearCombination)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual `(state, query)` recursion driven by the supplied gradient field. -/
noncomputable def iteratePair (s : ScheduleQ) (g : E → E) (x0 : E) : ℕ → E × E
  | 0 => (x0, x0)
  | k + 1 =>
      let old := iteratePair s g x0 k
      let newState := old.2 - (s.step k : ℝ) • g old.2
      (newState, newState + (s.momentum k : ℝ) • (newState - old.1))

noncomputable def state (s : ScheduleQ) (g : E → E) (x0 : E) (k : ℕ) : E :=
  (iteratePair s g x0 k).1

noncomputable def query (s : ScheduleQ) (g : E → E) (x0 : E) (k : ℕ) : E :=
  (iteratePair s g x0 k).2

@[simp] theorem state_zero (s : ScheduleQ) (g : E → E) (x0 : E) :
    state s g x0 0 = x0 := rfl

@[simp] theorem query_zero (s : ScheduleQ) (g : E → E) (x0 : E) :
    query s g x0 0 = x0 := rfl

theorem state_succ (s : ScheduleQ) (g : E → E) (x0 : E) (k : ℕ) :
    state s g x0 (k + 1) = query s g x0 k - (s.step k : ℝ) • g (query s g x0 k) := rfl

theorem query_succ (s : ScheduleQ) (g : E → E) (x0 : E) (k : ℕ) :
    query s g x0 (k + 1) = state s g x0 (k + 1) +
      (s.momentum k : ℝ) • (state s g x0 (k + 1) - state s g x0 k) := rfl

/-- External run contract.  It names the ordinary two update equations, not
compiled coefficients, Gram feasibility, or interpolation inequalities. -/
structure IsRun (N : ℕ) (s : ScheduleQ) (g : E → E) (x0 : E)
    (x y : ℕ → E) : Prop where
  state_initial : x 0 = x0
  query_initial : y 0 = x0
  step : ∀ k, k < N → x (k + 1) = y k - (s.step k : ℝ) • g (y k)
  extrapolate : ∀ k, k < N →
    y (k + 1) = x (k + 1) + (s.momentum k : ℝ) • (x (k + 1) - x k)

/-- Any externally defined run of the same recurrence agrees through its horizon. -/
theorem eq_of_isRun {N : ℕ} {s : ScheduleQ} {g : E → E} {x0 : E}
    {x y : ℕ → E} (h : IsRun N s g x0 x y) :
    ∀ k, k ≤ N → x k = state s g x0 k ∧ y k = query s g x0 k := by
  intro k
  induction k with
  | zero =>
      intro hk
      exact ⟨h.state_initial, h.query_initial⟩
  | succ k ih =>
      intro hk
      have hklt : k < N := by omega
      have hprev := ih (Nat.le_of_lt hklt)
      have hx : x (k + 1) = state s g x0 (k + 1) := by
        rw [h.step k hklt, state_succ, hprev.2]
      refine ⟨hx, ?_⟩
      rw [h.extrapolate k hklt, query_succ, hx, hprev.1]

/-- Sample queries before the final index and the STATE at the final index. -/
noncomputable def outputPoints (N : ℕ) (s : ScheduleQ) (g : E → E) (x0 : E) :
    Fin (N + 1) → E :=
  fun i => if i.val = N then state s g x0 N else query s g x0 i.val

theorem outputPoints_before_final {N : ℕ} (s : ScheduleQ) (g : E → E) (x0 : E)
    (i : Fin (N + 1)) (hi : i.val < N) :
    outputPoints N s g x0 i = query s g x0 i.val := by
  simp [outputPoints, Nat.ne_of_lt hi]

@[simp] theorem outputPoints_final (N : ℕ) (s : ScheduleQ) (g : E → E) (x0 : E) :
    outputPoints N s g x0 (Fin.last N) = state s g x0 N := by
  simp [outputPoints]

@[simp] theorem evalVector_stateAffineQ_zero {N : ℕ} (s : ScheduleQ)
    (u0 : E) (grad : Fin (N + 1) → E) :
    evalVector (stateAffineQ N s 0) u0 grad = u0 := by
  simp [stateAffineQ, evalVector, linearCombination]

@[simp] theorem evalVector_queryAffineQ_zero {N : ℕ} (s : ScheduleQ)
    (u0 : E) (grad : Fin (N + 1) → E) :
    evalVector (queryAffineQ N s 0) u0 grad = u0 := by
  simp [queryAffineQ, evalVector, linearCombination]

/-- The B1 symbolic state equation is valid in every real inner-product space. -/
theorem evalVector_stateAffineQ_succ {N : ℕ} (s : ScheduleQ) (k : Fin (N + 1))
    (u0 : E) (grad : Fin (N + 1) → E) :
    evalVector (stateAffineQ N s (k.val + 1)) u0 grad =
      evalVector (queryAffineQ N s k.val) u0 grad - (s.step k.val : ℝ) • grad k := by
  rw [stateAffineQ_succ]
  simp

/-- The B1 symbolic momentum equation is valid in the same ambient space. -/
theorem evalVector_queryAffineQ_succ {N : ℕ} (s : ScheduleQ) (k : ℕ)
    (u0 : E) (grad : Fin (N + 1) → E) :
    evalVector (queryAffineQ N s (k + 1)) u0 grad =
      evalVector (stateAffineQ N s (k + 1)) u0 grad +
        (s.momentum k : ℝ) • (evalVector (stateAffineQ N s (k + 1)) u0 grad -
          evalVector (stateAffineQ N s k) u0 grad) := by
  rw [queryAffineQ_succ]
  simp

/-- Both actual sequences realize their compiled affine expressions.  Sampling
the terminal state rather than the unused final query does not alter any update. -/
theorem affineTrajectory_realization (N : ℕ) (s : ScheduleQ)
    (g : E → E) (xStar x0 : E) :
    ∀ k, k ≤ N →
      evalVector (stateAffineQ N s k) (x0 - xStar)
          (fun i => g (outputPoints N s g x0 i)) = state s g x0 k - xStar ∧
      evalVector (queryAffineQ N s k) (x0 - xStar)
          (fun i => g (outputPoints N s g x0 i)) = query s g x0 k - xStar := by
  intro k
  induction k with
  | zero =>
      intro hk
      constructor <;> simp
  | succ k ih =>
      intro hk
      have hklt : k < N := by omega
      have hprev := ih (Nat.le_of_lt hklt)
      let i : Fin (N + 1) := ⟨k, by omega⟩
      have hi : i.val < N := hklt
      have hx :
          evalVector (stateAffineQ N s (k + 1)) (x0 - xStar)
              (fun j => g (outputPoints N s g x0 j)) = state s g x0 (k + 1) - xStar := by
        have hstep := evalVector_stateAffineQ_succ s i (x0 - xStar)
          (fun j => g (outputPoints N s g x0 j))
        rw [hprev.2, outputPoints_before_final s g x0 i hi] at hstep
        calc
          _ = (query s g x0 k - xStar) - (s.step k : ℝ) • g (query s g x0 k) := hstep
          _ = state s g x0 (k + 1) - xStar := by
            rw [state_succ]
            abel
      refine ⟨hx, ?_⟩
      rw [evalVector_queryAffineQ_succ, hx, hprev.1, query_succ]
      have hdiff :
          (state s g x0 (k + 1) - xStar) - (state s g x0 k - xStar) =
            state s g x0 (k + 1) - state s g x0 k := by abel
      rw [hdiff]
      abel

/-- Actual output samples meet the generic profile realization contract. -/
theorem outputPoints_realizesProfile (N : ℕ) (s : ScheduleQ)
    (g : E → E) (xStar x0 : E) :
    ProfileGram.RealizesProfile (outputProfileQ N s) g xStar x0
      (outputPoints N s g x0) := by
  intro i
  by_cases hi : i.val = N
  · have hieq : i = Fin.last N := Fin.ext (by simpa using hi)
    subst i
    rw [iterateAffineQ_outputProfileQ_final, outputPoints_final]
    exact (affineTrajectory_realization N s g xStar x0 N (le_refl N)).1
  · have hiN : i.val < N := by
      have hbound := i.isLt
      omega
    rw [iterateAffineQ_outputProfileQ_before_final s i hiN,
      outputPoints_before_final s g x0 i hiN]
    exact (affineTrajectory_realization N s g xStar x0 i.val (Nat.le_of_lt hiN)).2

/-- Momentum samples use the generic profile Gram datum verbatim. -/
noncomputable def outputData (N : ℕ) (s : ScheduleQ)
    (normalization : NormalizationProfileQ)
    (f : E → ℝ) (g : E → E) (xStar x0 : E) : DataR (Fin (N + 2)) (N + 2) :=
  ProfileGram.profileData (outputPEPProfileQ N s normalization) f g xStar x0
    (outputPoints N s g x0)

/-- Full finite feasibility of the compiler-generated momentum formulation. -/
theorem outputData_feasible (N : ℕ) (s : ScheduleQ)
    (normalization : NormalizationProfileQ)
    {f : E → ℝ} {g : E → E} {xStar x0 : E}
    (hfun : IsOneSmoothConvexFirstOrder f g)
    (hstationary : g xStar = 0)
    (hradius : ‖x0 - xStar‖ ^ 2 ≤ (normalization.radiusSq : ℝ)) :
    RealizesModelQ (outputModelQ N s normalization)
        (outputData N s normalization f g xStar x0) ∧
      CoreFeasible (outputData N s normalization f g xStar x0) ∧
      AssumptionsFeasibleR (outputModelQ N s normalization)
        (outputData N s normalization f g xStar x0) :=
  ProfileGram.profileData_feasible (outputPEPProfileQ N s normalization)
    hfun hstationary (outputPoints_realizesProfile N s g xStar x0) hradius

/-- The datum's objective is the ACTUAL final-state gap, not the final-query gap. -/
@[simp] theorem outputData_objective_eval (N : ℕ) (s : ScheduleQ)
    (normalization : NormalizationProfileQ)
    (f : E → ℝ) (g : E → E) (xStar x0 : E) :
    (outputObjectiveQ N s normalization).evalR
        (outputData N s normalization f g xStar x0) =
      f (state s g x0 N) - f xStar := by
  change (compileObjectiveQ (outputPEPProfileQ N s normalization)).evalR
    (ProfileGram.profileData _ f g xStar x0 (outputPoints N s g x0)) = _
  rw [ProfileGram.profileData_objective_eval]
  change f (outputPoints N s g x0 (Fin.last N)) - f xStar = _
  rw [outputPoints_final]

/-- Generic actual momentum upper theorem from any accepted general certificate. -/
theorem certificate_upper {N : ℕ} {s : ScheduleQ}
    {normalization : NormalizationProfileQ}
    (c : GramPEP.UpperCertQ (outputModelQ N s normalization))
    (hcheck : GramPEP.checkUpperCertQ c = true)
    (hobjective : c.objective = outputObjectiveQ N s normalization)
    {f : E → ℝ} {g : E → E} {xStar x0 : E}
    (hfun : IsOneSmoothConvexFirstOrder f g)
    (hstationary : g xStar = 0)
    (hradius : ‖x0 - xStar‖ ^ 2 ≤ (normalization.radiusSq : ℝ)) :
    f (state s g x0 N) - f xStar ≤ (c.bound : ℝ) := by
  have hbound := ProfileGram.certificate_upper (outputPEPProfileQ N s normalization)
    c hcheck hobjective hfun hstationary (outputPoints_realizesProfile N s g xStar x0) hradius
  change f (outputPoints N s g x0 (Fin.last N)) - f xStar ≤ (c.bound : ℝ) at hbound
  rw [outputPoints_final] at hbound
  exact hbound

/-- Analysis-facing version for any rational schedule and matching certificate. -/
theorem certificate_upper_analytic {N : ℕ} [CompleteSpace E] {s : ScheduleQ}
    {normalization : NormalizationProfileQ}
    (c : GramPEP.UpperCertQ (outputModelQ N s normalization))
    (hcheck : GramPEP.checkUpperCertQ c = true)
    (hobjective : c.objective = outputObjectiveQ N s normalization)
    {f : E → ℝ} {g : E → E} {xStar x0 : E}
    (hfun : IsOneSmoothConvexAnalytic f g)
    (hstationary : g xStar = 0)
    (hradius : ‖x0 - xStar‖ ^ 2 ≤ (normalization.radiusSq : ℝ)) :
    f (state s g x0 N) - f xStar ≤ (c.bound : ℝ) :=
  certificate_upper c hcheck hobjective hfun.toFirstOrder hstationary hradius

/-- A caller need not use our recursive definition: its external run suffices. -/
theorem certificate_upper_of_isRun {N : ℕ} {s : ScheduleQ}
    {normalization : NormalizationProfileQ}
    (c : GramPEP.UpperCertQ (outputModelQ N s normalization))
    (hcheck : GramPEP.checkUpperCertQ c = true)
    (hobjective : c.objective = outputObjectiveQ N s normalization)
    {f : E → ℝ} {g : E → E} {xStar x0 : E} {x y : ℕ → E}
    (hfun : IsOneSmoothConvexFirstOrder f g)
    (hstationary : g xStar = 0)
    (hradius : ‖x0 - xStar‖ ^ 2 ≤ (normalization.radiusSq : ℝ))
    (hrun : IsRun N s g x0 x y) :
    f (x N) - f xStar ≤ (c.bound : ℝ) := by
  rw [(eq_of_isRun hrun N (le_refl N)).1]
  exact certificate_upper c hcheck hobjective hfun hstationary hradius

end LeanPEP.ActualFunction.MomentumActual
