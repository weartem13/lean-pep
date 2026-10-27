import LeanPEP.ActualFunction.MomentumActual

/-!
# Finite-horizon oracle agreement for actual momentum runs

If two fields agree at the reference run's queried points before the horizon,
then their state and query sequences agree through the horizon.  This is a
structural statement for every rational schedule and every real inner-product
space; it requires neither smoothness nor a certificate.

In particular, it is useful for proving that a clipped gradient follows a
constant-field reference run.  No agreement is required at the unqueried final
state.  Equality of `outputPoints` does NOT assert equality of the terminal
gradient observation or of the entire Gram datum.
-/

namespace LeanPEP.ActualFunction.MomentumActual

open LeanPEP.Profiles.Momentum (ScheduleQ)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The reference trajectory satisfies the ordinary run equations for the
second oracle whenever both fields agree on all queries that drive updates. -/
theorem isRun_of_oracle_eq_on_queries
    (N : ℕ) (s : ScheduleQ) (g g' : E → E) (x0 : E)
    (hqueries : ∀ k, k < N → g' (query s g x0 k) = g (query s g x0 k)) :
    IsRun N s g' x0 (state s g x0) (query s g x0) where
  state_initial := state_zero s g x0
  query_initial := query_zero s g x0
  step := by
    intro k hk
    rw [state_succ, hqueries k hk]
  extrapolate := by
    intro k _
    exact query_succ s g x0 k

/-- Oracle agreement at reference queries implies equality of both actual
sequences, including the final state and the unused final extrapolation. -/
theorem eq_of_oracle_eq_on_queries
    (N : ℕ) (s : ScheduleQ) (g g' : E → E) (x0 : E)
    (hqueries : ∀ k, k < N → g' (query s g x0 k) = g (query s g x0 k))
    (k : ℕ) (hk : k ≤ N) :
    state s g' x0 k = state s g x0 k ∧
      query s g' x0 k = query s g x0 k := by
  have h := eq_of_isRun
    (isRun_of_oracle_eq_on_queries N s g g' x0 hqueries) k hk
  exact ⟨h.1.symm, h.2.symm⟩

/-- The compiler's selected sample positions agree too.  This does not claim
that the two oracles have equal observations at the final state. -/
theorem outputPoints_eq_of_oracle_eq_on_queries
    (N : ℕ) (s : ScheduleQ) (g g' : E → E) (x0 : E)
    (hqueries : ∀ k, k < N → g' (query s g x0 k) = g (query s g x0 k)) :
    outputPoints N s g' x0 = outputPoints N s g x0 := by
  funext i
  unfold outputPoints
  split_ifs with hi
  · exact (eq_of_oracle_eq_on_queries N s g g' x0 hqueries N (le_refl N)).1
  · exact (eq_of_oracle_eq_on_queries N s g g' x0 hqueries
      i.val (Nat.le_of_lt_succ i.isLt)).2

end LeanPEP.ActualFunction.MomentumActual
