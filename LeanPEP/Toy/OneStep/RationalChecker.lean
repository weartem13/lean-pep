import LeanPEP.Toy.OneStep.RationalData

/-!
# Executable exact rational checker

`checkFeasibleQ` enumerates all nine ordered interpolation constraints.  The
checker is executable because all arithmetic is over `ℚ`.  The soundness and
completeness theorems connect its Boolean result to the proposition-level
finite PEP semantics.
-/

namespace LeanPEP
namespace Toy
namespace OneStep

/-- Check all ordered pairs in `pts × pts` using exact rational arithmetic. -/
def checkFeasibleQ (d : OneStepDataQ) : Bool :=
  pts.all (fun i =>
    pts.all (fun j => decide (0 ≤ slackQ d i j)))

/-- A successful Boolean check proves every rational interpolation inequality. -/
theorem checkFeasibleQ_sound
    (d : OneStepDataQ)
    (h : checkFeasibleQ d = true) :
    OneStepFeasibleQ d := by
  constructor
  intro i j
  cases i <;> cases j <;>
    simp_all [checkFeasibleQ, pts]

/-- Proposition-level rational feasibility makes the Boolean checker succeed. -/
theorem checkFeasibleQ_complete
    (d : OneStepDataQ)
    (h : OneStepFeasibleQ d) :
    checkFeasibleQ d = true := by
  simp [checkFeasibleQ, pts, h.interp]

/-- The executable checker exactly decides rational finite PEP feasibility. -/
theorem checkFeasibleQ_eq_true_iff (d : OneStepDataQ) :
    checkFeasibleQ d = true ↔ OneStepFeasibleQ d := by
  constructor
  · exact checkFeasibleQ_sound d
  · exact checkFeasibleQ_complete d

/-- The exact rational witness is accepted by computation. -/
theorem exactWitnessQ_check :
    checkFeasibleQ exactWitnessQ = true := by
  native_decide

/-- The invalid rational pseudo-certificate is rejected by computation. -/
theorem pseudoCertQ_check :
    checkFeasibleQ pseudoCertQ = false := by
  native_decide

/-- The accepted exact witness is propositionally feasible. -/
theorem exactWitnessQ_feasible :
    OneStepFeasibleQ exactWitnessQ :=
  checkFeasibleQ_sound exactWitnessQ exactWitnessQ_check

/-- A concrete failed constraint returned by the diagnostic layer. -/
structure ViolationQ where
  i : Pt
  j : Pt
  value : ℚ
  deriving DecidableEq, Repr

/-- All ordered point pairs, in deterministic row-major order. -/
def pointPairs : List (Pt × Pt) :=
  pts.flatMap (fun i => pts.map (fun j => (i, j)))

/-- Scan a list of point pairs and return the first negative slack. -/
def firstViolationFromQ
    (d : OneStepDataQ) : List (Pt × Pt) → Option ViolationQ
  | [] => none
  | (i, j) :: rest =>
      let s := slackQ d i j
      if s < 0 then
        some { i := i, j := j, value := s }
      else
        firstViolationFromQ d rest

/-- Return the first violated interpolation inequality, if one exists. -/
def firstViolationQ (d : OneStepDataQ) : Option ViolationQ :=
  firstViolationFromQ d pointPairs


/-- Any diagnostic result returned by the list scanner names its exact slack,
and that slack is strictly negative. -/
theorem firstViolationFromQ_some_sound
    (d : OneStepDataQ)
    (pairs : List (Pt × Pt))
    (v : ViolationQ)
    (h : firstViolationFromQ d pairs = some v) :
    v.value = slackQ d v.i v.j ∧ v.value < 0 := by
  induction pairs generalizing v with
  | nil =>
      simp [firstViolationFromQ] at h
  | cons head rest ih =>
      rcases head with ⟨i, j⟩
      by_cases hs : slackQ d i j < 0
      · have hv :
          ({ i := i, j := j, value := slackQ d i j } : ViolationQ) = v := by
            simpa [firstViolationFromQ, hs] using h
        subst v
        exact ⟨rfl, hs⟩
      · have hrest : firstViolationFromQ d rest = some v := by
          simpa [firstViolationFromQ, hs] using h
        exact ih v hrest

/-- Any result returned by `firstViolationQ` is a genuine violated constraint. -/
theorem firstViolationQ_some_sound
    (d : OneStepDataQ)
    (v : ViolationQ)
    (h : firstViolationQ d = some v) :
    v.value = slackQ d v.i v.j ∧ v.value < 0 := by
  exact firstViolationFromQ_some_sound d pointPairs v h

/-- A returned violation is an exact proof that the rational datum is infeasible. -/
theorem firstViolationQ_some_not_feasible
    (d : OneStepDataQ)
    (v : ViolationQ)
    (h : firstViolationQ d = some v) :
    ¬ OneStepFeasibleQ d := by
  intro hfeasible
  rcases firstViolationQ_some_sound d v h with ⟨hvalue, hnegative⟩
  have hnonnegative : 0 ≤ v.value := by
    rw [hvalue]
    exact hfeasible.interp v.i v.j
  exact (not_lt_of_ge hnonnegative) hnegative

/-- The exact witness has no violated rational constraint. -/
theorem exactWitnessQ_no_violation :
    firstViolationQ exactWitnessQ = none := by
  native_decide

/-- In row-major order, the pseudo-certificate first fails at `(star, p1)`. -/
theorem pseudoCertQ_first_violation :
    firstViolationQ pseudoCertQ =
      some
        { i := Pt.star
          j := Pt.p1
          value := -((1 : ℚ) / 4) } := by
  native_decide

/-- The previously highlighted `(p0, p1)` slack is also exactly `-1 / 4`. -/
theorem pseudoCertQ_p0_p1_slack :
    slackQ pseudoCertQ Pt.p0 Pt.p1 = -((1 : ℚ) / 4) := by
  norm_num [slackQ, xQ, gradQ, valQ, pseudoCertQ]

end OneStep
end Toy
end LeanPEP
