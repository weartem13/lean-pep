import LeanPEP.Toy.FiniteGD.Core

/-!
# Generated exact rational checker for finite gradient-descent PEP data

The same checker works for every trajectory length `N`.  It decides all
`(N + 2)^2` ordered interpolation constraints and can return every exact
negative slack.
-/

namespace LeanPEP
namespace Toy
namespace FiniteGD

/-- Decide finite PEP feasibility using exact rational arithmetic.

The proposition `Feasible d` quantifies over all points, so rather than asking
Lean for a global `Decidable (Feasible d)` instance, the executable checker
explicitly scans the generated finite list of ordered point pairs. -/
def checkFeasibleQ {N : ℕ} (d : DataQ N) : Bool :=
  (pointPairs N).all (fun pair =>
    decide (0 ≤ slack d pair.1 pair.2))

/-- The executable checker exactly decides proposition-level feasibility. -/
theorem checkFeasibleQ_eq_true_iff {N : ℕ} (d : DataQ N) :
    checkFeasibleQ d = true ↔ Feasible d := by
  unfold checkFeasibleQ Feasible
  rw [List.all_eq_true]
  constructor
  · intro hall i j
    exact of_decide_eq_true
      (hall (i, j) (mem_pointPairs i j))
  · intro h pair _hpair
    rcases pair with ⟨i, j⟩
    exact decide_eq_true (h i j)

/-- Soundness of the generated Boolean checker. -/
theorem checkFeasibleQ_sound
    {N : ℕ} (d : DataQ N)
    (h : checkFeasibleQ d = true) :
    Feasible d :=
  (checkFeasibleQ_eq_true_iff d).mp h

/-- Completeness of the generated Boolean checker. -/
theorem checkFeasibleQ_complete
    {N : ℕ} (d : DataQ N)
    (h : Feasible d) :
    checkFeasibleQ d = true :=
  (checkFeasibleQ_eq_true_iff d).mpr h

/-- One exact violated interpolation constraint. -/
structure ViolationQ (N : ℕ) where
  i : Point N
  j : Point N
  value : ℚ
  deriving DecidableEq, Repr

/-- Scan a supplied list of ordered pairs and retain every negative slack. -/
def violationsFromQ
    {N : ℕ} (d : DataQ N) :
    List (Point N × Point N) → List (ViolationQ N)
  | [] => []
  | (i, j) :: rest =>
      let s := slack d i j
      if s < 0 then
        { i := i, j := j, value := s } :: violationsFromQ d rest
      else
        violationsFromQ d rest

/-- Every negative slack, in the deterministic finite enumeration order. -/
def allViolationsQ {N : ℕ} (d : DataQ N) : List (ViolationQ N) :=
  violationsFromQ d (pointPairs N)

/-- Every reported item is the named exact slack and is strictly negative. -/
theorem mem_violationsFromQ_sound
    {N : ℕ} (d : DataQ N)
    (pairs : List (Point N × Point N))
    (v : ViolationQ N)
    (h : v ∈ violationsFromQ d pairs) :
    v.value = slack d v.i v.j ∧ v.value < 0 := by
  induction pairs with
  | nil =>
      simp [violationsFromQ] at h
  | cons head rest ih =>
      rcases head with ⟨i, j⟩
      by_cases hs : slack d i j < 0
      · simp [violationsFromQ, hs] at h
        rcases h with h | h
        · subst v
          exact ⟨rfl, hs⟩
        · exact ih h
      · have hrest : v ∈ violationsFromQ d rest := by
          simpa [violationsFromQ, hs] using h
        exact ih hrest

/-- Every item in a complete report is a genuine violated constraint. -/
theorem mem_allViolationsQ_sound
    {N : ℕ} (d : DataQ N)
    (v : ViolationQ N)
    (h : v ∈ allViolationsQ d) :
    v.value = slack d v.i v.j ∧ v.value < 0 := by
  exact mem_violationsFromQ_sound d (pointPairs N) v h

/-- Any negative slack whose pair occurs in the scan is included. -/
theorem mem_violationsFromQ_of_mem_of_negative
    {N : ℕ} (d : DataQ N)
    (pairs : List (Point N × Point N))
    (i j : Point N)
    (hpair : (i, j) ∈ pairs)
    (hnegative : slack d i j < 0) :
    ({ i := i, j := j, value := slack d i j } : ViolationQ N) ∈
      violationsFromQ d pairs := by
  revert hpair
  induction pairs with
  | nil =>
      intro hpair
      simp at hpair
  | cons head rest ih =>
      intro hpair
      rcases head with ⟨a, b⟩
      by_cases heq : (i, j) = (a, b)
      · cases heq
        simp [violationsFromQ, hnegative]
      · have hrest : (i, j) ∈ rest := by
          simpa [heq] using hpair
        by_cases hab : slack d a b < 0
        · simp [violationsFromQ, hab, ih hrest]
        · simpa [violationsFromQ, hab] using ih hrest

/-- Every negative interpolation slack appears in the complete report. -/
theorem mem_allViolationsQ_of_negative
    {N : ℕ} (d : DataQ N)
    (i j : Point N)
    (hnegative : slack d i j < 0) :
    ({ i := i, j := j, value := slack d i j } : ViolationQ N) ∈
      allViolationsQ d := by
  exact mem_violationsFromQ_of_mem_of_negative
    d (pointPairs N) i j (mem_pointPairs i j) hnegative

/-- Feasible data produce no entries in the complete report. -/
theorem violationsFromQ_eq_nil_of_feasible
    {N : ℕ} (d : DataQ N)
    (h : Feasible d) :
    ∀ pairs : List (Point N × Point N), violationsFromQ d pairs = []
  | [] => rfl
  | (i, j) :: rest => by
      have hnot : ¬ slack d i j < 0 := not_lt_of_ge (h i j)
      simp [violationsFromQ, hnot,
        violationsFromQ_eq_nil_of_feasible d h rest]

/-- A datum is feasible exactly when its complete violation report is empty. -/
theorem allViolationsQ_eq_nil_iff
    {N : ℕ} (d : DataQ N) :
    allViolationsQ d = [] ↔ Feasible d := by
  constructor
  · intro hempty i j
    by_contra hnonnegative
    have hnegative : slack d i j < 0 := lt_of_not_ge hnonnegative
    have hmem := mem_allViolationsQ_of_negative d i j hnegative
    rw [hempty] at hmem
    simp at hmem
  · intro h
    exact violationsFromQ_eq_nil_of_feasible d h (pointPairs N)

/-- Executable generic primal-audit output. -/
structure PrimalAuditReportQ (N : ℕ) where
  accepted : Bool
  violations : List (ViolationQ N)
  deriving DecidableEq, Repr

/-- Audit one exact rational finite trajectory. -/
def auditPrimalQ {N : ℕ} (d : DataQ N) : PrimalAuditReportQ N :=
  { accepted := checkFeasibleQ d
    violations := allViolationsQ d }

/-- Acceptance has exactly the proposition-level feasibility meaning. -/
theorem auditPrimalQ_accepted_iff
    {N : ℕ} (d : DataQ N) :
    (auditPrimalQ d).accepted = true ↔ Feasible d := by
  simpa [auditPrimalQ] using checkFeasibleQ_eq_true_iff d

/-- Acceptance is equivalent to an empty complete violation report. -/
theorem auditPrimalQ_accepted_iff_no_violations
    {N : ℕ} (d : DataQ N) :
    (auditPrimalQ d).accepted = true ↔
      (auditPrimalQ d).violations = [] := by
  rw [auditPrimalQ_accepted_iff]
  simpa [auditPrimalQ] using (allViolationsQ_eq_nil_iff d).symm

end FiniteGD
end Toy
end LeanPEP
