import LeanPEP.Toy.OneStep.RationalChecker

/-!
# Complete exact rational primal audit reports

The earlier diagnostic returned only the first violated interpolation inequality.
This file adds a complete report containing every negative rational slack, while
retaining a Boolean acceptance field whose meaning is already proved equivalent
to proposition-level finite PEP feasibility.
-/

namespace LeanPEP
namespace Toy
namespace OneStep

/-- Scan a supplied list of ordered point pairs and retain every negative slack. -/
def violationsFromQ
    (d : OneStepDataQ) : List (Pt × Pt) → List ViolationQ
  | [] => []
  | (i, j) :: rest =>
      let s := slackQ d i j
      if s < 0 then
        { i := i, j := j, value := s } :: violationsFromQ d rest
      else
        violationsFromQ d rest

/-- Every violated interpolation inequality, in deterministic row-major order. -/
def allViolationsQ (d : OneStepDataQ) : List ViolationQ :=
  violationsFromQ d pointPairs

/-- Every item returned by the complete scanner is the named exact slack and is
strictly negative. -/
theorem mem_violationsFromQ_sound
    (d : OneStepDataQ)
    (pairs : List (Pt × Pt))
    (v : ViolationQ)
    (h : v ∈ violationsFromQ d pairs) :
    v.value = slackQ d v.i v.j ∧ v.value < 0 := by
  induction pairs with
  | nil =>
      simp [violationsFromQ] at h
  | cons head rest ih =>
      rcases head with ⟨i, j⟩
      by_cases hs : slackQ d i j < 0
      · simp [violationsFromQ, hs] at h
        rcases h with h | h
        · subst v
          exact ⟨rfl, hs⟩
        · exact ih h
      · have hrest : v ∈ violationsFromQ d rest := by
          simpa [violationsFromQ, hs] using h
        exact ih hrest

/-- Every item in `allViolationsQ` is a genuine violated constraint. -/
theorem mem_allViolationsQ_sound
    (d : OneStepDataQ)
    (v : ViolationQ)
    (h : v ∈ allViolationsQ d) :
    v.value = slackQ d v.i v.j ∧ v.value < 0 := by
  exact mem_violationsFromQ_sound d pointPairs v h

/-- Any negative slack whose ordered pair occurs in the scan list is included
in the result. -/
theorem mem_violationsFromQ_of_mem_of_negative
    (d : OneStepDataQ)
    (pairs : List (Pt × Pt))
    (i j : Pt)
    (hpair : (i, j) ∈ pairs)
    (hnegative : slackQ d i j < 0) :
    ({ i := i, j := j, value := slackQ d i j } : ViolationQ) ∈
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
        by_cases hab : slackQ d a b < 0
        · simp [violationsFromQ, hab, ih hrest]
        · simpa [violationsFromQ, hab] using ih hrest

/-- Every ordered pair of the finite point type occurs in `pointPairs`. -/
theorem mem_pointPairs (i j : Pt) : (i, j) ∈ pointPairs := by
  cases i <;> cases j <;>
    simp [pointPairs, pts]

/-- Every negative interpolation slack appears in the complete report. -/
theorem mem_allViolationsQ_of_negative
    (d : OneStepDataQ)
    (i j : Pt)
    (hnegative : slackQ d i j < 0) :
    ({ i := i, j := j, value := slackQ d i j } : ViolationQ) ∈
      allViolationsQ d := by
  exact mem_violationsFromQ_of_mem_of_negative
    d pointPairs i j (mem_pointPairs i j) hnegative

/-- A propositionally feasible datum produces no entries in the complete
violation report. -/
theorem violationsFromQ_eq_nil_of_feasible
    (d : OneStepDataQ)
    (h : OneStepFeasibleQ d) :
    ∀ pairs : List (Pt × Pt), violationsFromQ d pairs = []
  | [] => rfl
  | (i, j) :: rest => by
      have hnot : ¬ slackQ d i j < 0 := not_lt_of_ge (h.interp i j)
      simp [violationsFromQ, hnot, violationsFromQ_eq_nil_of_feasible d h rest]

/-- A feasible datum has an empty complete violation report. -/
theorem allViolationsQ_eq_nil_of_feasible
    (d : OneStepDataQ)
    (h : OneStepFeasibleQ d) :
    allViolationsQ d = [] := by
  exact violationsFromQ_eq_nil_of_feasible d h pointPairs

/-- The complete report is empty exactly for feasible rational data. -/
theorem allViolationsQ_eq_nil_iff
    (d : OneStepDataQ) :
    allViolationsQ d = [] ↔ OneStepFeasibleQ d := by
  constructor
  · intro hempty
    constructor
    intro i j
    by_contra hnonnegative
    have hnegative : slackQ d i j < 0 := lt_of_not_ge hnonnegative
    have hmem := mem_allViolationsQ_of_negative d i j hnegative
    rw [hempty] at hmem
    simp at hmem
  · exact allViolationsQ_eq_nil_of_feasible d

/-- Executable primal audit output: the decision and all exact violations. -/
structure PrimalAuditReportQ where
  accepted : Bool
  violations : List ViolationQ
  deriving DecidableEq, Repr

/-- Audit one rational primal candidate. -/
def auditPrimalQ (d : OneStepDataQ) : PrimalAuditReportQ :=
  { accepted := checkFeasibleQ d
    violations := allViolationsQ d }

/-- The acceptance field has exactly the proposition-level feasibility meaning. -/
theorem auditPrimalQ_accepted_iff
    (d : OneStepDataQ) :
    (auditPrimalQ d).accepted = true ↔ OneStepFeasibleQ d := by
  simpa [auditPrimalQ] using checkFeasibleQ_eq_true_iff d

/-- The report is accepted exactly when its complete violation list is empty. -/
theorem auditPrimalQ_accepted_iff_no_violations
    (d : OneStepDataQ) :
    (auditPrimalQ d).accepted = true ↔
      (auditPrimalQ d).violations = [] := by
  rw [auditPrimalQ_accepted_iff]
  simpa [auditPrimalQ] using (allViolationsQ_eq_nil_iff d).symm

/-- Every violation appearing in an audit report is genuine. -/
theorem auditPrimalQ_violation_sound
    (d : OneStepDataQ)
    (v : ViolationQ)
    (h : v ∈ (auditPrimalQ d).violations) :
    v.value = slackQ d v.i v.j ∧ v.value < 0 := by
  exact mem_allViolationsQ_sound d v h

/-- An accepted report contains no violations. -/
theorem auditPrimalQ_accepted_no_violations
    (d : OneStepDataQ)
    (h : (auditPrimalQ d).accepted = true) :
    (auditPrimalQ d).violations = [] := by
  have hfeasible : OneStepFeasibleQ d :=
    (auditPrimalQ_accepted_iff d).mp h
  simpa [auditPrimalQ] using allViolationsQ_eq_nil_of_feasible d hfeasible

/-- The exact witness is accepted and has an empty report. -/
theorem exactWitnessQ_audit :
    auditPrimalQ exactWitnessQ =
      { accepted := true, violations := [] } := by
  native_decide

/-- The pseudo-certificate is rejected and both negative slacks are reported. -/
theorem pseudoCertQ_audit :
    auditPrimalQ pseudoCertQ =
      { accepted := false
        violations :=
          [ { i := Pt.star
              j := Pt.p1
              value := -((1 : ℚ) / 4) }
          , { i := Pt.p0
              j := Pt.p1
              value := -((1 : ℚ) / 4) } ] } := by
  native_decide

end OneStep
end Toy
end LeanPEP
