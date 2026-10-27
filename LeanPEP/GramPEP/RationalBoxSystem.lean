import LeanPEP.GramPEP.RationalLinearSystem

/-! D11: exact feasibility and Farkas obstructions for a rational linear system
with finite lower/upper bounds. The phase-I solver is untrusted. An obstruction
concerns this submitted system and box, not arbitrary PEP certificates.
No bounded-denominator search, optimality or algorithm termination is claimed. -/
namespace LeanPEP.GramPEP.RationalBoxSystem
open scoped BigOperators
open RationalLinearSystem (SystemQ IsSolutionQ)

structure BoxQ (r c : ℕ) where
  system : SystemQ r c
  lower : Fin c → ℚ
  upper : Fin c → ℚ

def FeasibleQ {r c : ℕ} (s : BoxQ r c) (x : Fin c → ℚ) : Prop :=
  IsSolutionQ s.system x ∧ ∀ j, s.lower j ≤ x j ∧ x j ≤ s.upper j

def checkFeasibleQ {r c : ℕ} (s : BoxQ r c) (x : Fin c → ℚ) : Bool :=
  RationalLinearSystem.checkSolutionQ s.system x &&
    (List.finRange c).all (fun j => decide (s.lower j ≤ x j ∧ x j ≤ s.upper j))

theorem checkFeasibleQ_eq_true_iff {r c : ℕ} (s : BoxQ r c) (x : Fin c → ℚ) :
    checkFeasibleQ s x = true ↔ FeasibleQ s x := by
  simp [checkFeasibleQ, FeasibleQ, RationalLinearSystem.checkSolutionQ_eq_true_iff,
    List.all_eq_true]

structure ObstructionQ (r c : ℕ) where
  equality : Fin r → ℚ
  lower : Fin c → ℚ
  upper : Fin c → ℚ

def marginQ {r c : ℕ} (s : BoxQ r c) (w : ObstructionQ r c) : ℚ :=
  (∑ i, w.equality i * s.system.rhs i) +
    ∑ j, (w.upper j * s.upper j - w.lower j * s.lower j)

def IsObstructionQ {r c : ℕ} (s : BoxQ r c) (w : ObstructionQ r c) : Prop :=
  (∀ j, 0 ≤ w.lower j ∧ 0 ≤ w.upper j) ∧
  (∀ j, (∑ i, w.equality i * s.system.matrix i j) + w.upper j - w.lower j = 0) ∧
  marginQ s w < 0

def checkObstructionQ {r c : ℕ} (s : BoxQ r c) (w : ObstructionQ r c) : Bool :=
  ((List.finRange c).all fun j => decide (0 ≤ w.lower j ∧ 0 ≤ w.upper j)) &&
  ((List.finRange c).all fun j =>
    decide ((∑ i, w.equality i * s.system.matrix i j) + w.upper j - w.lower j = 0)) &&
  decide (marginQ s w < 0)

theorem checkObstructionQ_eq_true_iff {r c : ℕ} (s : BoxQ r c) (w : ObstructionQ r c) :
    checkObstructionQ s w = true ↔ IsObstructionQ s w := by
  simp [checkObstructionQ, IsObstructionQ, List.all_eq_true, and_assoc]

/-- Weak duality, without sign or strict-negativity assumptions. -/
theorem margin_eq_slacks {r c : ℕ} (s : BoxQ r c) (w : ObstructionQ r c)
    (x : Fin c → ℚ) (hx : IsSolutionQ s.system x)
    (hcancel : ∀ j, (∑ i, w.equality i * s.system.matrix i j) +
      w.upper j - w.lower j = 0) :
    marginQ s w = ∑ j, (w.lower j * (x j - s.lower j) +
      w.upper j * (s.upper j - x j)) := by
  have heq : (∑ i, w.equality i * s.system.rhs i) =
      ∑ j, (∑ i, w.equality i * s.system.matrix i j) * x j := by
    calc
      (∑ i, w.equality i * s.system.rhs i) =
          ∑ i, w.equality i * (∑ j, s.system.matrix i j * x j) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hx i]
      _ = ∑ j, (∑ i, w.equality i * s.system.matrix i j) * x j := by
        simp_rw [Finset.mul_sum, ← mul_assoc]
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
  unfold marginQ
  rw [heq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hc := hcancel j
  have hs : (∑ i, w.equality i * s.system.matrix i j) = w.lower j - w.upper j := by
    linarith only [hc]
  rw [hs]
  ring

theorem obstruction_not_feasible {r c : ℕ} (s : BoxQ r c) (w : ObstructionQ r c)
    (hw : IsObstructionQ s w) : ¬ ∃ x, FeasibleQ s x := by
  rintro ⟨x, hx, hbox⟩
  have hnonneg : 0 ≤ marginQ s w := by
    rw [margin_eq_slacks s w x hx hw.2.1]
    apply Finset.sum_nonneg
    intro j hj
    exact add_nonneg (mul_nonneg (hw.1 j).1 (sub_nonneg.mpr (hbox j).1))
      (mul_nonneg (hw.1 j).2 (sub_nonneg.mpr (hbox j).2))
  exact (not_lt_of_ge hnonneg) hw.2.2

theorem checked_obstruction {r c : ℕ} (s : BoxQ r c) (w : ObstructionQ r c)
    (hw : checkObstructionQ s w = true) : ¬ ∃ x, FeasibleQ s x :=
  obstruction_not_feasible s w ((checkObstructionQ_eq_true_iff s w).mp hw)

/-- The bound coordinate has no sign restriction; each multiplier does. -/
def policyLowerQ {c : ℕ} (raw : Fin c → ℚ) (eta : ℚ) (nonnegative : Fin c → Bool)
    (j : Fin c) : ℚ :=
  if nonnegative j then max 0 (raw j - eta) else raw j - eta

def policyUpperQ {c : ℕ} (raw : Fin c → ℚ) (eta : ℚ) (j : Fin c) : ℚ := raw j + eta

theorem policy_interval_iff {c : ℕ} (raw : Fin c → ℚ) (eta : ℚ)
    (nonnegative : Fin c → Bool) (j : Fin c) (v : ℚ) :
    (policyLowerQ raw eta nonnegative j ≤ v ∧ v ≤ policyUpperQ raw eta j) ↔
      |v - raw j| ≤ eta ∧ (nonnegative j = true → 0 ≤ v) := by
  have herr : (raw j - eta ≤ v ∧ v ≤ raw j + eta) ↔ |v - raw j| ≤ eta := by
    rw [abs_le]
    constructor <;> rintro ⟨hlo, hhi⟩ <;> constructor <;> linarith
  cases hsign : nonnegative j <;>
    simp [policyLowerQ, policyUpperQ, hsign, max_le_iff, ← herr,
      and_assoc, and_comm, and_left_comm]

/-- Separate the continuous box contract from denominator restrictions. -/
theorem policy_box_iff {r c : ℕ} (s : SystemQ r c) (raw x : Fin c → ℚ)
    (eta : ℚ) (nonnegative : Fin c → Bool) :
    FeasibleQ
      { system := s
        lower := policyLowerQ raw eta nonnegative
        upper := policyUpperQ raw eta } x ↔
      IsSolutionQ s x ∧ ∀ j, |x j - raw j| ≤ eta ∧ (nonnegative j = true → 0 ≤ x j) := by
  simp only [FeasibleQ, policy_interval_iff]

end LeanPEP.GramPEP.RationalBoxSystem
