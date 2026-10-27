import LeanPEP.GramPEP.UpperCertificateChecker

/-! D10: independently checked exact linear-system solutions and obstructions.
The row-reduction implementation and the source-to-matrix compiler are not
trusted here. The original upper checker still verifies completed certificates.
An obstruction concerns this submitted system, not general PEP infeasibility. -/
namespace LeanPEP.GramPEP.RationalLinearSystem
open scoped BigOperators

structure SystemQ (r c : ℕ) where
  matrix : Fin r → Fin c → ℚ
  rhs : Fin r → ℚ

def IsSolutionQ {r c : ℕ} (s : SystemQ r c) (x : Fin c → ℚ) : Prop :=
  ∀ i, (∑ j, s.matrix i j * x j) = s.rhs i

def checkSolutionQ {r c : ℕ} (s : SystemQ r c) (x : Fin c → ℚ) : Bool :=
  (List.finRange r).all fun i => decide ((∑ j, s.matrix i j * x j) = s.rhs i)

theorem checkSolutionQ_eq_true_iff {r c : ℕ} (s : SystemQ r c) (x : Fin c → ℚ) :
    checkSolutionQ s x = true ↔ IsSolutionQ s x := by
  simp [checkSolutionQ, IsSolutionQ, List.all_eq_true]

def IsObstructionQ {r c : ℕ} (s : SystemQ r c) (y : Fin r → ℚ) : Prop :=
  (∀ j, (∑ i, y i * s.matrix i j) = 0) ∧ (∑ i, y i * s.rhs i) ≠ 0

def checkObstructionQ {r c : ℕ} (s : SystemQ r c) (y : Fin r → ℚ) : Bool :=
  ((List.finRange c).all fun j => decide ((∑ i, y i * s.matrix i j) = 0)) &&
    decide ((∑ i, y i * s.rhs i) ≠ 0)

theorem checkObstructionQ_eq_true_iff {r c : ℕ} (s : SystemQ r c) (y : Fin r → ℚ) :
    checkObstructionQ s y = true ↔ IsObstructionQ s y := by
  simp [checkObstructionQ, IsObstructionQ, List.all_eq_true]

theorem obstruction_not_solution {r c : ℕ} (s : SystemQ r c) (y : Fin r → ℚ)
    (hy : IsObstructionQ s y) : ¬ ∃ x, IsSolutionQ s x := by
  rintro ⟨x, hx⟩
  apply hy.2
  calc
    (∑ i, y i * s.rhs i) = ∑ i, y i * (∑ j, s.matrix i j * x j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hx i]
    _ = ∑ j, (∑ i, y i * s.matrix i j) * x j := by
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = 0 := by simp [hy.1]

theorem checked_obstruction {r c : ℕ} (s : SystemQ r c) (y : Fin r → ℚ)
    (hy : checkObstructionQ s y = true) : ¬ ∃ x, IsSolutionQ s x :=
  obstruction_not_solution s y ((checkObstructionQ_eq_true_iff s y).mp hy)

end LeanPEP.GramPEP.RationalLinearSystem
