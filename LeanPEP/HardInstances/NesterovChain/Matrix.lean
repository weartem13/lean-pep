import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The matrix of the Nesterov chain quadratic

The ambient dimension in this file is `n + 1`.  This convention gives a
nonempty coordinate type `Fin (n + 1)` while keeping the `n` adjacent edge
vectors indexed by `Fin n`.

The chain matrix is defined as an exact sum of rank-one matrices:

* one rank-one term for the first boundary coordinate;
* one term for each adjacent difference `xᵢ - xᵢ₊₁`; and
* one term for the last boundary coordinate.

Consequently its quadratic form is definitionally tied to the intended
sum-of-squares semantics.  This matrix is the Hessian structure matrix of the
explicit Nesterov-chain function; it is not a PEP Gram matrix and it is not an
array of interpolation slacks.
-/

namespace LeanPEP
namespace HardInstances
namespace NesterovChain

open scoped BigOperators Matrix
open Matrix

/-- Coordinate vectors in dimension `n + 1`. -/
abbrev Vector (n : ℕ) := Fin (n + 1) → ℝ

/-- The squared Euclidean norm, written without a square root. -/
def normSq {n : ℕ} (x : Vector n) : ℝ :=
  ∑ i, (x i) ^ 2

/-- The first standard basis vector. -/
def firstBasis (n : ℕ) : Vector n :=
  Pi.single 0 1

/-- The last standard basis vector. -/
def lastBasis (n : ℕ) : Vector n :=
  Pi.single (Fin.last n) 1

/-- The oriented incidence vector `eᵢ - eᵢ₊₁`. -/
def edgeBasis {n : ℕ} (i : Fin n) : Vector n :=
  Pi.single i.castSucc 1 - Pi.single i.succ 1

/-- The adjacent coordinate difference `xᵢ - xᵢ₊₁`. -/
def edgeDiff {n : ℕ} (x : Vector n) (i : Fin n) : ℝ :=
  x i.castSucc - x i.succ

/-- The polarized chain energy. -/
def energyInner {n : ℕ} (x y : Vector n) : ℝ :=
  x 0 * y 0
    + ∑ i, edgeDiff x i * edgeDiff y i
    + x (Fin.last n) * y (Fin.last n)

/-- The chain quadratic energy

`x₀² + ∑ᵢ (xᵢ - xᵢ₊₁)² + x_last²`.
-/
def energy {n : ℕ} (x : Vector n) : ℝ :=
  (x 0) ^ 2
    + ∑ i, (edgeDiff x i) ^ 2
    + (x (Fin.last n)) ^ 2

/-- A symmetric rank-one matrix. -/
def rankOne {n : ℕ} (u : Vector n) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.vecMulVec u u

/-- The Nesterov chain matrix in dimension `n + 1`.

This factorized definition is exactly the matrix whose quadratic form is the
chain energy.  Equivalently, it is the tridiagonal matrix with diagonal `2`
and adjacent off-diagonal entries `-1`.
-/
def chainMatrix (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  rankOne (firstBasis n)
    + (∑ i : Fin n, rankOne (edgeBasis i))
    + rankOne (lastBasis n)

/-- Bilinear evaluation of a matrix. -/
def bilinearForm {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (x y : Vector n) : ℝ :=
  x ⬝ᵥ (A *ᵥ y)

/-- Quadratic evaluation of a matrix. -/
def quadraticForm {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (x : Vector n) : ℝ :=
  bilinearForm A x x

@[simp] theorem firstBasis_dot {n : ℕ} (x : Vector n) :
    firstBasis n ⬝ᵥ x = x 0 := by
  simp [firstBasis]

@[simp] theorem lastBasis_dot {n : ℕ} (x : Vector n) :
    lastBasis n ⬝ᵥ x = x (Fin.last n) := by
  simp [lastBasis]

@[simp] theorem edgeBasis_dot {n : ℕ} (i : Fin n) (x : Vector n) :
    edgeBasis i ⬝ᵥ x = edgeDiff x i := by
  simp [edgeBasis, edgeDiff]

@[simp] theorem edgeDiff_add {n : ℕ} (x y : Vector n) (i : Fin n) :
    edgeDiff (x + y) i = edgeDiff x i + edgeDiff y i := by
  simp [edgeDiff]
  ring

@[simp] theorem edgeDiff_neg {n : ℕ} (x : Vector n) (i : Fin n) :
    edgeDiff (-x) i = -edgeDiff x i := by
  simp [edgeDiff]
  ring

@[simp] theorem edgeDiff_sub {n : ℕ} (x y : Vector n) (i : Fin n) :
    edgeDiff (x - y) i = edgeDiff x i - edgeDiff y i := by
  simp [edgeDiff]
  ring

/-- Adjacent differences telescope. -/
theorem sum_edgeDiff {n : ℕ} (x : Vector n) :
    (∑ i : Fin n, edgeDiff x i) = x 0 - x (Fin.last n) := by
  have hcast := Fin.sum_univ_castSucc x
  have hsucc := Fin.sum_univ_succ x
  simp only [edgeDiff, Finset.sum_sub_distrib]
  linarith

@[simp] theorem energy_eq_energyInner {n : ℕ} (x : Vector n) :
    energy x = energyInner x x := by
  simp [energy, energyInner, pow_two]

/-- The polarized energy is symmetric. -/
theorem energyInner_comm {n : ℕ} (x y : Vector n) :
    energyInner x y = energyInner y x := by
  simp [energyInner, mul_comm]

/-- Exact polarization identity for the chain energy. -/
theorem energy_add {n : ℕ} (x y : Vector n) :
    energy (x + y) = energy x + 2 * energyInner x y + energy y := by
  have hedge :
      (∑ i : Fin n, (edgeDiff (x + y) i) ^ 2)
        = (∑ i : Fin n, (edgeDiff x i) ^ 2)
          + 2 * (∑ i : Fin n, edgeDiff x i * edgeDiff y i)
          + (∑ i : Fin n, (edgeDiff y i) ^ 2) := by
    calc
      (∑ i : Fin n, (edgeDiff (x + y) i) ^ 2)
          = ∑ i : Fin n,
              ((edgeDiff x i) ^ 2
                + 2 * (edgeDiff x i * edgeDiff y i)
                + (edgeDiff y i) ^ 2) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [edgeDiff_add]
              ring
      _ = (∑ i : Fin n, (edgeDiff x i) ^ 2)
          + 2 * (∑ i : Fin n, edgeDiff x i * edgeDiff y i)
          + (∑ i : Fin n, (edgeDiff y i) ^ 2) := by
              simp [Finset.sum_add_distrib, Finset.mul_sum]
  unfold energy energyInner
  rw [hedge]
  simp only [Pi.add_apply]
  ring

/-- The chain energy is a sum of squares. -/
theorem energy_nonneg {n : ℕ} (x : Vector n) :
    0 ≤ energy x := by
  unfold energy
  positivity

/-- Squared Euclidean norms are nonnegative. -/
theorem normSq_nonneg {n : ℕ} (x : Vector n) :
    0 ≤ normSq x := by
  unfold normSq
  positivity

/-- Each adjacent square is bounded by twice the two endpoint squares. -/
theorem edgeDiff_sq_le {n : ℕ} (x : Vector n) (i : Fin n) :
    (edgeDiff x i) ^ 2
      ≤ 2 * (x i.castSucc) ^ 2 + 2 * (x i.succ) ^ 2 := by
  unfold edgeDiff
  nlinarith [sq_nonneg (x i.castSucc + x i.succ)]

/-- The exact dimension-independent matrix bound `A ≤ 4 I`, expressed through
quadratic forms. -/
theorem energy_le_four_normSq {n : ℕ} (x : Vector n) :
    energy x ≤ 4 * normSq x := by
  have hedge :
      (∑ i : Fin n, (edgeDiff x i) ^ 2)
        ≤ ∑ i : Fin n,
            (2 * (x i.castSucc) ^ 2 + 2 * (x i.succ) ^ 2) := by
    exact Finset.sum_le_sum fun i hi => edgeDiff_sq_le x i
  have hedge' :
      (∑ i : Fin n, (edgeDiff x i) ^ 2)
        ≤ 2 * (∑ i : Fin n, (x i.castSucc) ^ 2)
          + 2 * (∑ i : Fin n, (x i.succ) ^ 2) := by
    calc
      (∑ i : Fin n, (edgeDiff x i) ^ 2)
          ≤ ∑ i : Fin n,
              (2 * (x i.castSucc) ^ 2 + 2 * (x i.succ) ^ 2) := hedge
      _ = 2 * (∑ i : Fin n, (x i.castSucc) ^ 2)
          + 2 * (∑ i : Fin n, (x i.succ) ^ 2) := by
            simp [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hcast := Fin.sum_univ_castSucc (fun i : Fin (n + 1) => (x i) ^ 2)
  have hsucc := Fin.sum_univ_succ (fun i : Fin (n + 1) => (x i) ^ 2)
  unfold energy normSq
  nlinarith [sq_nonneg (x 0), sq_nonneg (x (Fin.last n))]

/-- A rank-one bilinear form factors into two dot products. -/
theorem bilinearForm_rankOne {n : ℕ} (u x y : Vector n) :
    bilinearForm (rankOne u) x y = (u ⬝ᵥ x) * (u ⬝ᵥ y) := by
  unfold bilinearForm rankOne
  rw [Matrix.vecMulVec_mulVec]
  simp [dotProduct_comm, mul_comm]

@[simp] theorem bilinearForm_zero {n : ℕ} (x y : Vector n) :
    bilinearForm (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) x y = 0 := by
  simp [bilinearForm]

/-- Bilinear evaluation distributes over matrix addition. -/
theorem bilinearForm_add {n : ℕ}
    (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (x y : Vector n) :
    bilinearForm (A + B) x y = bilinearForm A x y + bilinearForm B x y := by
  simp [bilinearForm, Matrix.add_mulVec]

/-- Bilinear evaluation distributes over a finite matrix sum. -/
theorem bilinearForm_sum {n : ℕ} {ι : Type*}
    (s : Finset ι)
    (A : ι → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (x y : Vector n) :
    bilinearForm (∑ i ∈ s, A i) x y = ∑ i ∈ s, bilinearForm (A i) x y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp [ha, ih, bilinearForm_add]

/-- The matrix bilinear form is exactly the polarized sum-of-squares energy. -/
theorem bilinearForm_chainMatrix {n : ℕ} (x y : Vector n) :
    bilinearForm (chainMatrix n) x y = energyInner x y := by
  rw [chainMatrix, bilinearForm_add, bilinearForm_add]
  rw [bilinearForm_sum (s := Finset.univ) (A := fun i : Fin n => rankOne (edgeBasis i))]
  simp [bilinearForm_rankOne, energyInner]

/-- The advertised square-sum identity

`xᵀ A x = x₀² + ∑ᵢ (xᵢ - xᵢ₊₁)² + x_last²`.
-/
theorem quadraticForm_chainMatrix {n : ℕ} (x : Vector n) :
    quadraticForm (chainMatrix n) x = energy x := by
  rw [quadraticForm, bilinearForm_chainMatrix, energy_eq_energyInner]

/-- The chain matrix is symmetric. -/
theorem chainMatrix_transpose (n : ℕ) :
    (chainMatrix n)ᵀ = chainMatrix n := by
  ext i j
  simp [chainMatrix, rankOne, Matrix.vecMulVec_apply, Matrix.sum_apply, mul_comm]

/-- Every rank-one term used in the chain factorization is positive
semidefinite. -/
theorem rankOne_posSemidef {n : ℕ} (u : Vector n) :
    (rankOne u).PosSemidef := by
  simpa [rankOne] using Matrix.posSemidef_vecMulVec_star_self u

/-- The chain matrix is positive semidefinite. -/
theorem chainMatrix_posSemidef (n : ℕ) :
    (chainMatrix n).PosSemidef := by
  have hedge :
      (∑ i : Fin n, rankOne (edgeBasis i)).PosSemidef := by
    apply Matrix.posSemidef_sum Finset.univ
    intro i hi
    exact rankOne_posSemidef (edgeBasis i)
  exact ((rankOne_posSemidef (firstBasis n)).add hedge).add
    (rankOne_posSemidef (lastBasis n))

/-- Positivity of the chain quadratic form, in the total-vector semantics used
by the rest of this development. -/
theorem quadraticForm_chainMatrix_nonneg {n : ℕ} (x : Vector n) :
    0 ≤ quadraticForm (chainMatrix n) x := by
  rw [quadraticForm_chainMatrix]
  exact energy_nonneg x

/-- The upper matrix bound `A ≤ 4 I`, in total-vector quadratic semantics. -/
theorem quadraticForm_chainMatrix_le {n : ℕ} (x : Vector n) :
    quadraticForm (chainMatrix n) x ≤ 4 * normSq x := by
  rw [quadraticForm_chainMatrix]
  exact energy_le_four_normSq x

end NesterovChain
end HardInstances
end LeanPEP
