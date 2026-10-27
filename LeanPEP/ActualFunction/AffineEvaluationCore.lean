import LeanPEP.Toy.FiniteGD.UpperCertificate
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-! Generic realization of rational affine vectors; no GD certificate instance. -/
namespace LeanPEP.ActualFunction.ParametricGDHilbert
open scoped BigOperators
open LeanPEP.Toy.FiniteGD
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A rational coefficient vector realized as a finite ambient linear
combination of sampled gradients. -/
noncomputable def linearCombination
    {N : ℕ}
    (a : Fin (N + 1) → ℚ)
    (grad : Fin (N + 1) → E) : E :=
  ∑ i, (a i : ℝ) • grad i

/-- Ambient vector represented by one affine form in the sampled gradients. -/
noncomputable def evalVector
    {N : ℕ}
    (a : GradAffineQ N)
    (u0 : E)
    (grad : Fin (N + 1) → E) : E :=
  (a.constCoeff : ℝ) • u0 + linearCombination a.gradCoeff grad

@[simp] theorem evalVector_zero
    {N : ℕ} (u0 : E) (grad : Fin (N + 1) → E) :
    evalVector (GradAffineQ.zero N) u0 grad = 0 := by
  simp [evalVector, linearCombination, GradAffineQ.zero]

@[simp] theorem evalVector_const
    {N : ℕ} (c : ℚ) (u0 : E) (grad : Fin (N + 1) → E) :
    evalVector (GradAffineQ.const N c) u0 grad = (c : ℝ) • u0 := by
  simp [evalVector, linearCombination, GradAffineQ.const]

@[simp] theorem evalVector_basis
    {N : ℕ} (i : Fin (N + 1))
    (u0 : E) (grad : Fin (N + 1) → E) :
    evalVector (GradAffineQ.basis i) u0 grad = grad i := by
  classical
  unfold evalVector linearCombination
  simp only [GradAffineQ.basis, Rat.cast_zero, zero_smul, zero_add]
  rw [Fintype.sum_eq_single i (by
    intro j hji
    simp [unitCoeff, hji])]
  simp [unitCoeff]

@[simp] theorem evalVector_add
    {N : ℕ} (a b : GradAffineQ N)
    (u0 : E) (grad : Fin (N + 1) → E) :
    evalVector (GradAffineQ.add a b) u0 grad =
      evalVector a u0 grad + evalVector b u0 grad := by
  simp [evalVector, linearCombination, GradAffineQ.add,
    add_smul, Finset.sum_add_distrib] <;> abel

@[simp] theorem evalVector_neg
    {N : ℕ} (a : GradAffineQ N)
    (u0 : E) (grad : Fin (N + 1) → E) :
    evalVector (GradAffineQ.neg a) u0 grad =
      -evalVector a u0 grad := by
  simp [evalVector, linearCombination, GradAffineQ.neg] <;> abel

@[simp] theorem evalVector_sub
    {N : ℕ} (a b : GradAffineQ N)
    (u0 : E) (grad : Fin (N + 1) → E) :
    evalVector (GradAffineQ.sub a b) u0 grad =
      evalVector a u0 grad - evalVector b u0 grad := by
  change evalVector (GradAffineQ.add a (GradAffineQ.neg b)) u0 grad = _
  rw [evalVector_add, evalVector_neg]
  exact (sub_eq_add_neg _ _).symm

@[simp] theorem evalVector_scale
    {N : ℕ} (c : ℚ) (a : GradAffineQ N)
    (u0 : E) (grad : Fin (N + 1) → E) :
    evalVector (GradAffineQ.scale c a) u0 grad =
      (c : ℝ) • evalVector a u0 grad := by
  simp [evalVector, linearCombination, GradAffineQ.scale,
    smul_add, Finset.smul_sum, smul_smul]

end LeanPEP.ActualFunction.ParametricGDHilbert
