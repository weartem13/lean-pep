import Mathlib.Tactic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.Range
import Mathlib.Tactic.DeriveFintype

/-!
# Parameterized finite gradient-descent PEP semantics

This file generalizes the hard-coded one-step point set to an arbitrary finite
number `N` of gradient-descent steps.  The iterates are not free variables:
`x₀ = 1` and `xₖ = 1 - ∑_{t < k} gₜ`, so the update
`xₖ₊₁ = xₖ - gₖ` is built into the semantics.

The model is still one-dimensional finite PEP semantics.  It does not yet
formalize real smooth functions or the smooth convex interpolation theorem.
-/

namespace LeanPEP
namespace Toy
namespace FiniteGD

/-- The optimum together with the iterates `0, ..., N`. -/
inductive Point (N : ℕ) where
  | star
  | iter (k : Fin (N + 1))
  deriving DecidableEq, Repr, Fintype

/-- Finite gradient and function-value data for `N` gradient-descent steps. -/
@[ext]
structure Data (N : ℕ) (𝕜 : Type*) where
  grad : Fin (N + 1) → 𝕜
  value : Fin (N + 1) → 𝕜

/-- Sum of the first `k` entries of a gradient vector.

The proof argument records that all accessed indices lie in `Fin (N + 1)`.
-/
def prefixSum
    {N : ℕ} {𝕜 : Type*} [Zero 𝕜] [Add 𝕜]
    (g : Fin (N + 1) → 𝕜) :
    (k : ℕ) → k ≤ N + 1 → 𝕜
  | 0, _ => 0
  | k + 1, hk =>
      prefixSum g k (Nat.le_trans (Nat.le_succ k) hk) +
        g ⟨k, Nat.lt_of_succ_le hk⟩

/-- The normalized position of iterate `k`.

This definition enforces `x₀ = 1` and step-size-one gradient descent.
-/
def iterX
    {N : ℕ} {𝕜 : Type*} [AddGroup 𝕜] [One 𝕜]
    (d : Data N 𝕜) (k : Fin (N + 1)) : 𝕜 :=
  1 - prefixSum d.grad k.val (Nat.le_of_lt k.isLt)

/-- Position attached to any finite point. -/
def x
    {N : ℕ} {𝕜 : Type*} [AddGroup 𝕜] [One 𝕜]
    (d : Data N 𝕜) : Point N → 𝕜
  | Point.star => 0
  | Point.iter k => iterX d k

/-- Gradient attached to any finite point. -/
def gradAt
    {N : ℕ} {𝕜 : Type*} [Zero 𝕜]
    (d : Data N 𝕜) : Point N → 𝕜
  | Point.star => 0
  | Point.iter k => d.grad k

/-- Function value attached to any finite point. -/
def valueAt
    {N : ℕ} {𝕜 : Type*} [Zero 𝕜]
    (d : Data N 𝕜) : Point N → 𝕜
  | Point.star => 0
  | Point.iter k => d.value k

/-- Pairwise scalar interpolation slack for normalized 1-smooth convex finite
PEP data. -/
def slack
    {N : ℕ} {𝕜 : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (d : Data N 𝕜) (i j : Point N) : 𝕜 :=
  valueAt d i - valueAt d j
    - gradAt d j * (x d i - x d j)
    - ((1 : 𝕜) / 2) * (gradAt d i - gradAt d j)^2

/-- Proposition-level finite PEP feasibility. -/
def Feasible
    {N : ℕ} {𝕜 : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (d : Data N 𝕜) : Prop :=
  ∀ i j : Point N, 0 ≤ slack d i j

/-- Real finite trajectory data. -/
abbrev DataR (N : ℕ) := Data N ℝ

/-- Exact rational finite trajectory data. -/
abbrev DataQ (N : ℕ) := Data N ℚ

/-- Every point, in deterministic order: `star, iter 0, ..., iter N`. -/
def points (N : ℕ) : List (Point N) :=
  Point.star :: (List.finRange (N + 1)).map (fun k => Point.iter k)

/-- Every ordered point pair, in deterministic row-major order. -/
def pointPairs (N : ℕ) : List (Point N × Point N) :=
  (points N).flatMap (fun i =>
    (points N).map (fun j => (i, j)))

@[simp] theorem mem_points {N : ℕ} (i : Point N) :
    i ∈ points N := by
  cases i <;> simp [points]

@[simp] theorem mem_pointPairs {N : ℕ} (i j : Point N) :
    (i, j) ∈ pointPairs N := by
  simp [pointPairs]

@[simp] theorem x_star
    {N : ℕ} {𝕜 : Type*} [AddGroup 𝕜] [One 𝕜]
    (d : Data N 𝕜) :
    x d (Point.star : Point N) = 0 := rfl

@[simp] theorem x_iter
    {N : ℕ} {𝕜 : Type*} [AddGroup 𝕜] [One 𝕜]
    (d : Data N 𝕜) (k : Fin (N + 1)) :
    x d (Point.iter k) = iterX d k := rfl

@[simp] theorem gradAt_star
    {N : ℕ} {𝕜 : Type*} [Zero 𝕜]
    (d : Data N 𝕜) :
    gradAt d (Point.star : Point N) = 0 := rfl

@[simp] theorem gradAt_iter
    {N : ℕ} {𝕜 : Type*} [Zero 𝕜]
    (d : Data N 𝕜) (k : Fin (N + 1)) :
    gradAt d (Point.iter k) = d.grad k := rfl

@[simp] theorem valueAt_star
    {N : ℕ} {𝕜 : Type*} [Zero 𝕜]
    (d : Data N 𝕜) :
    valueAt d (Point.star : Point N) = 0 := rfl

@[simp] theorem valueAt_iter
    {N : ℕ} {𝕜 : Type*} [Zero 𝕜]
    (d : Data N 𝕜) (k : Fin (N + 1)) :
    valueAt d (Point.iter k) = d.value k := rfl

end FiniteGD
end Toy
end LeanPEP
