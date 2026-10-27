import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Mul

/-!
# Exact Gram-PEP semantic core

A general-dimensional finite PEP does not store concrete ambient vectors.
Instead, every sampled point displacement and gradient is represented by a
coefficient vector over a finite abstract vector family, while a Gram matrix
records the inner products of that family.

This module defines only the exact mathematical semantics:

* coefficient-vector expressions;
* Gram inner products and squared norms;
* sampled positions, gradients, and function values;
* every ordered smooth-convex interpolation slack; and
* proposition-level symmetry and positive-semidefiniteness obligations.

It deliberately does not yet provide an executable PSD checker, algorithmic
trajectory constraints, normalization constraints, or a solver-artifact
schema.  Those are later layers built on this core.
-/

namespace LeanPEP
namespace GramPEP

open scoped BigOperators

/-- A formal vector expression over `m` abstract base vectors. -/
abbrev VecExpr (m : ℕ) (𝕜 : Type*) := Fin m → 𝕜

/-- A Gram matrix for `m` abstract base vectors. -/
abbrev Gram (m : ℕ) (𝕜 : Type*) := Matrix (Fin m) (Fin m) 𝕜

/-- Exact bilinear evaluation `uᵀ G v`. -/
def gramInner
    {m : ℕ} {𝕜 : Type*} [Semiring 𝕜]
    (G : Gram m 𝕜) (u v : VecExpr m 𝕜) : 𝕜 :=
  ∑ i, ∑ j, u i * G i j * v j

/-- Exact squared norm represented by a Gram matrix. -/
def gramNormSq
    {m : ℕ} {𝕜 : Type*} [Semiring 𝕜]
    (G : Gram m 𝕜) (u : VecExpr m 𝕜) : 𝕜 :=
  gramInner G u u

/-- Symmetry of a real/rational Gram matrix. -/
def IsGramSymmetric
    {m : ℕ} {𝕜 : Type*}
    (G : Gram m 𝕜) : Prop :=
  ∀ i j, G i j = G j i

/-- Proposition-level positive-semidefiniteness for the finite-vector
semantics used by the project.

The executable exact factorization checker planned for the next stage will
produce this proposition; this definition itself is not an eigenvalue test.
-/
def IsGramPosSemidef
    {m : ℕ} {𝕜 : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (G : Gram m 𝕜) : Prop :=
  IsGramSymmetric G ∧ ∀ u : VecExpr m 𝕜, 0 ≤ gramNormSq G u

/-- General finite sampled data interpreted through one Gram matrix.  The
point type includes every point relevant to the formulation, including an
optimum point when the model uses one. -/
@[ext]
structure Data (Point : Type*) (m : ℕ) (𝕜 : Type*) where
  gram : Gram m 𝕜
  position : Point → VecExpr m 𝕜
  gradient : Point → VecExpr m 𝕜
  value : Point → 𝕜

/-- Exact rational Gram-PEP data. -/
abbrev DataQ (Point : Type*) (m : ℕ) := Data Point m ℚ

/-- Exact real Gram-PEP data. -/
abbrev DataR (Point : Type*) (m : ℕ) := Data Point m ℝ

/-- The normalized `1`-smooth convex interpolation slack for one ordered pair.
This is a scalar.  It is not a PSD matrix entry and it is not itself a Gram
matrix. -/
def interpolationSlack
    {Point : Type*} {m : ℕ} {𝕜 : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (d : Data Point m 𝕜) (i j : Point) : 𝕜 :=
  d.value i - d.value j
    - gramInner d.gram (d.gradient j) (d.position i - d.position j)
    - ((1 : 𝕜) / 2) * gramNormSq d.gram (d.gradient i - d.gradient j)

/-- All scalar ordered-pair interpolation constraints. -/
def InterpolationFeasible
    {Point : Type*} {m : ℕ} {𝕜 : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (d : Data Point m 𝕜) : Prop :=
  ∀ i j, 0 ≤ interpolationSlack d i j

/-- The current general-dimensional semantic core: a genuine PSD Gram matrix
plus every scalar interpolation inequality.

Algorithm equations, normalization, and the objective remain formulation
specific and are intentionally not hidden inside this definition.
-/
def CoreFeasible
    {Point : Type*} {m : ℕ} {𝕜 : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (d : Data Point m 𝕜) : Prop :=
  IsGramPosSemidef d.gram ∧ InterpolationFeasible d

/-- Deterministic row-major ordered-pair enumeration for a supplied point list. -/
def orderedPairs {Point : Type*} (points : List Point) : List (Point × Point) :=
  points.flatMap (fun i => points.map (fun j => (i, j)))

@[simp] theorem gramInner_zero_left
    {m : ℕ} {𝕜 : Type*} [Semiring 𝕜]
    (G : Gram m 𝕜) (v : VecExpr m 𝕜) :
    gramInner G 0 v = 0 := by
  simp [gramInner]

@[simp] theorem gramInner_zero_right
    {m : ℕ} {𝕜 : Type*} [Semiring 𝕜]
    (G : Gram m 𝕜) (u : VecExpr m 𝕜) :
    gramInner G u 0 = 0 := by
  simp [gramInner]

@[simp] theorem gramNormSq_zero
    {m : ℕ} {𝕜 : Type*} [Semiring 𝕜]
    (G : Gram m 𝕜) :
    gramNormSq G 0 = 0 := by
  simp [gramNormSq]

end GramPEP
end LeanPEP
