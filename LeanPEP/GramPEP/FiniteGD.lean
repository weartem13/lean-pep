import LeanPEP.GramPEP.Core
import LeanPEP.Toy.FiniteGD.Core

/-!
# One-dimensional finite-GD embedding into Gram semantics

The existing `FiniteGD` model uses scalar positions and gradients.  This file
embeds those scalars as coefficient vectors over one abstract base vector with
Gram matrix `[1]`.

The main theorem proves exact preservation of every ordered interpolation
slack.  Consequently, the old scalar feasibility proposition is equivalent to
interpolation feasibility of the embedded Gram data; adding the trivially PSD
unit Gram matrix yields equivalence with `GramPEP.CoreFeasible`.
-/

namespace LeanPEP
namespace GramPEP

open scoped BigOperators

/-- The one-dimensional unit Gram matrix. -/
def unitGram {𝕜 : Type*} [One 𝕜] : Gram 1 𝕜 :=
  fun _ _ => 1

/-- A scalar represented as a coefficient vector over the one-dimensional
abstract basis. -/
def scalarExpr {𝕜 : Type*} (a : 𝕜) : VecExpr 1 𝕜 :=
  fun _ => a

/-- Bilinear evaluation under the unit Gram matrix is ordinary multiplication. -/
@[simp] theorem gramInner_unitGram
    {𝕜 : Type*} [Semiring 𝕜]
    (u v : VecExpr 1 𝕜) :
    gramInner (unitGram (𝕜 := 𝕜)) u v = u 0 * v 0 := by
  unfold gramInner
  rw [Fin.sum_univ_one, Fin.sum_univ_one]
  simp [unitGram]

/-- The unit-Gram squared norm is the square of the sole coordinate. -/
@[simp] theorem gramNormSq_unitGram
    {𝕜 : Type*} [Semiring 𝕜]
    (u : VecExpr 1 𝕜) :
    gramNormSq (unitGram (𝕜 := 𝕜)) u = (u 0)^2 := by
  simp [gramNormSq, pow_two]

/-- The unit Gram matrix is propositionally positive semidefinite. -/
theorem unitGram_posSemidef
    {𝕜 : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] :
    IsGramPosSemidef (unitGram (𝕜 := 𝕜)) := by
  constructor
  · intro i j
    rfl
  · intro u
    rw [gramNormSq_unitGram]
    exact sq_nonneg (u 0)

/-- Embed scalar finite-GD data into a one-basis-vector Gram representation. -/
def ofFiniteGD
    {N : ℕ} {𝕜 : Type*} [AddGroup 𝕜] [One 𝕜]
    (d : LeanPEP.Toy.FiniteGD.Data N 𝕜) :
    Data (LeanPEP.Toy.FiniteGD.Point N) 1 𝕜 :=
  { gram := unitGram
    position := fun p => scalarExpr (LeanPEP.Toy.FiniteGD.x d p)
    gradient := fun p => scalarExpr (LeanPEP.Toy.FiniteGD.gradAt d p)
    value := fun p => LeanPEP.Toy.FiniteGD.valueAt d p }

@[simp] theorem ofFiniteGD_position_apply
    {N : ℕ} {𝕜 : Type*} [AddGroup 𝕜] [One 𝕜]
    (d : LeanPEP.Toy.FiniteGD.Data N 𝕜)
    (p : LeanPEP.Toy.FiniteGD.Point N) (k : Fin 1) :
    (ofFiniteGD d).position p k = LeanPEP.Toy.FiniteGD.x d p := rfl

@[simp] theorem ofFiniteGD_gradient_apply
    {N : ℕ} {𝕜 : Type*} [AddGroup 𝕜] [One 𝕜]
    (d : LeanPEP.Toy.FiniteGD.Data N 𝕜)
    (p : LeanPEP.Toy.FiniteGD.Point N) (k : Fin 1) :
    (ofFiniteGD d).gradient p k = LeanPEP.Toy.FiniteGD.gradAt d p := rfl

@[simp] theorem ofFiniteGD_value
    {N : ℕ} {𝕜 : Type*} [AddGroup 𝕜] [One 𝕜]
    (d : LeanPEP.Toy.FiniteGD.Data N 𝕜)
    (p : LeanPEP.Toy.FiniteGD.Point N) :
    (ofFiniteGD d).value p = LeanPEP.Toy.FiniteGD.valueAt d p := rfl

/-- The Gram embedding preserves every ordered scalar interpolation slack
exactly, with no inequality weakening or dimensional approximation. -/
@[simp] theorem interpolationSlack_ofFiniteGD
    {N : ℕ} {𝕜 : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (d : LeanPEP.Toy.FiniteGD.Data N 𝕜)
    (i j : LeanPEP.Toy.FiniteGD.Point N) :
    interpolationSlack (ofFiniteGD d) i j =
      LeanPEP.Toy.FiniteGD.slack d i j := by
  simp [interpolationSlack, LeanPEP.Toy.FiniteGD.slack,
    ofFiniteGD, scalarExpr, pow_two]

/-- Scalar finite-GD feasibility is exactly interpolation feasibility after
embedding into the one-dimensional Gram representation. -/
theorem interpolationFeasible_ofFiniteGD_iff
    {N : ℕ} {𝕜 : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (d : LeanPEP.Toy.FiniteGD.Data N 𝕜) :
    InterpolationFeasible (ofFiniteGD d) ↔
      LeanPEP.Toy.FiniteGD.Feasible d := by
  constructor
  · intro h i j
    simpa using h i j
  · intro h i j
    simpa using h i j

/-- Because the unit Gram matrix is PSD, the complete Gram semantic core is
also equivalent to the old scalar finite-GD feasibility proposition. -/
theorem coreFeasible_ofFiniteGD_iff
    {N : ℕ} {𝕜 : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (d : LeanPEP.Toy.FiniteGD.Data N 𝕜) :
    CoreFeasible (ofFiniteGD d) ↔
      LeanPEP.Toy.FiniteGD.Feasible d := by
  constructor
  · intro h
    exact (interpolationFeasible_ofFiniteGD_iff d).mp h.2
  · intro h
    exact ⟨unitGram_posSemidef,
      (interpolationFeasible_ofFiniteGD_iff d).mpr h⟩

end GramPEP
end LeanPEP
