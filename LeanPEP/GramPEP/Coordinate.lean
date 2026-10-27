import LeanPEP.GramPEP.PSDFactorization

/-!
# Standard-coordinate Gram realizations

A concrete rational vector in `Fin m → ℚ` can be interpreted directly as a
`VecExpr m ℚ` over the standard coordinate axes.  The corresponding Gram
matrix is the identity matrix.  This module provides the exact identity-Gram
semantics and a canonical rank-one factor certificate consisting of the
standard basis vectors.

The identity Gram matrix is a PEP Gram matrix for the chosen abstract base
vectors.  It is unrelated to the Nesterov-chain Hessian structure matrix.
-/

namespace LeanPEP
namespace GramPEP

open scoped BigOperators

/-- Gram matrix of the standard coordinate axes. -/
def standardGram
    {m : ℕ} {𝕜 : Type*} [Zero 𝕜] [One 𝕜] : Gram m 𝕜 :=
  fun i j => if i = j then 1 else 0

/-- One standard coordinate basis expression. -/
def standardBasisExpr
    {m : ℕ} {𝕜 : Type*} [Zero 𝕜] [One 𝕜]
    (i : Fin m) : VecExpr m 𝕜 :=
  fun j => if j = i then 1 else 0

/-- Gram evaluation under the standard-coordinate Gram matrix is the ordinary
coordinate dot product. -/
@[simp] theorem gramInner_standardGram
    {m : ℕ} {𝕜 : Type*} [CommSemiring 𝕜]
    (u v : VecExpr m 𝕜) :
    gramInner (standardGram (m := m) (𝕜 := 𝕜)) u v =
      ∑ i, u i * v i := by
  classical
  simp [gramInner, standardGram]

/-- The represented squared norm is the sum of coordinate squares. -/
@[simp] theorem gramNormSq_standardGram
    {m : ℕ} {𝕜 : Type*} [CommSemiring 𝕜]
    (u : VecExpr m 𝕜) :
    gramNormSq (standardGram (m := m) (𝕜 := 𝕜)) u =
      ∑ i, (u i)^2 := by
  simp [gramNormSq, pow_two]

/-- The standard-coordinate Gram matrix is propositionally PSD over every
strictly ordered field. -/
theorem standardGram_posSemidef
    {m : ℕ} {𝕜 : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] :
    IsGramPosSemidef (standardGram (m := m) (𝕜 := 𝕜)) := by
  constructor
  · intro i j
    by_cases hij : i = j
    · subst j
      rfl
    · have hji : j ≠ i := Ne.symm hij
      simp [standardGram, hij, hji]
  · intro u
    rw [gramNormSq_standardGram]
    exact Finset.sum_nonneg (fun i hi => sq_nonneg (u i))

/-- Canonical exact rational factor certificate for the standard Gram matrix:
`I = Σ_i e_i e_iᵀ`. -/
def standardFactorCertQ (m : ℕ) : PSDFactorCertQ m :=
  { factors :=
      (gramIndices m).map (fun i =>
        { weight := 1
          vector := standardBasisExpr (𝕜 := ℚ) i }) }

end GramPEP
end LeanPEP
