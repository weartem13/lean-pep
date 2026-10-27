import LeanPEP.GramPEP.Coordinate

/-!
# Rational-to-real bridge for Gram-PEP data

Exact rational Gram data can be cast entrywise into the real semantic layer.
This file proves preservation of Gram inner products, represented squared
norms, and every ordered interpolation slack.  It deliberately does not claim
that arbitrary rational proposition-level PSD automatically implies real PSD;
for the standard-coordinate witnesses used in v0.10C, real PSD follows
independently from `standardGram_posSemidef`.
-/

namespace LeanPEP
namespace GramPEP

/-- Entrywise cast of a rational coefficient expression. -/
noncomputable def castVecQ {m : ℕ} (u : VecExpr m ℚ) : VecExpr m ℝ :=
  fun i => (u i : ℝ)

/-- Entrywise cast of a rational Gram matrix. -/
noncomputable def castGramQ {m : ℕ} (G : Gram m ℚ) : Gram m ℝ :=
  fun i j => (G i j : ℝ)

/-- Entrywise cast of complete rational Gram-PEP data. -/
noncomputable def castDataQ
    {Point : Type*} {m : ℕ} (d : DataQ Point m) : DataR Point m :=
  { gram := castGramQ d.gram
    position := fun p => castVecQ (d.position p)
    gradient := fun p => castVecQ (d.gradient p)
    value := fun p => (d.value p : ℝ) }

@[simp] theorem castVecQ_apply
    {m : ℕ} (u : VecExpr m ℚ) (i : Fin m) :
    castVecQ u i = (u i : ℝ) := rfl

@[simp] theorem castGramQ_apply
    {m : ℕ} (G : Gram m ℚ) (i j : Fin m) :
    castGramQ G i j = (G i j : ℝ) := rfl

@[simp] theorem castDataQ_gram
    {Point : Type*} {m : ℕ} (d : DataQ Point m) :
    (castDataQ d).gram = castGramQ d.gram := rfl

@[simp] theorem castDataQ_position_apply
    {Point : Type*} {m : ℕ} (d : DataQ Point m)
    (p : Point) (i : Fin m) :
    (castDataQ d).position p i = (d.position p i : ℝ) := rfl

@[simp] theorem castDataQ_gradient_apply
    {Point : Type*} {m : ℕ} (d : DataQ Point m)
    (p : Point) (i : Fin m) :
    (castDataQ d).gradient p i = (d.gradient p i : ℝ) := rfl

@[simp] theorem castDataQ_value
    {Point : Type*} {m : ℕ} (d : DataQ Point m) (p : Point) :
    (castDataQ d).value p = (d.value p : ℝ) := rfl

@[simp] theorem castVecQ_sub
    {m : ℕ} (u v : VecExpr m ℚ) :
    castVecQ (u - v) = castVecQ u - castVecQ v := by
  funext i
  simp [castVecQ]

/-- Exact casts commute with Gram bilinear evaluation. -/
@[simp] theorem gramInner_castQ
    {m : ℕ} (G : Gram m ℚ) (u v : VecExpr m ℚ) :
    gramInner (castGramQ G) (castVecQ u) (castVecQ v) =
      ((gramInner G u v : ℚ) : ℝ) := by
  simp [gramInner, castGramQ, castVecQ]

/-- Exact casts commute with represented squared norms. -/
@[simp] theorem gramNormSq_castQ
    {m : ℕ} (G : Gram m ℚ) (u : VecExpr m ℚ) :
    gramNormSq (castGramQ G) (castVecQ u) =
      ((gramNormSq G u : ℚ) : ℝ) := by
  simp [gramNormSq]

/-- Casting the standard rational Gram matrix gives the standard real Gram
matrix. -/
@[simp] theorem castGramQ_standardGram {m : ℕ} :
    castGramQ (standardGram (m := m) (𝕜 := ℚ)) =
      standardGram (m := m) (𝕜 := ℝ) := by
  funext i j
  by_cases hij : i = j
  · simp [castGramQ, standardGram, hij]
  · simp [castGramQ, standardGram, hij]

/-- Every exact rational interpolation slack is preserved by the real cast. -/
@[simp] theorem interpolationSlack_castDataQ
    {Point : Type*} {m : ℕ} (d : DataQ Point m) (i j : Point) :
    interpolationSlack (castDataQ d) i j =
      ((interpolationSlack d i j : ℚ) : ℝ) := by
  simp [interpolationSlack, castDataQ, castGramQ, castVecQ,
    gramInner, gramNormSq]

/-- Rational interpolation feasibility implies real interpolation feasibility
for the entrywise cast data. -/
theorem interpolationFeasibleQ_toReal
    {Point : Type*} {m : ℕ} (d : DataQ Point m)
    (h : InterpolationFeasible d) :
    InterpolationFeasible (castDataQ d) := by
  intro i j
  rw [interpolationSlack_castDataQ]
  exact Rat.cast_nonneg.mpr (h i j)

end GramPEP
end LeanPEP
