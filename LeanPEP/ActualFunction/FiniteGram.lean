import LeanPEP.ActualFunction.AnalyticBridge
import LeanPEP.GramPEP.UpperCertificate
import Mathlib.Tactic

/-!
# Finite actual samples as exact real Gram-PEP data

This file supplies the representation layer required between actual Hilbert-space
samples and the finite Gram-PEP semantic core.

A finite family of ambient vectors determines a real Gram matrix.  A coefficient
vector is realized as the corresponding finite linear combination of those
ambient vectors.  The main semantic theorem proves that `gramInner` is exactly
the ambient inner product of the realized vectors; positive semidefiniteness is
then immediate from nonnegativity of an actual squared norm.

For a fixed rational `ModelQ`, `dataOfModel` keeps the model's symbolic
position and gradient coefficient vectors and fills in its Gram matrix and
function values from actual data.  A separate `RealizesActualSamples`
proposition records that those symbolic vectors really denote centered sampled
positions and actual gradients.  Under this proposition, every Gram
interpolation slack is definitionally connected to the actual-function slack.
Consequently the analytic smooth-convex theorem from v0.12A2 yields
`CoreFeasible` for the finite datum.

This is a soundness direction only.  It does not assert that arbitrary feasible
finite Gram data are realizable by an actual smooth-convex interpolant.
-/

namespace LeanPEP
namespace ActualFunction
namespace FiniteGram

open scoped BigOperators
open GramPEP

variable
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The exact real Gram matrix of a finite family of ambient vectors. -/
noncomputable def gramOfVectors {m : ℕ} (base : Fin m → E) : Gram m ℝ :=
  fun i j => inner ℝ (base i) (base j)

/-- Realize a formal coefficient vector as a finite ambient linear
combination. -/
noncomputable def realize {m : ℕ}
    (base : Fin m → E) (u : VecExpr m ℝ) : E :=
  ∑ i, u i • base i

@[simp] theorem realize_zero {m : ℕ} (base : Fin m → E) :
    realize base 0 = 0 := by
  simp [realize]

@[simp] theorem realize_add {m : ℕ} (base : Fin m → E)
    (u v : VecExpr m ℝ) :
    realize base (u + v) = realize base u + realize base v := by
  simp [realize, add_smul, Finset.sum_add_distrib]

@[simp] theorem realize_neg {m : ℕ} (base : Fin m → E)
    (u : VecExpr m ℝ) :
    realize base (-u) = -realize base u := by
  simp [realize]

@[simp] theorem realize_sub {m : ℕ} (base : Fin m → E)
    (u v : VecExpr m ℝ) :
    realize base (u - v) = realize base u - realize base v := by
  simp [realize, sub_smul, Finset.sum_sub_distrib]

/-- The abstract Gram bilinear form is exactly the ambient inner product of the
realized vectors. -/
theorem gramInner_gramOfVectors {m : ℕ} (base : Fin m → E)
    (u v : VecExpr m ℝ) :
    gramInner (gramOfVectors base) u v =
      inner ℝ (realize base u) (realize base v) := by
  classical
  unfold gramInner
  calc
    (∑ i, ∑ j, u i * gramOfVectors base i j * v j) =
        ∑ i, ∑ j, inner ℝ (u i • base i) (v j • base j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [real_inner_smul_left, real_inner_smul_right]
      dsimp [gramOfVectors]
      ring
    _ = inner ℝ (∑ i, u i • base i) (∑ j, v j • base j) := by
      rw [sum_inner]
      apply Finset.sum_congr rfl
      intro i hi
      rw [inner_sum]
    _ = inner ℝ (realize base u) (realize base v) := rfl

/-- The represented squared norm is an actual ambient squared norm. -/
theorem gramNormSq_gramOfVectors {m : ℕ} (base : Fin m → E)
    (u : VecExpr m ℝ) :
    gramNormSq (gramOfVectors base) u =
      inner ℝ (realize base u) (realize base u) := by
  simpa [gramNormSq] using gramInner_gramOfVectors base u u

/-- A Gram matrix built from actual vectors is symmetric. -/
theorem gramOfVectors_symmetric {m : ℕ} (base : Fin m → E) :
    IsGramSymmetric (gramOfVectors base) := by
  intro i j
  exact real_inner_comm _ _

/-- A Gram matrix built from actual vectors is propositionally positive
semidefinite. -/
theorem gramOfVectors_posSemidef {m : ℕ} (base : Fin m → E) :
    IsGramPosSemidef (gramOfVectors base) := by
  constructor
  · exact gramOfVectors_symmetric base
  · intro u
    rw [gramNormSq_gramOfVectors]
    exact real_inner_self_nonneg

/-- Real Gram-PEP data obtained from a fixed rational model, an ambient vector
family, actual sample points, and actual function values.

The stored positions and gradients are still the model's coefficient vectors.
Their ambient meaning is supplied separately by `RealizesActualSamples`.
-/
noncomputable def dataOfModel
    {p m : ℕ}
    (base : Fin m → E) (model : ModelQ p m)
    (sample : Fin p → E) (f : E → ℝ) : DataR (Fin p) m :=
  { gram := gramOfVectors base
    position := fun i => castVecQ (model.position i)
    gradient := fun i => castVecQ (model.gradient i)
    value := fun i => f (sample i) }

@[simp] theorem dataOfModel_gram
    {p m : ℕ}
    (base : Fin m → E) (model : ModelQ p m)
    (sample : Fin p → E) (f : E → ℝ) :
    (dataOfModel base model sample f).gram = gramOfVectors base := rfl

@[simp] theorem dataOfModel_position
    {p m : ℕ}
    (base : Fin m → E) (model : ModelQ p m)
    (sample : Fin p → E) (f : E → ℝ) (i : Fin p) :
    (dataOfModel base model sample f).position i =
      castVecQ (model.position i) := rfl

@[simp] theorem dataOfModel_gradient
    {p m : ℕ}
    (base : Fin m → E) (model : ModelQ p m)
    (sample : Fin p → E) (f : E → ℝ) (i : Fin p) :
    (dataOfModel base model sample f).gradient i =
      castVecQ (model.gradient i) := rfl

@[simp] theorem dataOfModel_value
    {p m : ℕ}
    (base : Fin m → E) (model : ModelQ p m)
    (sample : Fin p → E) (f : E → ℝ) (i : Fin p) :
    (dataOfModel base model sample f).value i = f (sample i) := rfl

/-- The coefficient fields of `dataOfModel` realize the supplied fixed model
by construction. -/
theorem dataOfModel_realizes
    {p m : ℕ}
    (base : Fin m → E) (model : ModelQ p m)
    (sample : Fin p → E) (f : E → ℝ) :
    RealizesModelQ model (dataOfModel base model sample f) := by
  constructor
  · intro i
    rfl
  · intro i
    rfl

/-- Ambient interpretation of all symbolic samples in a fixed model.

Positions are represented relative to one common anchor.  This centering is
mathematically harmless because every interpolation constraint uses only
position differences. -/
structure RealizesActualSamples
    {p m : ℕ}
    (base : Fin m → E) (model : ModelQ p m)
    (sample : Fin p → E) (anchor : E) (g : E → E) : Prop where
  position :
    ∀ i,
      realize base (castVecQ (model.position i)) = sample i - anchor
  gradient :
    ∀ i,
      realize base (castVecQ (model.gradient i)) = g (sample i)

/-- Every Gram interpolation slack in `dataOfModel` is exactly the
corresponding actual-function interpolation slack. -/
theorem interpolationSlack_dataOfModel
    {p m : ℕ}
    {base : Fin m → E} {model : ModelQ p m}
    {sample : Fin p → E} {anchor : E}
    {f : E → ℝ} {g : E → E}
    (hreal : RealizesActualSamples base model sample anchor g)
    (i j : Fin p) :
    GramPEP.interpolationSlack (dataOfModel base model sample f) i j =
      ActualFunction.interpolationSlack f g (sample i) (sample j) := by
  have hpositionDiff :
      realize base
          (castVecQ (model.position i) - castVecQ (model.position j)) =
        sample i - sample j := by
    rw [realize_sub, hreal.position i, hreal.position j]
    abel
  have hgradientDiff :
      realize base
          (castVecQ (model.gradient i) - castVecQ (model.gradient j)) =
        g (sample i) - g (sample j) := by
    rw [realize_sub, hreal.gradient i, hreal.gradient j]
  change
    f (sample i) - f (sample j)
        - gramInner (gramOfVectors base)
            (castVecQ (model.gradient j))
            (castVecQ (model.position i) - castVecQ (model.position j))
        - ((1 : ℝ) / 2) *
            gramNormSq (gramOfVectors base)
              (castVecQ (model.gradient i) - castVecQ (model.gradient j)) =
      f (sample i) - f (sample j)
        - inner ℝ (g (sample j)) (sample i - sample j)
        - ((1 : ℝ) / 2) *
            inner ℝ (g (sample i) - g (sample j))
              (g (sample i) - g (sample j))
  rw [gramInner_gramOfVectors, hreal.gradient j, hpositionDiff,
    gramNormSq_gramOfVectors, hgradientDiff]

/-- Actual smooth-convex samples satisfy every ordered interpolation
constraint of their exact real Gram datum. -/
theorem dataOfModel_interpolationFeasible
    {p m : ℕ}
    [CompleteSpace E]
    {base : Fin m → E} {model : ModelQ p m}
    {sample : Fin p → E} {anchor : E}
    {f : E → ℝ} {g : E → E}
    (hfun : IsOneSmoothConvexAnalytic f g)
    (hreal : RealizesActualSamples base model sample anchor g) :
    InterpolationFeasible (dataOfModel base model sample f) := by
  intro i j
  rw [interpolationSlack_dataOfModel hreal i j]
  exact hfun.interpolationSlack_nonneg (sample i) (sample j)

/-- The finite datum built from actual smooth-convex samples has a genuine PSD
Gram matrix and every ordered interpolation inequality. -/
theorem dataOfModel_coreFeasible
    {p m : ℕ}
    [CompleteSpace E]
    {base : Fin m → E} {model : ModelQ p m}
    {sample : Fin p → E} {anchor : E}
    {f : E → ℝ} {g : E → E}
    (hfun : IsOneSmoothConvexAnalytic f g)
    (hreal : RealizesActualSamples base model sample anchor g) :
    CoreFeasible (dataOfModel base model sample f) :=
  ⟨gramOfVectors_posSemidef base,
    dataOfModel_interpolationFeasible hfun hreal⟩

end FiniteGram
end ActualFunction
end LeanPEP
