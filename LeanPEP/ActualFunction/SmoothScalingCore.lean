import LeanPEP.ActualFunction.GeneralSmooth
import Mathlib.Tactic

/-! Generic affine/function/gradient normalization, extracted unchanged from
OneStepScaling. No numerical certificate or one-step application is imported. -/
open scoped NNReal
namespace LeanPEP
namespace ActualFunction

namespace SmoothScaling

variable
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Affine change of variables centered at `xStar` with spatial scale `R`. -/
def scaledPoint (xStar : E) (R : ℝ) (z : E) : E :=
  xStar + R • z

/-- Function-value normalization used to reduce smoothness `L` and radius `R`
to the existing unit formulation. -/
noncomputable def normalizedFunction
    (f : E → ℝ) (xStar : E) (L : ℝ≥0) (R : ℝ) (z : E) : ℝ :=
  (f (scaledPoint xStar R z) - f xStar) / ((L : ℝ) * R ^ 2)

/-- Gradient normalization corresponding to `normalizedFunction`. -/
noncomputable def normalizedGradient
    (g : E → E) (xStar : E) (L : ℝ≥0) (R : ℝ) (z : E) : E :=
  (1 / ((L : ℝ) * R)) • g (scaledPoint xStar R z)

variable
    {L : ℝ≥0} {f : E → ℝ} {g : E → E} {xStar : E} {R : ℝ}

/-- Positive `L,R` scaling transports the general first-order models to the
existing normalized first-order contract. -/
theorem normalizedFirstOrder
    (h : IsSmoothConvexFirstOrder L f g)
    (hL : 0 < (L : ℝ)) (hR : 0 < R) :
    IsOneSmoothConvexFirstOrder
      (normalizedFunction f xStar L R)
      (normalizedGradient g xStar L R) := by
  have hL0 : (L : ℝ) ≠ 0 := ne_of_gt hL
  have hR0 : R ≠ 0 := ne_of_gt hR
  have hA : 0 < (L : ℝ) * R ^ 2 := by positivity
  constructor
  · intro x y
    let X : E := scaledPoint xStar R x
    let Y : E := scaledPoint xStar R y
    have hXY : Y - X = R • (y - x) := by
      dsimp [X, Y, scaledPoint]
      rw [smul_sub]
      abel
    have hleft :
        normalizedFunction f xStar L R x
            + inner ℝ (normalizedGradient g xStar L R x) (y - x) =
          (f X - f xStar + inner ℝ (g X) (Y - X)) /
            ((L : ℝ) * R ^ 2) := by
      change
        (f X - f xStar) / ((L : ℝ) * R ^ 2)
            + inner ℝ ((1 / ((L : ℝ) * R)) • g X) (y - x) =
          (f X - f xStar + inner ℝ (g X) (Y - X)) /
            ((L : ℝ) * R ^ 2)
      rw [real_inner_smul_left, hXY, real_inner_smul_right]
      field_simp [hL0, hR0] <;> ring
    rw [hleft]
    change
      (f X - f xStar + inner ℝ (g X) (Y - X)) /
          ((L : ℝ) * R ^ 2) ≤
        (f Y - f xStar) / ((L : ℝ) * R ^ 2)
    rw [div_le_div_iff_of_pos_right hA]
    linarith [h.lowerModel X Y]
  · intro x y
    let X : E := scaledPoint xStar R x
    let Y : E := scaledPoint xStar R y
    have hXY : Y - X = R • (y - x) := by
      dsimp [X, Y, scaledPoint]
      rw [smul_sub]
      abel
    have hright :
        normalizedFunction f xStar L R x
            + inner ℝ (normalizedGradient g xStar L R x) (y - x)
            + ((1 : ℝ) / 2) * inner ℝ (y - x) (y - x) =
          (f X - f xStar
              + inner ℝ (g X) (Y - X)
              + ((L : ℝ) / 2) * inner ℝ (Y - X) (Y - X)) /
            ((L : ℝ) * R ^ 2) := by
      change
        (f X - f xStar) / ((L : ℝ) * R ^ 2)
            + inner ℝ ((1 / ((L : ℝ) * R)) • g X) (y - x)
            + ((1 : ℝ) / 2) * inner ℝ (y - x) (y - x) =
          (f X - f xStar
              + inner ℝ (g X) (Y - X)
              + ((L : ℝ) / 2) * inner ℝ (Y - X) (Y - X)) /
            ((L : ℝ) * R ^ 2)
      rw [real_inner_smul_left, hXY]
      simp only [real_inner_smul_left, real_inner_smul_right]
      field_simp [hL0, hR0] <;> ring
    rw [hright]
    change
      (f Y - f xStar) / ((L : ℝ) * R ^ 2) ≤
        (f X - f xStar
            + inner ℝ (g X) (Y - X)
            + ((L : ℝ) / 2) * inner ℝ (Y - X) (Y - X)) /
          ((L : ℝ) * R ^ 2)
    rw [div_le_div_iff_of_pos_right hA]
    linarith [h.upperModel X Y]

end SmoothScaling

end ActualFunction
end LeanPEP
