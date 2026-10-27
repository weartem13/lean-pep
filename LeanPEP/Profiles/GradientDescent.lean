import LeanPEP.Profiles.FixedStepFirstOrder
import LeanPEP.Toy.FiniteGD.ParametricUpperQuadraticDiagonal

/-!
# Gradient descent as an exact fixed-step profile

This module migrates the normalized arbitrary-length gradient-descent model to
the reusable fixed-step profile/compiler introduced in v0.13A1.

For unit-step GD, the cumulative coefficient of `g_j` in iterate `x_i` is `1`
precisely when `j < i`.  The main equivalence results prove that compiling this
profile reproduces, definition for definition at the coefficient-object level,
all of the legacy v0.12 objects:

* generated point positions;
* ordered interpolation polynomials;
* weighted interpolation sums;
* complete certificate right-hand sides; and
* executable checker acceptance.

Consequently the arbitrary-`N` certificate `gdUpperCertQ N` is accepted through
the profile-aware checker without changing the certificate, polynomial syntax,
or exact coefficient checker.  This is a migration theorem, not a second
hard-coded GD implementation.
-/

namespace LeanPEP
namespace Profiles
namespace GradientDescent

open LeanPEP.Toy.FiniteGD
open LeanPEP.Toy.FiniteGD.ParametricUpper
open LeanPEP.Profiles.FixedStepFirstOrder

/-- Cumulative unit-step GD coefficient: `g_j` occurs in `x_i` exactly when
`j < i`. -/
def unitStepCoeffQ
    {N : ℕ} (i j : Fin (N + 1)) : ℚ :=
  if j.val < i.val then 1 else 0

/-- Unit-step GD coefficients are causal. -/
theorem unitStepCoeffQ_causal
    {N : ℕ} (i j : Fin (N + 1))
    (hij : i.val ≤ j.val) :
    unitStepCoeffQ i j = 0 := by
  simp [unitStepCoeffQ, not_lt_of_ge hij]

/-- Exact normalized unit-step gradient-descent algorithm profile. -/
def unitGDProfileQ (N : ℕ) : ProfileQ N :=
  { stepCoeff := unitStepCoeffQ
    causal := unitStepCoeffQ_causal }

@[simp] theorem unitGDProfileQ_stepCoeff
    {N : ℕ} (i j : Fin (N + 1)) :
    (unitGDProfileQ N).stepCoeff i j =
      if j.val < i.val then 1 else 0 := rfl

/-- The compiled cumulative gradient combination is exactly the legacy
symbolic prefix. -/
theorem gradientCombinationAffineQ_unitGD
    {N : ℕ} (i : Fin (N + 1)) :
    gradientCombinationAffineQ (unitGDProfileQ N) i =
      GradAffineQ.prefixAffine i.val (Nat.le_of_lt i.isLt) := by
  apply GradAffineQ.ext
  · change 0 =
      (GradAffineQ.prefixAffine i.val (Nat.le_of_lt i.isLt)).constCoeff
    exact (prefixAffine_constCoeff i.val (Nat.le_of_lt i.isLt)).symm
  · funext j
    simp [gradientCombinationAffineQ, unitGDProfileQ, unitStepCoeffQ,
      prefixAffine_gradCoeff]

/-- Compiling one unit-step GD iterate reproduces the legacy `xAffineQ`
position exactly. -/
theorem iterateAffineQ_unitGD
    {N : ℕ} (i : Fin (N + 1)) :
    iterateAffineQ (unitGDProfileQ N) i =
      xAffineQ (Point.iter i) := by
  unfold iterateAffineQ
  rw [gradientCombinationAffineQ_unitGD]
  rfl

/-- Pointwise position-compiler equivalence, including the optimum point. -/
@[simp] theorem pointAffineQ_unitGD
    {N : ℕ} (i : Point N) :
    pointAffineQ (unitGDProfileQ N) i = xAffineQ i := by
  cases i with
  | star => rfl
  | iter k => exact iterateAffineQ_unitGD k

/-- Scalar evaluation of the compiled GD position is the existing normalized
finite-GD position. -/
@[simp] theorem pointPositionR_unitGD
    {N : ℕ} (d : DataR N) (i : Point N) :
    pointPositionR (unitGDProfileQ N) d i = x d i := by
  simp [pointPositionR]

/-- Every compiled unit-step GD interpolation polynomial is exactly the legacy
v0.12 interpolation polynomial. -/
@[simp] theorem interpolationPolyQ_unitGD
    {N : ℕ} (i j : Point N) :
    interpolationPolyQ (unitGDProfileQ N) i j =
      slackPolyQ i j := by
  simp [interpolationPolyQ, slackPolyQ]

/-- The profile-generated real interpolation slack is exactly the legacy GD
slack. -/
@[simp] theorem interpolationSlackR_unitGD
    {N : ℕ} (d : DataR N) (i j : Point N) :
    interpolationSlackR (unitGDProfileQ N) d i j =
      slack d i j := by
  rw [← evalR_interpolationPolyQ]
  simp

/-- Profile feasibility for unit-step GD is equivalent to the original v0.12
finite-GD feasibility proposition. -/
theorem feasibleR_unitGD_iff
    {N : ℕ} (d : DataR N) :
    FeasibleR (unitGDProfileQ N) d ↔ Feasible d := by
  constructor
  · intro h i j
    simpa using h i j
  · intro h i j
    simpa using h i j

/-- Weighted interpolation sums compiled from unit-step GD are identical to the
legacy sums. -/
theorem interpPolySumQ_unitGD
    {N : ℕ} (terms : List (InterpTermQ N)) :
    FixedStepFirstOrder.interpPolySumQ (unitGDProfileQ N) terms =
      LeanPEP.Toy.FiniteGD.interpPolySumQ terms := by
  induction terms with
  | nil => rfl
  | cons t ts ih =>
      simp [FixedStepFirstOrder.interpPolySumQ,
        LeanPEP.Toy.FiniteGD.interpPolySumQ, ih]

/-- The complete profile-compiled GD certificate right-hand side is exactly the
legacy one. -/
@[simp] theorem certificateRhsPolyQ_unitGD
    {N : ℕ} (c : UpperCertQ N) :
    FixedStepFirstOrder.certificateRhsPolyQ (unitGDProfileQ N) c =
      LeanPEP.Toy.FiniteGD.certificateRhsPolyQ c := by
  simp [FixedStepFirstOrder.certificateRhsPolyQ,
    LeanPEP.Toy.FiniteGD.certificateRhsPolyQ,
    interpPolySumQ_unitGD]

/-- For unit-step GD, the new profile checker is extensionally the existing
checker on every certificate. -/
theorem checkUpperCertQ_unitGD
    {N : ℕ} (c : UpperCertQ N) :
    FixedStepFirstOrder.checkUpperCertQ (unitGDProfileQ N) c =
      LeanPEP.Toy.FiniteGD.checkUpperCertQ c := by
  simp [FixedStepFirstOrder.checkUpperCertQ,
    LeanPEP.Toy.FiniteGD.checkUpperCertQ]

/-- The arbitrary-length closed-form GD certificate is accepted through the
profile-aware checker for every `N`. -/
theorem gdUpperCertQ_profile_check_all
    (N : ℕ) :
    FixedStepFirstOrder.checkUpperCertQ
      (unitGDProfileQ N) (gdUpperCertQ N) = true := by
  rw [checkUpperCertQ_unitGD]
  exact gdUpperCertQ_check_all N

/-- Universal normalized finite-GD upper theorem routed through the new
profile/compiler path. -/
theorem gd_profile_upper_all
    (N : ℕ) (d : DataR N)
    (hfeasible : FeasibleR (unitGDProfileQ N) d) :
    d.value (gdObjective N) ≤ (gdBoundQ N : ℝ) := by
  simpa [gdUpperCertQ] using
    FixedStepFirstOrder.checkUpperCertQ_sound_real
      (unitGDProfileQ N) (gdUpperCertQ N)
      (gdUpperCertQ_profile_check_all N) d hfeasible

/-- The profile-routed theorem has exactly the same feasibility premise and
conclusion as the legacy theorem. -/
theorem gd_profile_upper_all_of_legacy_feasible
    (N : ℕ) (d : DataR N) (hfeasible : Feasible d) :
    d.value (gdObjective N) ≤ (gdBoundQ N : ℝ) :=
  gd_profile_upper_all N d ((feasibleR_unitGD_iff d).2 hfeasible)

end GradientDescent
end Profiles
end LeanPEP
