import LeanPEP.ActualFunction.HuberWitnessTrajectory
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

/-!
# Analytic regularity of the one-dimensional Huber witness

The previous Huber-witness slices established an exact first-order
smooth-convex contract and proved that the actual unit-step gradient-descent
trajectory attains the normalized bound `1 / (4N + 2)`.

This file closes the remaining analysis-facing regularity obligations for the
same explicit function/gradient pair.  It proves:

* `huberFunction a` has derivative `huberGradient a x` at every `x`;
* the derivative field is monotone, hence the function is convex on `Set.univ`;
* `huberGradient a = min · a` is `1`-Lipschitz; and
* the pair belongs to `IsOneSmoothConvexAnalytic`.

The proof at the joining point glues the quadratic derivative on `Set.Iic a`
and the affine derivative on `Set.Ici a`.  No finite-PEP witness, external
solver, floating-point calculation, or interpolation-completeness theorem is
used.
-/

noncomputable section

namespace LeanPEP
namespace ActualFunction
namespace HuberWitness

open Set
open Filter
open scoped Topology
open ParametricGDActual
open Toy.FiniteGD.ParametricUpper

/-- Derivative of the quadratic branch `x ↦ x^2 / 2`. -/
private theorem hasDerivAt_quadraticBranch (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
  have hsquare : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x)
  have hhalf :
      HasDerivAt
        (fun y : ℝ => y ^ 2 * ((1 : ℝ) / 2))
        ((2 * x) * ((1 : ℝ) / 2)) x :=
    hsquare.mul_const ((1 : ℝ) / 2)
  have hcoeff : (2 * x) * ((1 : ℝ) / 2) = x := by
    ring
  rw [hcoeff] at hhalf
  simpa [div_eq_mul_inv] using hhalf

/-- Derivative of the affine branch `x ↦ a*x - a^2/2`. -/
private theorem hasDerivAt_affineBranch (a x : ℝ) :
    HasDerivAt (fun y : ℝ => a * y - a ^ 2 / 2) a x := by
  have hlinear : HasDerivAt (fun y : ℝ => a * y) a x := by
    simpa using (hasDerivAt_id x).const_mul a
  simpa using hlinear.sub_const (a ^ 2 / 2)

/-- The Huber function has the clipped derivative at every point, including
at the joining point. -/
theorem huberFunction_hasDerivAt (a x : ℝ) :
    HasDerivAt (huberFunction a) (huberGradient a x) x := by
  rcases lt_trichotomy x a with hxa | hxa | hax
  · have hEq :
        huberFunction a =ᶠ[𝓝 x] (fun y : ℝ => y ^ 2 / 2) := by
      filter_upwards [Iio_mem_nhds hxa] with y hy
      exact huberFunction_of_le (le_of_lt hy)
    have hderiv := (hasDerivAt_quadraticBranch x).congr_of_eventuallyEq hEq
    have hgrad : huberGradient a x = x :=
      huberGradient_of_le (le_of_lt hxa)
    simpa [hgrad] using hderiv
  · subst x
    have hleft :
        HasDerivWithinAt (huberFunction a) a (Iic a) a := by
      apply (hasDerivAt_quadraticBranch a).hasDerivWithinAt.congr_of_mem
      · intro y hy
        exact huberFunction_of_le hy
      · exact mem_Iic.mpr le_rfl
    have hright :
        HasDerivWithinAt (huberFunction a) a (Ici a) a := by
      apply (hasDerivAt_affineBranch a a).hasDerivWithinAt.congr_of_mem
      · intro y hy
        exact huberFunction_of_ge hy
      · exact mem_Ici.mpr le_rfl
    have hcover : Iic a ∪ Ici a = (Set.univ : Set ℝ) := by
      ext y
      simp only [mem_union, mem_Iic, mem_Ici, mem_univ, iff_true]
      exact le_total y a
    have hnhds : Iic a ∪ Ici a ∈ 𝓝 a := by
      rw [hcover]
      exact univ_mem
    have hjoin : HasDerivAt (huberFunction a) a a :=
      (hleft.union hright).hasDerivAt hnhds
    have hgrad : huberGradient a a = a :=
      huberGradient_of_ge le_rfl
    simpa [hgrad] using hjoin
  · have hEq :
        huberFunction a =ᶠ[𝓝 x]
          (fun y : ℝ => a * y - a ^ 2 / 2) := by
      filter_upwards [Ioi_mem_nhds hax] with y hy
      exact huberFunction_of_ge (le_of_lt hy)
    have hderiv := (hasDerivAt_affineBranch a x).congr_of_eventuallyEq hEq
    have hgrad : huberGradient a x = a :=
      huberGradient_of_ge (le_of_lt hax)
    simpa [hgrad] using hderiv

/-- The ordinary one-dimensional derivative equals the supplied clipped
field. -/
@[simp] theorem deriv_huberFunction (a x : ℝ) :
    deriv (huberFunction a) x = huberGradient a x :=
  (huberFunction_hasDerivAt a x).deriv

/-- The explicit Huber function is differentiable everywhere. -/
theorem huberFunction_differentiable (a : ℝ) :
    Differentiable ℝ (huberFunction a) :=
  fun x => (huberFunction_hasDerivAt a x).differentiableAt

/-- The clipped gradient field is monotone. -/
theorem huberGradient_monotone (a : ℝ) :
    Monotone (huberGradient a) := by
  intro x y hxy
  change min x a ≤ min y a
  exact min_le_min hxy le_rfl

/-- Convexity of the explicit function, derived from differentiability and
monotonicity of its derivative. -/
theorem huberFunction_convexOn (a : ℝ) :
    ConvexOn ℝ Set.univ (huberFunction a) := by
  apply Monotone.convexOn_univ_of_deriv (huberFunction_differentiable a)
  intro x y hxy
  rw [deriv_huberFunction, deriv_huberFunction]
  exact huberGradient_monotone a hxy

/-- The clipped gradient is nonexpansive. -/
theorem huberGradient_lipschitz (a : ℝ) :
    LipschitzWith 1 (huberGradient a) := by
  change LipschitzWith 1 (fun x : ℝ => min x a)
  exact (LipschitzWith.id : LipschitzWith 1 (fun x : ℝ => x)).min_const a

/-- One-dimensional derivative information expressed in the gradient API. -/
theorem huberFunction_hasGradientAt (a x : ℝ) :
    HasGradientAt (huberFunction a) (huberGradient a x) x :=
  (huberFunction_hasDerivAt a x).hasGradientAt'

/-- Full analysis-facing normalized smooth-convex contract for the explicit
Huber pair. -/
theorem analytic (a : ℝ) :
    IsOneSmoothConvexAnalytic (huberFunction a) (huberGradient a) where
  hasGradientAt := huberFunction_hasGradientAt a
  convexOn := huberFunction_convexOn a
  gradientLipschitz := huberGradient_lipschitz a

/-- Derivative of the parameterized witness function. -/
theorem witnessFunction_hasDerivAt (N : ℕ) (x : ℝ) :
    HasDerivAt (witnessFunction N) (witnessGradient N x) x := by
  simpa [witnessFunction, witnessGradient] using
    huberFunction_hasDerivAt (threshold N) x

/-- Gradient form of the parameterized witness derivative. -/
theorem witnessFunction_hasGradientAt (N : ℕ) (x : ℝ) :
    HasGradientAt (witnessFunction N) (witnessGradient N x) x :=
  (witnessFunction_hasDerivAt N x).hasGradientAt'

/-- The parameterized clipped gradient is `1`-Lipschitz. -/
theorem witnessGradient_lipschitz (N : ℕ) :
    LipschitzWith 1 (witnessGradient N) := by
  simpa [witnessGradient] using huberGradient_lipschitz (threshold N)

/-- The parameterized witness belongs to the standard analytic class used by
the universal actual-function upper theorem. -/
theorem witness_analytic (N : ℕ) :
    IsOneSmoothConvexAnalytic (witnessFunction N) (witnessGradient N) := by
  simpa [witnessFunction, witnessGradient] using analytic (threshold N)

/-- Proof-carrying normalized analytic lower witness.  This reuses the D2
actual trajectory and attainment theorem without changing its formulas. -/
theorem normalized_analytic_lower_witness (N : ℕ) :
    IsOneSmoothConvexAnalytic (witnessFunction N) (witnessGradient N) ∧
      witnessGradient N 0 = 0 ∧
      (∀ x : ℝ, witnessFunction N 0 ≤ witnessFunction N x) ∧
      ‖(1 : ℝ) - 0‖ ^ 2 ≤ 1 ∧
      witnessFunction N
          (unitGDIterate (witnessGradient N) 1 N) -
        witnessFunction N 0 = (gdBoundQ N : ℝ) := by
  refine ⟨witness_analytic N, witnessGradient_zero N,
    witness_zero_isGlobalMin N, ?_, witness_unitGD_attains_bound N⟩
  norm_num

end HuberWitness
end ActualFunction
end LeanPEP
