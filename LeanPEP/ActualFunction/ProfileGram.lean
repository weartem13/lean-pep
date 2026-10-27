import LeanPEP.ActualFunction.FiniteGram
import LeanPEP.ActualFunction.AffineEvaluationCore
import LeanPEP.GramPEP.UpperCertificateChecker
import LeanPEP.Profiles.GramCompilation

/-!
# Actual-function soundness for compiled fixed-step profiles

This is a soundness bridge for ANY `PEPProfileQ`, not a second algorithm or
Gram model.  Sampled positions satisfy the profile's cumulative update; their
actual gradients and the centered initial displacement form an ambient vector
family (not necessarily a linearly independent basis).  `FiniteGram` supplies
the exact real Gram matrix, PSD proof, and interpolation-slack interpretation.

The existing `ParametricGDHilbert.evalVector` and its generic affine evaluation
lemmas are reused without modifying the GD certificate.  Here they are linked
to `GramCompilation.affineVecQ` once, for arbitrary affine forms.

The first-order entry point requires only a real inner-product space.  The
analytic entry point uses the existing analytic-to-first-order theorem on a
real Hilbert space.  Neither entry point assumes interpolation completeness.
-/

namespace LeanPEP.ActualFunction.ProfileGram

open scoped BigOperators
open LeanPEP.Toy.FiniteGD (GradAffineQ Point)
open LeanPEP.Profiles.FixedStepFirstOrder
open LeanPEP.Profiles.GramCompilation
open LeanPEP.GramPEP
open LeanPEP.ActualFunction.ParametricGDHilbert (evalVector linearCombination)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Ambient point associated with a source point label. -/
def samplePoint {N : ℕ} (xStar : E) (points : Fin (N + 1) → E) : Point N → E
  | .star => xStar
  | .iter i => points i

/-- Actual samples in the compiler's fixed point order. -/
def orderedSamples {N : ℕ} (xStar : E) (points : Fin (N + 1) → E) :
    Fin (N + 2) → E :=
  fun i => samplePoint xStar points (pointAtIndex i)

@[simp] theorem orderedSamples_pointIndex {N : ℕ}
    (xStar : E) (points : Fin (N + 1) → E) (i : Point N) :
    orderedSamples xStar points (pointIndex i) = samplePoint xStar points i := by
  simp [orderedSamples]

/-- Ambient vectors in the fixed order `(x0-xStar, g(points 0), ..., g(points N))`.
No independence, nonzero-radius, or full-rank assumption is imposed. -/
def sampleBase {N : ℕ} (g : E → E) (xStar x0 : E)
    (points : Fin (N + 1) → E) : Fin (N + 2) → E :=
  Fin.cases (x0 - xStar) (fun i => g (points i))

/-- A standard rational coefficient vector selects its ambient vector. -/
@[simp] theorem realize_standardBasisQ {m : ℕ} (base : Fin m → E) (i : Fin m) :
    FiniteGram.realize base (castVecQ (standardBasisExpr (𝕜 := ℚ) i)) = base i := by
  classical
  unfold FiniteGram.realize
  rw [Fintype.sum_eq_single i (by
    intro j hji
    simp [castVecQ, standardBasisExpr, hji])]
  simp [castVecQ, standardBasisExpr]

/-- Homogenization and ambient affine evaluation agree exactly. -/
theorem realize_affineVecQ {N : ℕ} (a : GradAffineQ N)
    (g : E → E) (xStar x0 : E) (points : Fin (N + 1) → E) :
    FiniteGram.realize (sampleBase g xStar x0 points) (castVecQ (affineVecQ a)) =
      evalVector a (x0 - xStar) (fun i => g (points i)) := by
  unfold FiniteGram.realize
  rw [Fin.sum_univ_succ] <;> rfl

@[simp] theorem realize_initialBasisQ {N : ℕ}
    (g : E → E) (xStar x0 : E) (points : Fin (N + 1) → E) :
    FiniteGram.realize (sampleBase g xStar x0 points) (castVecQ (initialBasisQ N)) =
      x0 - xStar := by
  rw [initialBasisQ, realize_standardBasisQ] <;> rfl

@[simp] theorem realize_sampledGradientBasisQ {N : ℕ}
    (g : E → E) (xStar x0 : E) (points : Fin (N + 1) → E) (i : Fin (N + 1)) :
    FiniteGram.realize (sampleBase g xStar x0 points)
        (castVecQ (sampledGradientBasisQ i)) = g (points i) := by
  rw [sampledGradientBasisQ, realize_standardBasisQ] <;> rfl

/-- Ambient semantic contract for the compiled cumulative update equations.
The momentum layer proves this contract from its actual state/query recurrence. -/
def RealizesProfile {N : ℕ} (profile : ProfileQ N) (g : E → E)
    (xStar x0 : E) (points : Fin (N + 1) → E) : Prop :=
  ∀ i, evalVector (iterateAffineQ profile i) (x0 - xStar)
      (fun j => g (points j)) = points i - xStar

/-- The semantic contract is exactly the ordinary fixed-step update equation,
not an independent assumption of finite-PEP feasibility. -/
theorem realizesProfile_iff_updates {N : ℕ} (profile : ProfileQ N) (g : E → E)
    (xStar x0 : E) (points : Fin (N + 1) → E) :
    RealizesProfile profile g xStar x0 points ↔
      ∀ i, points i = x0 - ∑ j, (profile.stepCoeff i j : ℝ) • g (points j) := by
  have heval (i : Fin (N + 1)) :
      evalVector (iterateAffineQ profile i) (x0 - xStar) (fun j => g (points j)) =
        (x0 - xStar) - ∑ j, (profile.stepCoeff i j : ℝ) • g (points j) := by
    simp [evalVector, linearCombination, sub_eq_add_neg]
  constructor
  · intro h i
    have hi := h i
    rw [heval] at hi
    calc
      points i = (points i - xStar) + xStar := by abel
      _ = ((x0 - xStar) - ∑ j, (profile.stepCoeff i j : ℝ) • g (points j)) + xStar :=
        congrArg (fun z : E => z + xStar) hi.symm
      _ = x0 - ∑ j, (profile.stepCoeff i j : ℝ) • g (points j) := by abel
  · intro h i
    rw [heval, h i]
    abel

/-- The entire compiler-generated model has the intended ambient meaning. -/
theorem realizesActualSamples {N : ℕ} (profile : PEPProfileQ N)
    (g : E → E) (xStar x0 : E) (points : Fin (N + 1) → E)
    (hstationary : g xStar = 0)
    (htrajectory : RealizesProfile profile.algorithm g xStar x0 points) :
    FiniteGram.RealizesActualSamples (sampleBase g xStar x0 points)
      (compileModelQ profile) (orderedSamples xStar points) xStar g := by
  constructor
  · intro k
    obtain ⟨i, rfl⟩ := pointIndex_surjective k
    rw [compileModelQ_position_pointIndex, orderedSamples_pointIndex]
    cases i with
    | star =>
        change FiniteGram.realize (sampleBase g xStar x0 points)
          (castVecQ (affineVecQ (GradAffineQ.zero N))) = xStar - xStar
        rw [realize_affineVecQ]
        simp
    | iter i =>
        change FiniteGram.realize (sampleBase g xStar x0 points)
          (castVecQ (affineVecQ (iterateAffineQ profile.algorithm i))) = points i - xStar
        rw [realize_affineVecQ]
        exact htrajectory i
  · intro k
    obtain ⟨i, rfl⟩ := pointIndex_surjective k
    rw [compileModelQ_gradient_pointIndex, orderedSamples_pointIndex]
    cases i with
    | star =>
        change FiniteGram.realize (sampleBase g xStar x0 points)
          (castVecQ (0 : VecExpr (N + 2) ℚ)) = g xStar
        simp [FiniteGram.realize, castVecQ, hstationary]
    | iter i =>
        exact realize_sampledGradientBasisQ g xStar x0 points i

/-- Real finite Gram data, using the original compiler and `FiniteGram`. -/
noncomputable def profileData {N : ℕ} (profile : PEPProfileQ N)
    (f : E → ℝ) (g : E → E) (xStar x0 : E) (points : Fin (N + 1) → E) :
    DataR (Fin (N + 2)) (N + 2) :=
  FiniteGram.dataOfModel (sampleBase g xStar x0 points)
    (compileModelQ profile) (orderedSamples xStar points) f

theorem profileData_realizesModel {N : ℕ} (profile : PEPProfileQ N)
    (f : E → ℝ) (g : E → E) (xStar x0 : E) (points : Fin (N + 1) → E) :
    RealizesModelQ (compileModelQ profile) (profileData profile f g xStar x0 points) :=
  FiniteGram.dataOfModel_realizes _ _ _ _

/-- Every ordered Gram slack is the corresponding actual-function slack. -/
theorem profileData_interpolationSlack {N : ℕ} (profile : PEPProfileQ N)
    (f : E → ℝ) (g : E → E) (xStar x0 : E) (points : Fin (N + 1) → E)
    (hstationary : g xStar = 0)
    (htrajectory : RealizesProfile profile.algorithm g xStar x0 points)
    (i j : Fin (N + 2)) :
    GramPEP.interpolationSlack (profileData profile f g xStar x0 points) i j =
      ActualFunction.interpolationSlack f g
        (orderedSamples xStar points i) (orderedSamples xStar points j) :=
  FiniteGram.interpolationSlack_dataOfModel
    (realizesActualSamples profile g xStar x0 points hstationary htrajectory) i j

/-- First-order smooth-convex assumptions imply all interpolation inequalities
and a genuine PSD Gram matrix, without assuming completeness of the ambient space. -/
theorem profileData_coreFeasible {N : ℕ} (profile : PEPProfileQ N)
    {f : E → ℝ} {g : E → E} {xStar x0 : E} {points : Fin (N + 1) → E}
    (hfun : IsOneSmoothConvexFirstOrder f g)
    (hstationary : g xStar = 0)
    (htrajectory : RealizesProfile profile.algorithm g xStar x0 points) :
    CoreFeasible (profileData profile f g xStar x0 points) := by
  refine ⟨FiniteGram.gramOfVectors_posSemidef _, ?_⟩
  intro i j
  rw [profileData_interpolationSlack profile f g xStar x0 points hstationary htrajectory]
  exact ActualFunction.interpolationSlack_nonneg hfun _ _

/-- Exact evaluation of the compiler's radius assumption; it stays an inequality. -/
theorem profileData_initialRadius_eval {N : ℕ} (profile : PEPProfileQ N)
    (f : E → ℝ) (g : E → E) (xStar x0 : E) (points : Fin (N + 1) → E) :
    (initialRadiusExprQ profile.normalization).evalR
        (profileData profile f g xStar x0 points) =
      (profile.normalization.radiusSq : ℝ) - ‖x0 - xStar‖ ^ 2 := by
  rw [initialRadiusExprQ_evalR _ _ (FiniteGram.gramOfVectors_symmetric _)]
  change (profile.normalization.radiusSq : ℝ) -
    gramNormSq (FiniteGram.gramOfVectors (sampleBase g xStar x0 points))
      (castVecQ (initialBasisQ N)) = _
  rw [FiniteGram.gramNormSq_gramOfVectors, realize_initialBasisQ,
    real_inner_self_eq_norm_sq]

theorem profileData_assumptionsFeasible {N : ℕ} (profile : PEPProfileQ N)
    (f : E → ℝ) (g : E → E) (xStar x0 : E) (points : Fin (N + 1) → E)
    (hradius : ‖x0 - xStar‖ ^ 2 ≤ (profile.normalization.radiusSq : ℝ)) :
    AssumptionsFeasibleR (compileModelQ profile)
      (profileData profile f g xStar x0 points) := by
  intro k
  fin_cases k
  change 0 ≤ (initialRadiusExprQ profile.normalization).evalR
    (profileData profile f g xStar x0 points)
  rw [profileData_initialRadius_eval]
  exact sub_nonneg.mpr hradius

/-- Compiled objective evaluation preserves the declared target and reference. -/
@[simp] theorem profileData_objective_eval {N : ℕ} (profile : PEPProfileQ N)
    (f : E → ℝ) (g : E → E) (xStar x0 : E) (points : Fin (N + 1) → E) :
    (compileObjectiveQ profile).evalR (profileData profile f g xStar x0 points) =
      f (samplePoint xStar points profile.objective.target) -
        f (samplePoint xStar points profile.objective.reference) := by
  change (objectiveExprQ profile.objective).evalR _ = _
  rw [objectiveExprQ_evalR]
  simp [profileData]

/-- Complete feasibility package for any compiled fixed-step profile. -/
theorem profileData_feasible {N : ℕ} (profile : PEPProfileQ N)
    {f : E → ℝ} {g : E → E} {xStar x0 : E} {points : Fin (N + 1) → E}
    (hfun : IsOneSmoothConvexFirstOrder f g)
    (hstationary : g xStar = 0)
    (htrajectory : RealizesProfile profile.algorithm g xStar x0 points)
    (hradius : ‖x0 - xStar‖ ^ 2 ≤ (profile.normalization.radiusSq : ℝ)) :
    RealizesModelQ (compileModelQ profile) (profileData profile f g xStar x0 points) ∧
      CoreFeasible (profileData profile f g xStar x0 points) ∧
      AssumptionsFeasibleR (compileModelQ profile)
        (profileData profile f g xStar x0 points) :=
  ⟨profileData_realizesModel profile f g xStar x0 points,
    profileData_coreFeasible profile hfun hstationary htrajectory,
    profileData_assumptionsFeasible profile f g xStar x0 points hradius⟩

/-- An accepted general Gram certificate bounds the ACTUAL declared objective.
The objective equality is mandatory: checker acceptance alone is not sufficient. -/
theorem certificate_upper {N : ℕ} (profile : PEPProfileQ N)
    (c : GramPEP.UpperCertQ (compileModelQ profile))
    (hcheck : GramPEP.checkUpperCertQ c = true)
    (hobjective : c.objective = compileObjectiveQ profile)
    {f : E → ℝ} {g : E → E} {xStar x0 : E} {points : Fin (N + 1) → E}
    (hfun : IsOneSmoothConvexFirstOrder f g)
    (hstationary : g xStar = 0)
    (htrajectory : RealizesProfile profile.algorithm g xStar x0 points)
    (hradius : ‖x0 - xStar‖ ^ 2 ≤ (profile.normalization.radiusSq : ℝ)) :
    f (samplePoint xStar points profile.objective.target) -
      f (samplePoint xStar points profile.objective.reference) ≤ (c.bound : ℝ) := by
  have hfeasible := profileData_feasible profile hfun hstationary htrajectory hradius
  have hbound := GramPEP.checkUpperCertQ_sound_real c hcheck
    (profileData profile f g xStar x0 points)
    hfeasible.1 hfeasible.2.1 hfeasible.2.2
  rw [hobjective, profileData_objective_eval] at hbound
  exact hbound

/-- Analysis-facing wrapper through the existing analytic-to-first-order bridge. -/
theorem certificate_upper_analytic {N : ℕ} [CompleteSpace E]
    (profile : PEPProfileQ N) (c : GramPEP.UpperCertQ (compileModelQ profile))
    (hcheck : GramPEP.checkUpperCertQ c = true)
    (hobjective : c.objective = compileObjectiveQ profile)
    {f : E → ℝ} {g : E → E} {xStar x0 : E} {points : Fin (N + 1) → E}
    (hfun : IsOneSmoothConvexAnalytic f g)
    (hstationary : g xStar = 0)
    (htrajectory : RealizesProfile profile.algorithm g xStar x0 points)
    (hradius : ‖x0 - xStar‖ ^ 2 ≤ (profile.normalization.radiusSq : ℝ)) :
    f (samplePoint xStar points profile.objective.target) -
      f (samplePoint xStar points profile.objective.reference) ≤ (c.bound : ℝ) :=
  certificate_upper profile c hcheck hobjective hfun.toFirstOrder
    hstationary htrajectory hradius

end LeanPEP.ActualFunction.ProfileGram
