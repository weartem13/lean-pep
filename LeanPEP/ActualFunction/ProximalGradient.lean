import LeanPEP.ActualFunction.Composite
import LeanPEP.ActualFunction.ProfileGram
import LeanPEP.Profiles.ProximalGradient

/-!
# Actual positive-horizon proximal-gradient runs and compiler soundness

An `IsProxRun N h g x` supplies ordinary global prox minimizers for exactly
N updates. No selected prox map and no proximal existence axiom are needed.
The residuals are extracted as `x_k - g(x_k) - x_(k+1)`.

The profile parameter `n` means `N = n+1` steps. `IsProxRun 0` is allowed
and vacuous, but no zero-step composite objective/rate is claimed. A radius
alone does not bound a general nonsmooth initial objective gap.
-/

noncomputable section
namespace LeanPEP.ActualFunction.ProximalGradient

open LeanPEP.GramPEP
open LeanPEP.Profiles.ProximalGradient
open Proximal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Ordinary unit proximal minimization at each of N steps. -/
def IsProxRun (N : ℕ) (h : E → ℝ) (g : E → E) (x : ℕ → E) : Prop :=
  ∀ k < N, IsUnitProxPoint h (x k - g (x k)) (x (k + 1))

/-- Residual-oracle form of the SAME run, not a separate algorithm. -/
def IsResidualRun (N : ℕ) (h : E → ℝ) (g : E → E) (x s : ℕ → E) : Prop :=
  ∀ k < N, IsUnitForwardBackwardStep h (g (x k)) (x k) (x (k + 1)) (s k)

def residual (g : E → E) (x : ℕ → E) (k : ℕ) : E :=
  x k - g (x k) - x (k + 1)

@[simp] theorem isProxRun_zero (h : E → ℝ) (g : E → E) (x : ℕ → E) :
    IsProxRun 0 h g x := by
  intro k hk
  omega

theorem IsProxRun.restrict {M N : ℕ} {h : E → ℝ} {g : E → E} {x : ℕ → E}
    (hrun : IsProxRun N h g x) (hmn : M ≤ N) : IsProxRun M h g x := by
  intro k hk
  exact hrun k (by omega)

theorem IsResidualRun.toProxRun {N : ℕ} {h : E → ℝ} {g : E → E} {x s : ℕ → E}
    (hrun : IsResidualRun N h g x s) : IsProxRun N h g x := by
  intro k hk
  exact (hrun k hk).prox

theorem IsProxRun.toResidualRun {N : ℕ} {h : E → ℝ} {g : E → E} {x : ℕ → E}
    (hrun : IsProxRun N h g x) (hh : ConvexOn ℝ Set.univ h) :
    IsResidualRun N h g x (residual g x) := by
  intro k hk
  exact forwardBackwardStep_of_prox hh (hrun k hk)

/-- Residuals are forced by the update, not arbitrarily chosen subgradients. -/
theorem IsResidualRun.residual_eq {N : ℕ} {h : E → ℝ} {g : E → E} {x s : ℕ → E}
    (hrun : IsResidualRun N h g x s) (k : ℕ) (hk : k < N) :
    s k = residual g x k := by
  have hu := (hrun k hk).update
  unfold residual
  rw [hu]
  abel

theorem isProxRun_iff_residual {N : ℕ} {h : E → ℝ} {g : E → E} {x : ℕ → E}
    (hh : ConvexOn ℝ Set.univ h) :
    IsProxRun N h g x ↔ IsResidualRun N h g x (residual g x) :=
  ⟨fun hp => hp.toResidualRun hh, fun hr => hr.toProxRun⟩

/-- Actual samples; no nonsmooth oracle at x_0 is requested. -/
def smoothPoints (n : ℕ) (xStar : E) (x : ℕ → E) : Fin (n + 3) → E :=
  Fin.cases xStar (fun i => x i.val)

def nonsmoothPoints (n : ℕ) (xStar : E) (x : ℕ → E) : Fin (n + 2) → E :=
  Fin.cases xStar (fun j => x (j.val + 1))

def nonsmoothOracles (n : ℕ) (gStar : E) (s : ℕ → E) : Fin (n + 2) → E :=
  Fin.cases (-gStar) (fun j => s j.val)

def baseVectors (n : ℕ) (g : E → E) (xStar : E) (x s : ℕ → E) :
    Fin (basisCount n) → E :=
  Fin.addCases
    (Fin.cases (x 0 - xStar) (Fin.cases (g xStar) (fun i => g (x i.val))))
    (fun j => s j.val)

def valueSlots (n : ℕ) (f h : E → ℝ) (xStar : E) (x : ℕ → E) :
    Fin (valueCount n) → ℝ :=
  Fin.addCases (fun i => f (smoothPoints n xStar x i))
    (fun j => h (nonsmoothPoints n xStar x j))

@[simp] theorem valueSlots_smooth (n : ℕ) (f h : E → ℝ) (xStar : E) (x : ℕ → E)
    (i : Fin (n + 3)) :
    valueSlots n f h xStar x (smoothValueIndex i) = f (smoothPoints n xStar x i) := by
  simp [valueSlots, smoothValueIndex]

@[simp] theorem valueSlots_nonsmooth (n : ℕ) (f h : E → ℝ) (xStar : E) (x : ℕ → E)
    (i : Fin (n + 2)) :
    valueSlots n f h xStar x (nonsmoothValueIndex i) = h (nonsmoothPoints n xStar x i) := by
  simp [valueSlots, nonsmoothValueIndex]

def actualData (n : ℕ) (f h : E → ℝ) (g : E → E) (xStar : E) (x s : ℕ → E) :
    DataR (Fin (valueCount n)) (basisCount n) :=
  Composite.dataOfValues (baseVectors n g xStar x s) (valueSlots n f h xStar x)

@[simp] theorem realize_initial (n : ℕ) (g : E → E) (xStar : E) (x s : ℕ → E) :
    FiniteGram.realize (baseVectors n g xStar x s) (castVecQ (initialVecQ n)) =
      x 0 - xStar := by
  rw [initialVecQ, ProfileGram.realize_standardBasisQ]
  simp [baseVectors, initialBasisIndex]

@[simp] theorem realize_starGradient (n : ℕ) (g : E → E) (xStar : E) (x s : ℕ → E) :
    FiniteGram.realize (baseVectors n g xStar x s) (castVecQ (starGradientQ n)) =
      g xStar := by
  rw [starGradientQ, ProfileGram.realize_standardBasisQ]
  have hindex : (1 : Fin (n + 4)) = (0 : Fin (n + 3)).succ := by
    apply Fin.ext
    rfl
  simp only [baseVectors, starBasisIndex, Fin.addCases_left, hindex,
    Fin.cases_succ, Fin.cases_zero]

@[simp] theorem realize_gradient (n : ℕ) (g : E → E) (xStar : E) (x s : ℕ → E)
    (i : Fin (n + 2)) :
    FiniteGram.realize (baseVectors n g xStar x s) (castVecQ (gradientVecQ i)) =
      g (x i.val) := by
  rw [gradientVecQ, ProfileGram.realize_standardBasisQ]
  simp [baseVectors, gradientBasisIndex]

@[simp] theorem realize_residual (n : ℕ) (g : E → E) (xStar : E) (x s : ℕ → E)
    (j : Fin (n + 1)) :
    FiniteGram.realize (baseVectors n g xStar x s) (castVecQ (residualVecQ j)) =
      s j.val := by
  rw [residualVecQ, ProfileGram.realize_standardBasisQ]
  simp [baseVectors, residualBasisIndex]

/-- Symbolic trajectory realization follows from ordinary local updates.
It is proved, not left as a premise of the final actual-function theorem. -/
theorem position_realization {n : ℕ} {g : E → E} {x s : ℕ → E} (xStar : E)
    (hu : ∀ k < n + 1, x (k + 1) = x k - g (x k) - s k)
    (k : ℕ) (hk : k ≤ n + 1) :
    FiniteGram.realize (baseVectors n g xStar x s) (castVecQ (positionVecQ n k)) =
      x k - xStar := by
  revert hk
  induction k with
  | zero => intro _; exact realize_initial n g xStar x s
  | succ k ih =>
      intro hk
      have hk' : k < n + 1 := by omega
      let j : Fin (n + 1) := ⟨k, hk'⟩
      rw [show positionVecQ n (k + 1) =
          positionVecQ n k - gradientVecQ j.castSucc - residualVecQ j from
        positionVecQ_succ j]
      rw [castVecQ_sub, castVecQ_sub, FiniteGram.realize_sub, FiniteGram.realize_sub,
        realize_gradient, realize_residual, ih (by omega), hu k hk']
      change (x k - xStar) - g (x k) - s k = (x k - g (x k) - s k) - xStar
      abel

theorem smoothSamples_denote {n : ℕ} (f h : E → ℝ) (g : E → E)
    (xStar : E) (x s : ℕ → E)
    (hu : ∀ k < n + 1, x (k + 1) = x k - g (x k) - s k) (i : Fin (n + 3)) :
    Composite.SampleDenotes (baseVectors n g xStar x s) (valueSlots n f h xStar x)
      xStar (smoothSamplesQ n i) (smoothPoints n xStar x i)
        (g (smoothPoints n xStar x i)) (f (smoothPoints n xStar x i)) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Composite.SampleDenotes, smoothSamplesQ, smoothPoints, valueSlots,
      smoothValueIndex]
  · have hx := position_realization xStar hu j.val (by omega)
    simp [Composite.SampleDenotes, smoothSamplesQ, smoothPoints, valueSlots,
      smoothValueIndex, hx]

theorem nonsmoothSamples_denote {n : ℕ} (f h : E → ℝ) (g : E → E)
    (xStar : E) (x s : ℕ → E)
    (hu : ∀ k < n + 1, x (k + 1) = x k - g (x k) - s k) (i : Fin (n + 2)) :
    Composite.SampleDenotes (baseVectors n g xStar x s) (valueSlots n f h xStar x)
      xStar (nonsmoothSamplesQ n i) (nonsmoothPoints n xStar x i)
        (nonsmoothOracles n (g xStar) s i) (h (nonsmoothPoints n xStar x i)) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Composite.SampleDenotes, nonsmoothSamplesQ, nonsmoothPoints,
      nonsmoothOracles, valueSlots, nonsmoothValueIndex, castVecQ_neg,
      FiniteGram.realize_neg]
  · have hx := position_realization xStar hu (j.val + 1) (by omega)
    simp [Composite.SampleDenotes, nonsmoothSamplesQ, nonsmoothPoints,
      nonsmoothOracles, valueSlots, nonsmoothValueIndex, hx]

/-- The exact radius-inequality interpretation, including rational cast 1. -/
theorem radius_eval (n : ℕ) (f h : E → ℝ) (g : E → E)
    (xStar : E) (x s : ℕ → E) :
    (radiusExprQ n).evalR (actualData n f h g xStar x s) = 1 - ‖x 0 - xStar‖ ^ 2 := by
  simp only [radiusExprQ, LinearExprQ.evalR_sub, LinearExprQ.evalR_const, Rat.cast_one]
  rw [LinearExprQ.evalR_gramNorm _ _
    (FiniteGram.gramOfVectors_symmetric (baseVectors n g xStar x s))]
  change 1 - gramNormSq (FiniteGram.gramOfVectors (baseVectors n g xStar x s))
    (castVecQ (initialVecQ n)) = _
  rw [FiniteGram.gramNormSq_gramOfVectors, realize_initial, real_inner_self_eq_norm_sq]

@[simp] theorem objective_eval (n : ℕ) (f h : E → ℝ) (g : E → E)
    (xStar : E) (x s : ℕ → E) :
    (objectiveQ n).evalR (actualData n f h g xStar x s) =
      (f (x (n + 1)) + h (x (n + 1))) - (f xStar + h xStar) := by
  have hfLast : smoothPoints n xStar x (Fin.last (n + 2)) = x (n + 1) := rfl
  have hhLast : nonsmoothPoints n xStar x (Fin.last (n + 1)) = x (n + 1) := rfl
  have hfStar : smoothPoints n xStar x 0 = xStar := rfl
  have hhStar : nonsmoothPoints n xStar x 0 = xStar := rfl
  simp only [objectiveQ, LinearExprQ.evalR_sub, LinearExprQ.evalR_add,
    LinearExprQ.evalR_valueVar]
  change (valueSlots n f h xStar x (smoothValueIndex (Fin.last (n + 2))) +
      valueSlots n f h xStar x (nonsmoothValueIndex (Fin.last (n + 1)))) -
    (valueSlots n f h xStar x (smoothValueIndex 0) +
      valueSlots n f h xStar x (nonsmoothValueIndex 0)) = _
  simp only [valueSlots_smooth, valueSlots_nonsmooth, hfLast, hhLast, hfStar, hhStar]

/-- Component-local interpolation and the radius constraint for ALL steps. -/
theorem actualData_constraints {n : ℕ} {f h : E → ℝ} {g : E → E}
    {xStar : E} {x s : ℕ → E} (hf : IsOneSmoothConvexFirstOrder f g)
    (hs : SubgradientAt h (-g xStar) xStar)
    (hrun : IsResidualRun (n + 1) h g x s) (hradius : ‖x 0 - xStar‖ ^ 2 ≤ 1) :
    AssumptionsFeasibleR (modelQ n) (actualData n f h g xStar x s) := by
  have hu : ∀ k < n + 1, x (k + 1) = x k - g (x k) - s k := by
    intro k hk
    exact (hrun k hk).update
  apply LeanPEP.Profiles.Composite.compileModelQ_feasible (profileQ n)
  · intro c hc
    have hc' : c = smoothComponentQ n ∨ c = nonsmoothComponentQ n := by
      simpa [profileQ] using hc
    rcases hc' with rfl | rfl
    · intro a ha b hb
      rcases List.mem_map.mp ha with ⟨i, hi, rfl⟩
      rcases List.mem_map.mp hb with ⟨j, hj, rfl⟩
      exact Composite.smooth_pair_nonneg
        (smoothSamples_denote f h g xStar x s hu i)
        (smoothSamples_denote f h g xStar x s hu j) hf
    · intro a ha b hb
      rcases List.mem_map.mp ha with ⟨i, hi, rfl⟩
      rcases List.mem_map.mp hb with ⟨j, hj, rfl⟩
      apply Composite.convex_pair_nonneg
        (nonsmoothSamples_denote f h g xStar x s hu i)
        (nonsmoothSamples_denote f h g xStar x s hu j)
      refine Fin.cases ?_ (fun k => ?_) j
      · exact hs
      · exact (hrun k.val k.isLt).subgradient
  · intro e he
    have he' : e = radiusExprQ n := by simpa [profileQ] using he
    subst e
    rw [radius_eval]
    linarith

/-- A checked certificate for the compiled horizon is sufficient for an
actual composite bound. No hidden single-function CoreFeasible is used. -/
theorem certificate_upper {n : ℕ} (c : GramPEP.UpperCertQ (modelQ n))
    (hcheck : GramPEP.checkUpperCertQ c = true) (hempty : c.interpTerms = [])
    (hobjective : c.objective = objectiveQ n)
    {f h : E → ℝ} {g : E → E} {xStar : E} {x s : ℕ → E}
    (hf : IsOneSmoothConvexFirstOrder f g) (hs : SubgradientAt h (-g xStar) xStar)
    (hrun : IsResidualRun (n + 1) h g x s) (hradius : ‖x 0 - xStar‖ ^ 2 ≤ 1) :
    (f (x (n + 1)) + h (x (n + 1))) - (f xStar + h xStar) ≤ (c.bound : ℝ) := by
  have hb := LeanPEP.Profiles.ProximalGradient.certificate_upper c hcheck hempty hobjective
    (actualData n f h g xStar x s)
    (FiniteGram.gramOfVectors_posSemidef (baseVectors n g xStar x s))
    (actualData_constraints hf hs hrun hradius)
  simpa only [objective_eval] using hb

/-- Ordinary actual prox minimizers automatically supply every residual. -/
theorem certificate_upper_of_prox {n : ℕ} (c : GramPEP.UpperCertQ (modelQ n))
    (hcheck : GramPEP.checkUpperCertQ c = true) (hempty : c.interpTerms = [])
    (hobjective : c.objective = objectiveQ n)
    {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsOneSmoothConvexFirstOrder f g) (hh : ConvexOn ℝ Set.univ h)
    (hs : SubgradientAt h (-g xStar) xStar) (hrun : IsProxRun (n + 1) h g x)
    (hradius : ‖x 0 - xStar‖ ^ 2 ≤ 1) :
    (f (x (n + 1)) + h (x (n + 1))) - (f xStar + h xStar) ≤ (c.bound : ℝ) :=
  certificate_upper c hcheck hempty hobjective hf hs (hrun.toResidualRun hh) hradius

theorem certificate_upper_analytic [CompleteSpace E] {n : ℕ}
    (c : GramPEP.UpperCertQ (modelQ n))
    (hcheck : GramPEP.checkUpperCertQ c = true) (hempty : c.interpTerms = [])
    (hobjective : c.objective = objectiveQ n)
    {f h : E → ℝ} {g : E → E} {xStar : E} {x : ℕ → E}
    (hf : IsOneSmoothConvexAnalytic f g) (hh : ConvexOn ℝ Set.univ h)
    (hs : SubgradientAt h (-g xStar) xStar) (hrun : IsProxRun (n + 1) h g x)
    (hradius : ‖x 0 - xStar‖ ^ 2 ≤ 1) :
    (f (x (n + 1)) + h (x (n + 1))) - (f xStar + h xStar) ≤ (c.bound : ℝ) :=
  certificate_upper_of_prox c hcheck hempty hobjective hf.toFirstOrder hh hs hrun hradius

end LeanPEP.ActualFunction.ProximalGradient
