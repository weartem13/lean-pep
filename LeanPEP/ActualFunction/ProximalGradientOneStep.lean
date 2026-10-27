import LeanPEP.ActualFunction.Composite
import LeanPEP.Profiles.ProximalGradientOneStep

/-!
# Actual one-step proximal-gradient upper bound from the composite certificate

An actual unit prox minimizer is converted to a residual subgradient and an
implicit update, then to the component compiler's fourteen constraints.
No `CoreFeasible` premise, fictitious smoothness of the nonsmooth component,
or separate stationarity of the two components is assumed.
-/

noncomputable section
namespace LeanPEP.ActualFunction.ProximalGradientOneStep

open LeanPEP.GramPEP
open LeanPEP.Profiles.ProximalGradientOneStep
open Proximal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def baseVectors (g : E → E) (xStar x0 x1 s1 : E) : Fin 5 → E :=
  ![x0 - xStar, g xStar, g x0, g x1, s1]

def valueSlots (f h : E → ℝ) (xStar x0 x1 : E) : Fin 5 → ℝ :=
  ![f xStar, f x0, f x1, h xStar, h x1]

def actualData (f h : E → ℝ) (g : E → E) (xStar x0 x1 s1 : E) :
    DataR (Fin 5) 5 :=
  Composite.dataOfValues (baseVectors g xStar x0 x1 s1) (valueSlots f h xStar x0 x1)

private theorem base_realization (g : E → E) (xStar x0 x1 s1 : E) :
    FiniteGram.realize (baseVectors g xStar x0 x1 s1) (castVecQ initialVecQ) = x0 - xStar ∧
    FiniteGram.realize (baseVectors g xStar x0 x1 s1) (castVecQ starGradientQ) = g xStar ∧
    FiniteGram.realize (baseVectors g xStar x0 x1 s1) (castVecQ initialGradientQ) = g x0 ∧
    FiniteGram.realize (baseVectors g xStar x0 x1 s1) (castVecQ finalGradientQ) = g x1 ∧
    FiniteGram.realize (baseVectors g xStar x0 x1 s1) (castVecQ finalSubgradientQ) = s1 := by
  simp [FiniteGram.realize, baseVectors, castVecQ, initialVecQ, starGradientQ,
    initialGradientQ, finalGradientQ, finalSubgradientQ, Fin.sum_univ_succ]

private theorem final_realization {g : E → E} {xStar x0 x1 s1 : E}
    (hupdate : x1 = x0 - g x0 - s1) :
    FiniteGram.realize (baseVectors g xStar x0 x1 s1) (castVecQ finalVecQ) = x1 - xStar := by
  have hb := base_realization g xStar x0 x1 s1
  simp only [finalVecQ, castVecQ_sub, FiniteGram.realize_sub]
  rw [hb.1, hb.2.2.1, hb.2.2.2.2, hupdate]
  abel

def smoothPoints (xStar x0 x1 : E) : Fin 3 → E := ![xStar, x0, x1]
def nonsmoothPoints (xStar x1 : E) : Fin 2 → E := ![xStar, x1]
def nonsmoothOracles (gStar s1 : E) : Fin 2 → E := ![-gStar, s1]

/-- The smooth component's three sample records denote actual values/gradients. -/
theorem smoothSamples_denote (f h : E → ℝ) (g : E → E) (xStar x0 x1 s1 : E)
    (hupdate : x1 = x0 - g x0 - s1) (i : Fin 3) :
    Composite.SampleDenotes (baseVectors g xStar x0 x1 s1) (valueSlots f h xStar x0 x1)
      xStar (smoothSamplesQ i) (smoothPoints xStar x0 x1 i)
        (g (smoothPoints xStar x0 x1 i)) (f (smoothPoints xStar x0 x1 i)) := by
  have hb := base_realization g xStar x0 x1 s1
  have hx := final_realization (xStar := xStar) hupdate
  fin_cases i <;>
    simp [Composite.SampleDenotes, smoothSamplesQ, smoothPoints, valueSlots,
      hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hx]

/-- The nonsmooth component has its OWN value slots and two subgradients. -/
theorem nonsmoothSamples_denote (f h : E → ℝ) (g : E → E) (xStar x0 x1 s1 : E)
    (hupdate : x1 = x0 - g x0 - s1) (i : Fin 2) :
    Composite.SampleDenotes (baseVectors g xStar x0 x1 s1) (valueSlots f h xStar x0 x1)
      xStar (nonsmoothSamplesQ i) (nonsmoothPoints xStar x1 i)
        (nonsmoothOracles (g xStar) s1 i) (h (nonsmoothPoints xStar x1 i)) := by
  have hb := base_realization g xStar x0 x1 s1
  have hx := final_realization (xStar := xStar) hupdate
  fin_cases i <;>
    simp [Composite.SampleDenotes, nonsmoothSamplesQ, nonsmoothPoints, nonsmoothOracles,
      valueSlots, castVecQ_neg, FiniteGram.realize_neg, hb.2.1, hb.2.2.2.2, hx]

/-- Exact radius-inequality semantics; the inequality is not replaced by equality. -/
theorem radius_eval (f h : E → ℝ) (g : E → E) (xStar x0 x1 s1 : E) :
    radiusExprQ.evalR (actualData f h g xStar x0 x1 s1) = 1 - ‖x0 - xStar‖ ^ 2 := by
  have hb := (base_realization g xStar x0 x1 s1).1
  simp only [radiusExprQ, LinearExprQ.evalR_sub, LinearExprQ.evalR_const, Rat.cast_one]
  rw [LinearExprQ.evalR_gramNorm _ _
    (FiniteGram.gramOfVectors_symmetric (baseVectors g xStar x0 x1 s1))]
  change 1 - gramNormSq (FiniteGram.gramOfVectors (baseVectors g xStar x0 x1 s1))
    (castVecQ initialVecQ) = _
  rw [FiniteGram.gramNormSq_gramOfVectors, hb, real_inner_self_eq_norm_sq]

@[simp] theorem objective_eval (f h : E → ℝ) (g : E → E) (xStar x0 x1 s1 : E) :
    objectiveQ.evalR (actualData f h g xStar x0 x1 s1) =
      (f x1 + h x1) - (f xStar + h xStar) := by
  simp [objectiveQ_evalR, actualData, Composite.dataOfValues, valueSlots]

/-- Every one of the 9 smooth pairs, 4 nonsmooth pairs, and the radius
constraint follows from the actual semantic assumptions. -/
theorem actualData_constraints {f h : E → ℝ} {g : E → E} {xStar x0 x1 s1 : E}
    (hf : IsOneSmoothConvexFirstOrder f g)
    (hs : SubgradientAt h (-g xStar) xStar)
    (hstep : IsUnitForwardBackwardStep h (g x0) x0 x1 s1)
    (hradius : ‖x0 - xStar‖ ^ 2 ≤ 1) :
    AssumptionsFeasibleR modelQ (actualData f h g xStar x0 x1 s1) := by
  apply LeanPEP.Profiles.Composite.compileModelQ_feasible profileQ
  · intro c hc
    have hc' : c = smoothComponentQ ∨ c = nonsmoothComponentQ := by
      simpa [profileQ] using hc
    rcases hc' with rfl | rfl
    · intro a ha b hb
      rcases List.mem_map.mp ha with ⟨i, hi, rfl⟩
      rcases List.mem_map.mp hb with ⟨j, hj, rfl⟩
      exact Composite.smooth_pair_nonneg
        (smoothSamples_denote f h g xStar x0 x1 s1 hstep.update i)
        (smoothSamples_denote f h g xStar x0 x1 s1 hstep.update j) hf
    · intro a ha b hb
      rcases List.mem_map.mp ha with ⟨i, hi, rfl⟩
      rcases List.mem_map.mp hb with ⟨j, hj, rfl⟩
      apply Composite.convex_pair_nonneg
        (nonsmoothSamples_denote f h g xStar x0 x1 s1 hstep.update i)
        (nonsmoothSamples_denote f h g xStar x0 x1 s1 hstep.update j)
      fin_cases j
      · exact hs
      · exact hstep.subgradient
  · intro e he
    have he' : e = radiusExprQ := by simpa [profileQ] using he
    subst e
    rw [radius_eval]
    linarith

/-- Actual sharp one-step bound, proved THROUGH the unchanged Gram checker. -/
theorem upper_firstOrder {f h : E → ℝ} {g : E → E} {xStar x0 x1 s1 : E}
    (hf : IsOneSmoothConvexFirstOrder f g)
    (hs : SubgradientAt h (-g xStar) xStar)
    (hstep : IsUnitForwardBackwardStep h (g x0) x0 x1 s1)
    (hradius : ‖x0 - xStar‖ ^ 2 ≤ 1) :
    (f x1 + h x1) - (f xStar + h xStar) ≤ (1 : ℝ) / 4 := by
  have hbound := LeanPEP.Profiles.ProximalGradientOneStep.upper
    (actualData f h g xStar x0 x1 s1)
    (FiniteGram.gramOfVectors_posSemidef (baseVectors g xStar x0 x1 s1))
    (actualData_constraints hf hs hstep hradius)
  simpa only [objective_eval] using hbound

/-- Standard convex proximal minimization is sufficient; the caller does NOT
supply a residual oracle or finite PEP feasibility. -/
theorem upper_of_prox {f h : E → ℝ} {g : E → E} {xStar x0 x1 : E}
    (hf : IsOneSmoothConvexFirstOrder f g) (hh : ConvexOn ℝ Set.univ h)
    (hs : SubgradientAt h (-g xStar) xStar)
    (hp : IsUnitProxPoint h (x0 - g x0) x1)
    (hradius : ‖x0 - xStar‖ ^ 2 ≤ 1) :
    (f x1 + h x1) - (f xStar + h xStar) ≤ (1 : ℝ) / 4 :=
  upper_firstOrder hf hs (forwardBackwardStep_of_prox hh hp) hradius

theorem upper_analytic [CompleteSpace E]
    {f h : E → ℝ} {g : E → E} {xStar x0 x1 : E}
    (hf : IsOneSmoothConvexAnalytic f g) (hh : ConvexOn ℝ Set.univ h)
    (hs : SubgradientAt h (-g xStar) xStar)
    (hp : IsUnitProxPoint h (x0 - g x0) x1)
    (hradius : ‖x0 - xStar‖ ^ 2 ≤ 1) :
    (f x1 + h x1) - (f xStar + h xStar) ≤ (1 : ℝ) / 4 :=
  upper_of_prox hf.toFirstOrder hh hs hp hradius

end LeanPEP.ActualFunction.ProximalGradientOneStep
