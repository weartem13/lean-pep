import LeanPEP.ActualFunction.Proximal
import LeanPEP.ActualFunction.FiniteGram
import LeanPEP.Profiles.Composite

/-!
# Actual semantics for component-local constraint compilation

Different components may have different scalar functions and different sample
sets. The ambient Gram matrix and explicit value slots are shared. There is no
smoothness assertion across components and no interpolation-completeness step.
-/

noncomputable section
namespace LeanPEP.ActualFunction.Composite

open LeanPEP.GramPEP
open LeanPEP.Profiles.Composite

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Pure Gram/value datum. The zero position/gradient slots are not samples. -/
def dataOfValues {p m : ℕ} (base : Fin m → E) (values : Fin p → ℝ) :
    DataR (Fin p) m :=
  { gram := FiniteGram.gramOfVectors base
    position := fun _ => 0
    gradient := fun _ => 0
    value := values }

/-- A sample's rational vectors denote a centered point and an oracle answer. -/
def SampleDenotes {p m : ℕ} (base : Fin m → E) (values : Fin p → ℝ)
    (anchor : E) (a : SampleQ p m) (x s : E) (value : ℝ) : Prop :=
  values a.valueIndex = value ∧
    FiniteGram.realize base (castVecQ a.position) = x - anchor ∧
    FiniteGram.realize base (castVecQ a.oracle) = s

/-- Exact ambient meaning of a convex pair of samples. -/
theorem eval_convex {p m : ℕ} {base : Fin m → E} {values : Fin p → ℝ}
    {anchor x y s t : E} {fx fy : ℝ} {a b : SampleQ p m}
    (ha : SampleDenotes base values anchor a x s fx)
    (hb : SampleDenotes base values anchor b y t fy) :
    (LeanPEP.Profiles.Composite.interpolationExprQ .convex a b).evalR
        (dataOfValues base values) = fx - fy - inner ℝ t (x - y) := by
  rw [evalR_interpolationExprQ_convex a b _ (FiniteGram.gramOfVectors_symmetric base)]
  change values a.valueIndex - values b.valueIndex -
    gramInner (FiniteGram.gramOfVectors base) (castVecQ b.oracle)
      (castVecQ (a.position - b.position)) = _
  rw [FiniteGram.gramInner_gramOfVectors, castVecQ_sub, FiniteGram.realize_sub,
    hb.2.2, ha.2.1, hb.2.1, ha.1, hb.1]
  have hdiff : (x - anchor) - (y - anchor) = x - y := by abel
  rw [hdiff]

/-- Exact ambient meaning of a unit-smooth pair of samples. -/
theorem eval_smooth {p m : ℕ} {base : Fin m → E} {values : Fin p → ℝ}
    {anchor x y s t : E} {fx fy : ℝ} {a b : SampleQ p m}
    (ha : SampleDenotes base values anchor a x s fx)
    (hb : SampleDenotes base values anchor b y t fy) :
    (LeanPEP.Profiles.Composite.interpolationExprQ .oneSmoothConvex a b).evalR
        (dataOfValues base values) = fx - fy - inner ℝ t (x - y) -
          (1/2 : ℝ) * inner ℝ (s - t) (s - t) := by
  rw [evalR_interpolationExprQ_smooth a b _ (FiniteGram.gramOfVectors_symmetric base)]
  change values a.valueIndex - values b.valueIndex -
    gramInner (FiniteGram.gramOfVectors base) (castVecQ b.oracle)
      (castVecQ (a.position - b.position)) -
    (1/2 : ℝ) * gramNormSq (FiniteGram.gramOfVectors base)
      (castVecQ (a.oracle - b.oracle)) = _
  rw [FiniteGram.gramInner_gramOfVectors, FiniteGram.gramNormSq_gramOfVectors,
    castVecQ_sub, castVecQ_sub, FiniteGram.realize_sub, FiniteGram.realize_sub,
    ha.2.1, hb.2.1, ha.2.2, hb.2.2, ha.1, hb.1]
  have hdiff : (x - anchor) - (y - anchor) = x - y := by abel
  rw [hdiff]

/-- A global subgradient contract entails the component-local convex slack. -/
theorem convex_pair_nonneg {p m : ℕ} {base : Fin m → E} {values : Fin p → ℝ}
    {anchor x y s t : E} {h : E → ℝ} {a b : SampleQ p m}
    (ha : SampleDenotes base values anchor a x s (h x))
    (hb : SampleDenotes base values anchor b y t (h y))
    (ht : Proximal.SubgradientAt h t y) :
    0 ≤ (LeanPEP.Profiles.Composite.interpolationExprQ .convex a b).evalR
      (dataOfValues base values) := by
  rw [eval_convex ha hb]
  have hsupport := ht x
  linarith

/-- The established actual smooth interpolation theorem justifies precisely
one component, without constraining values belonging to other components. -/
theorem smooth_pair_nonneg {p m : ℕ} {base : Fin m → E} {values : Fin p → ℝ}
    {anchor x y : E} {f : E → ℝ} {g : E → E} {a b : SampleQ p m}
    (ha : SampleDenotes base values anchor a x (g x) (f x))
    (hb : SampleDenotes base values anchor b y (g y) (f y))
    (hf : IsOneSmoothConvexFirstOrder f g) :
    0 ≤ (LeanPEP.Profiles.Composite.interpolationExprQ .oneSmoothConvex a b).evalR
      (dataOfValues base values) := by
  rw [eval_smooth ha hb]
  exact interpolationSlack_nonneg hf x y

end LeanPEP.ActualFunction.Composite
