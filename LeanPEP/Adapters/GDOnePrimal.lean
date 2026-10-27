import LeanPEP.ActualFunction.GDOneCapture
import LeanPEP.GramPEP.ExternalBundle

/-! GD1-only finite primal wrapper. Unlike PG's composite carrier, the canonical
GD datum must realize the model AND satisfy all ordered single-function
interpolation inequalities. Every checker below is the original core checker. -/
namespace LeanPEP.Adapters.GDOnePrimal
open LeanPEP.GramPEP LeanPEP.GramPEP.UpperCertificateExamples
open LeanPEP.ActualFunction.GDOneCapture

structure NativeQ where
  gram : Gram 3 ℚ
  values : Fin 4 → ℚ

def NativeQ.data (d : NativeQ) : DataQ (Fin 4) 3 :=
  { gram := d.gram, value := d.values, position := fun _ => 0, gradient := fun _ => 0 }

def canonicalData (d : NativeQ) : DataQ (Fin 3) 3 :=
  { gram := d.gram, value := fun i => d.values i.castSucc
    position := oneStepModelQ.position, gradient := oneStepModelQ.gradient }

def coefficientOK (r c : ℚ) : Bool :=
  decide (c.den ≤ 1000000 ∧ |c-r| ≤ (1/1000000 : ℚ))

def policy (r c : NativeQ) : Bool :=
  (gramIndexPairs 3).all (fun ij => coefficientOK (r.gram ij.1 ij.2) (c.gram ij.1 ij.2)) &&
    (List.finRange 4).all (fun i => coefficientOK (r.values i) (c.values i))

def fullNativeModelQ : ModelQ 4 3 :=
  { position := fun _ => 0, gradient := fun _ => 0
    assumptions := [LinearExprQ.neg (LinearExprQ.sub tauQ (liftExpr oneStepObjectiveQ)),
      liftExpr oneNormalizationQ] ++
      (pointIndexPairs 3).map (fun ij => liftExpr (interpolationExprQ oneStepModelQ ij.1 ij.2)) }

def beta (d : NativeQ) : ℚ := d.values 2 - d.values 0

/-- No post-solve origin deletion, gauge change, or dual matrix restriction. -/
theorem primal_transport (d : NativeQ) :
    (castDataQ (canonicalData d)).gram = (castDataQ d.data).gram ∧
    ∀ i : Fin 3, (castDataQ (canonicalData d)).value i = (d.values i.castSucc : ℝ) :=
  ⟨rfl, fun _ => rfl⟩

def checkFinite (d : NativeQ) (f : PSDFactorCertQ 3) : Bool :=
  checkPSDFactorQ d.gram f &&
  checkAssumptionsFeasibleQ nativeModelQ d.data &&
  checkAssumptionsFeasibleQ fullNativeModelQ d.data &&
  checkDataRealizesModelQ oneStepModelQ (canonicalData d) &&
  checkInterpolationFeasibleQ (canonicalData d) &&
  checkAssumptionsFeasibleQ oneStepModelQ (canonicalData d) &&
  decide (d.values 3 ≤ beta d ∧ oneStepObjectiveQ.evalQ (canonicalData d) = beta d ∧ 0 < beta d)

theorem checkFinite_sound (d : NativeQ) (f : PSDFactorCertQ 3)
    (h : checkFinite d f = true) :
    IsGramPosSemidef (castDataQ d.data).gram ∧
    AssumptionsFeasibleR nativeModelQ (castDataQ d.data) ∧
    AssumptionsFeasibleR fullNativeModelQ (castDataQ d.data) ∧
    RealizesModelQ oneStepModelQ (castDataQ (canonicalData d)) ∧
    CoreFeasible (castDataQ (canonicalData d)) ∧
    AssumptionsFeasibleR oneStepModelQ (castDataQ (canonicalData d)) ∧
    oneStepObjectiveQ.evalR (castDataQ (canonicalData d)) = (beta d : ℝ) ∧ 0 < (beta d : ℝ) := by
  simp only [checkFinite, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  rcases h with ⟨hp, hn, hall, hm, hi, hr, ht, ho, hb⟩
  refine ⟨checkPSDFactorQ_sound_real _ _ hp,
    assumptionsFeasibleQ_toReal _ _ ((checkAssumptionsFeasibleQ_eq_true_iff _ _).mp hn),
    assumptionsFeasibleQ_toReal _ _ ((checkAssumptionsFeasibleQ_eq_true_iff _ _).mp hall),
    realizesModelExactQ_toReal ((checkDataRealizesModelQ_eq_true_iff _ _).mp hm),
    ⟨checkPSDFactorQ_sound_real _ _ hp,
      interpolationFeasibleQ_toReal _ ((checkInterpolationFeasibleQ_eq_true_iff _).mp hi)⟩,
    assumptionsFeasibleQ_toReal _ _ ((checkAssumptionsFeasibleQ_eq_true_iff _ _).mp hr), ?_,
    Rat.cast_pos.mpr hb⟩
  rw [LinearExprQ.evalR_castDataQ, ho]
end LeanPEP.Adapters.GDOnePrimal
