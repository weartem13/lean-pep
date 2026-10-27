import LeanPEP.ActualFunction.OneStepScaling
import LeanPEP.GramPEP.RationalReconstructionAudit
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Instance-specific GD(1) certificate bridge. No historical rate theorem used.
Coordinates are (x0-xStar,g0,g1); reference position/gradient vanish exactly.
Tau is kept in the captured native certificate and explicitly substituted by f1-fStar.
-/
namespace LeanPEP.ActualFunction.GDOneCapture
open LeanPEP.GramPEP LeanPEP.GramPEP.UpperCertificateExamples
open LeanPEP.GramPEP.RationalReconstructionAudit
open scoped NNReal

def liftExpr (e : LinearExprQ 3 3) : LinearExprQ 4 3 :=
  { constCoeff := e.constCoeff, valueCoeff := ![e.valueCoeff 0,e.valueCoeff 1,e.valueCoeff 2,0],
    gramCoeff := e.gramCoeff }
def tauQ : LinearExprQ 4 3 := LinearExprQ.valueVar 3
def pairs : List (Fin 3 × Fin 3) := [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)]
def expectedRows : List (LinearExprQ 4 3) :=
  [LinearExprQ.sub tauQ (liftExpr oneStepObjectiveQ), LinearExprQ.neg (liftExpr oneNormalizationQ)] ++
  pairs.map (fun ij => LinearExprQ.neg (liftExpr (interpolationExprQ oneStepModelQ ij.1 ij.2)))
def nativeModelQ : ModelQ 4 3 :=
  { position := fun _ => 0, gradient := fun _ => 0,
    assumptions := expectedRows.map LinearExprQ.neg }
structure SourceQ where
  position : Fin 3 → Fin 3 → ℚ
  gradient : Fin 3 → Fin 3 → ℚ
  rows : List (LinearExprQ 4 3)
  labels : List (Nat × Nat × Nat)
  metric : LinearExprQ 4 3
  objective : LinearExprQ 4 3
  steps : Nat
  stepSize : ℚ

def checkSourceQ (s : SourceQ) : Bool :=
  decide (s.steps = 1 ∧ s.stepSize = 1 ∧ s.position = oneStepModelQ.position ∧
    s.gradient = oneStepModelQ.gradient ∧
    s.labels = [(0,0,0),(1,0,0),(2,0,1),(2,0,2),(2,1,0),(2,1,2),(2,2,0),(2,2,1)]) &&
  decide (s.rows.length = expectedRows.length) &&
  ((s.rows.zip expectedRows).all fun es => checkLinearExprEqQ es.1 es.2) &&
  checkLinearExprEqQ s.metric (liftExpr oneStepObjectiveQ) && checkLinearExprEqQ s.objective tauQ

structure TraceQ where
  bound : ℚ
  multipliers : List ℚ
  residual : Gram 3 ℚ

def checkRawQ (s : SourceQ) (t : TraceQ) (r : UpperCertQ nativeModelQ) : Bool :=
  checkSourceQ s && checkLinearExprEqQ r.objective s.objective &&
  decide (r.bound = t.bound ∧ r.interpTerms = [] ∧
    r.assumptionTerms.map (fun a => a.index.val) = List.range 8 ∧
    r.assumptionTerms.map (fun a => a.weight) = t.multipliers ∧ r.dualMatrix = t.residual)

def centered (c : UpperCertQ nativeModelQ) : UpperCertQ oneStepModelQ :=
  { bound := c.bound, objective := oneStepObjectiveQ,
    interpTerms := (pairs.zipIdx.map (fun (ij,k) =>
      { weight := (c.assumptionTerms[k+2]?.map (fun a => a.weight)).getD 0, i := ij.1, j := ij.2 })),
    assumptionTerms := [{ weight := (c.assumptionTerms[1]?.map (fun a => a.weight)).getD 0, index := ⟨0, by decide +kernel⟩ }],
    dualMatrix := c.dualMatrix, dualFactor := c.dualFactor }

/-- Exact tau := f1-fStar substitution, keeping every other coefficient. -/
def eraseTau (e : LinearExprQ 4 3) : LinearExprQ 3 3 :=
  { constCoeff := e.constCoeff,
    valueCoeff := ![e.valueCoeff 0-e.valueCoeff 3,e.valueCoeff 1,e.valueCoeff 2+e.valueCoeff 3],
    gramCoeff := e.gramCoeff }

theorem tau_substitution :
    checkLinearExprEqQ (eraseTau tauQ) oneStepObjectiveQ = true ∧
    (expectedRows.map eraseTau |>.map exprCoefficientsQ) =
      ([LinearExprQ.zero 3 3, LinearExprQ.neg oneNormalizationQ] ++
        pairs.map (fun ij => LinearExprQ.neg (interpolationExprQ oneStepModelQ ij.1 ij.2)) |>.map exprCoefficientsQ) := by
  decide +kernel

def checkAcceptedQ (s : SourceQ) (t : TraceQ) (policy : PolicyQ)
    (raw c : UpperCertQ nativeModelQ) : Bool :=
  checkRawQ s t raw && checkChangesQ policy raw c && checkUpperCertQ c &&
    checkUpperCertQ (centered c)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem unit_upper (c : UpperCertQ oneStepModelQ) (hc : checkUpperCertQ c = true)
    (ho : c.objective = oneStepObjectiveQ)
    {f : E → ℝ} {g : E → E} (h : IsOneSmoothConvexFirstOrder f g)
    {xStar x0 x1 : E} (hs : g xStar = 0) (hx : x1 = x0-g x0)
    (hr : ‖x0-xStar‖^2 ≤ 1) : f x1-f xStar ≤ (c.bound : ℝ) := by
  have hreal := OneStepGram.oneStepRealizesActualSamples g xStar x0 x1 hs hx
  have hcore : CoreFeasible (OneStepGram.oneStepData f g xStar x0 x1) := by
    constructor
    · exact FiniteGram.gramOfVectors_posSemidef (OneStepGram.oneStepBase g xStar x0 x1)
    · intro i j
      unfold OneStepGram.oneStepData
      rw [FiniteGram.interpolationSlack_dataOfModel hreal i j]
      exact ActualFunction.interpolationSlack_nonneg h _ _
  have hout := checkUpperCertQ_sound_real c hc (OneStepGram.oneStepData f g xStar x0 x1)
    (OneStepGram.oneStepData_realizesModel f g xStar x0 x1) hcore
    (OneStepGram.oneStepData_assumptionsFeasible f g xStar x0 x1 (by simpa [real_inner_self_eq_norm_sq] using hr))
  rw [ho] at hout
  simpa [oneStepObjectiveQ,OneStepGram.oneStepData,OneStepGram.oneStepSamples,FiniteGram.dataOfModel] using hout

variable [CompleteSpace E] {L : ℝ≥0} {f : E → ℝ} {g : E → E}
theorem upper_pos
    (c : UpperCertQ oneStepModelQ) (hc : checkUpperCertQ c = true)
    (ho : c.objective = oneStepObjectiveQ)
    (h : IsSmoothConvexAnalytic L f g)
    (hL : 0 < (L : ℝ))
    {xStar x0 : E} {R : ℝ}
    (hR : 0 < R)
    (hstationary : g xStar = 0)
    (hradius : ‖x0 - xStar‖ ^ 2 ≤ R ^ 2) :
    f (x0 - (L : ℝ)⁻¹ • g x0) - f xStar ≤
      (L : ℝ) * R ^ 2 * (c.bound : ℝ) := by
  let F : E → ℝ := SmoothScaling.normalizedFunction f xStar L R
  let G : E → E := SmoothScaling.normalizedGradient g xStar L R
  let z0 : E := R⁻¹ • (x0 - xStar)
  have hL0 : (L : ℝ) ≠ 0 := ne_of_gt hL
  have hR0 : R ≠ 0 := ne_of_gt hR
  have hA : 0 < (L : ℝ) * R ^ 2 := by positivity
  have hnormalized : IsOneSmoothConvexFirstOrder F G := by
    simpa [F, G] using
      SmoothScaling.normalizedFirstOrder
        (xStar := xStar) h.toFirstOrder hL hR
  have hGzero : G 0 = 0 := by
    simp [G, SmoothScaling.normalizedGradient,
      SmoothScaling.scaledPoint, hstationary]
  have hzradius : ‖z0‖ ^ 2 ≤ 1 := by
    have hR2 : 0 < R ^ 2 := by positivity
    have hnorm :
        ‖z0‖ ^ 2 = ‖x0 - xStar‖ ^ 2 / R ^ 2 := by
      dsimp [z0]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
      field_simp [hR0] <;> ring
    rw [hnorm]
    apply (div_le_iff₀ hR2).2
    simpa using hradius
  have hRz0 : R • z0 = x0 - xStar := by
    simp [z0, smul_smul, hR0]
  have hscaledZ0 : SmoothScaling.scaledPoint xStar R z0 = x0 := by
    rw [SmoothScaling.scaledPoint, hRz0]
    abel
  have hGz0 :
      G z0 = (1 / ((L : ℝ) * R)) • g x0 := by
    dsimp [G, SmoothScaling.normalizedGradient]
    rw [hscaledZ0]
  have hcoeff :
      R * (1 / ((L : ℝ) * R)) = (L : ℝ)⁻¹ := by
    field_simp [hL0, hR0] <;> ring
  have hscaledUpdate :
      SmoothScaling.scaledPoint xStar R (z0 - G z0) =
        x0 - (L : ℝ)⁻¹ • g x0 := by
    rw [SmoothScaling.scaledPoint, smul_sub, hRz0, hGz0, smul_smul,
      hcoeff]
    abel
  have hunit :
      F (z0 - G z0) - F 0 ≤ (c.bound : ℝ) :=
    unit_upper c hc ho hnormalized hGzero rfl (by simpa using hzradius)
  have hgap :
      F (z0 - G z0) - F 0 =
        (f (x0 - (L : ℝ)⁻¹ • g x0) - f xStar) /
          ((L : ℝ) * R ^ 2) := by
    dsimp [F, SmoothScaling.normalizedFunction]
    rw [hscaledUpdate]
    simp [SmoothScaling.scaledPoint]
  rw [hgap] at hunit
  have hscaled := (div_le_iff₀ hA).1 hunit
  calc
    f (x0 - (L : ℝ)⁻¹ • g x0) - f xStar ≤
        ((c.bound : ℝ)) * ((L : ℝ) * R ^ 2) := hscaled
    _ = (L : ℝ) * R ^ 2 * (c.bound : ℝ) := by ring

theorem upper_stationary
    (c : UpperCertQ oneStepModelQ) (hc : checkUpperCertQ c = true)
    (ho : c.objective = oneStepObjectiveQ)
    (h : IsSmoothConvexAnalytic L f g)
    (hL : 0 < (L : ℝ))
    {xStar x0 : E} {R : ℝ}
    (hR : 0 ≤ R)
    (hstationary : g xStar = 0)
    (hradius : ‖x0 - xStar‖ ^ 2 ≤ R ^ 2) :
    f (x0 - (L : ℝ)⁻¹ • g x0) - f xStar ≤
      (L : ℝ) * R ^ 2 * (c.bound : ℝ) := by
  rcases eq_or_lt_of_le hR with rfl | hRpos
  · have hnorm : ‖x0 - xStar‖ = 0 := by
      have hsquare : ‖x0 - xStar‖ ^ 2 ≤ 0 := by
        simpa using hradius
      nlinarith [norm_nonneg (x0 - xStar)]
    have hx : x0 = xStar := by
      apply sub_eq_zero.mp
      exact norm_eq_zero.mp hnorm
    subst x0
    simp [hstationary]
  · exact upper_pos c hc ho h
      hL hRpos hstationary hradius


theorem stationary_of_min (hf : IsSmoothConvexAnalytic L f g) {xStar : E}
    (hm : ∀ y, f xStar ≤ f y) : g xStar = 0 := by
  have hlocal : IsLocalMin f xStar := Filter.Eventually.of_forall hm
  rw [← hf.gradient_eq]
  simp [gradient, hlocal.fderiv_eq_zero]

theorem upper_analytic (s : SourceQ) (t : TraceQ) (policy : PolicyQ)
    (raw c : UpperCertQ nativeModelQ) (hc : checkAcceptedQ s t policy raw c = true)
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ))
    {xStar x0 x1 : E} {R : ℝ} (hR : 0 ≤ R) (hm : ∀ y, f xStar ≤ f y)
    (hx : x1 = x0-(L : ℝ)⁻¹ • g x0) (hr : ‖x0-xStar‖^2 ≤ R^2) :
    f x1-f xStar ≤ (L : ℝ)*R^2*(c.bound : ℝ) := by
  have hcheck : checkUpperCertQ (centered c) = true := (Bool.and_eq_true_iff.mp hc).2
  rw [hx]
  exact upper_stationary (centered c) hcheck rfl hf hL hR (stationary_of_min hf hm) hr
end LeanPEP.ActualFunction.GDOneCapture
