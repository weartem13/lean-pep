import LeanPEP.ActualFunction.GDOneCapture
import LeanPEP.ActualFunction.ProfileGram
import LeanPEP.Profiles.GradientDescentGram
import LeanPEP.GramPEP.RationalReconstructionAudit
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Instance-specific GD(2) certificate bridge. No historical rate theorem used.
Coordinates are (x0-xStar,g0,g1,g2); reference position/gradient vanish exactly.
Tau is kept in the captured native certificate and explicitly substituted by f2-fStar.
-/
namespace LeanPEP.ActualFunction.GDTwoCapture
open LeanPEP.GramPEP LeanPEP.GramPEP.UpperCertificateExamples
open LeanPEP.GramPEP.RationalReconstructionAudit
open scoped NNReal

def modelQ := Profiles.GradientDescentGram.unitGDModelQ 2
def objectiveQ := Profiles.GradientDescentGram.unitGDObjectiveQ 2
def normalizationQ := Profiles.GramCompilation.initialRadiusExprQ (N := 2) Profiles.GramCompilation.unitRadiusNormalizationQ

def liftExpr (e : LinearExprQ 4 4) : LinearExprQ 5 4 :=
  { constCoeff := e.constCoeff, valueCoeff := ![e.valueCoeff 0,e.valueCoeff 1,e.valueCoeff 2,e.valueCoeff 3,0],
    gramCoeff := e.gramCoeff }
def tauQ : LinearExprQ 5 4 := LinearExprQ.valueVar 4
def pairs : List (Fin 4 × Fin 4) := [(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2)]
def expectedRows : List (LinearExprQ 5 4) :=
  [LinearExprQ.sub tauQ (liftExpr objectiveQ), LinearExprQ.neg (liftExpr normalizationQ)] ++
  pairs.map (fun ij => LinearExprQ.neg (liftExpr (interpolationExprQ modelQ ij.1 ij.2)))
def nativeModelQ : ModelQ 5 4 :=
  { position := fun _ => 0, gradient := fun _ => 0,
    assumptions := expectedRows.map LinearExprQ.neg }
structure SourceQ where
  position : Fin 4 → Fin 4 → ℚ
  gradient : Fin 4 → Fin 4 → ℚ
  rows : List (LinearExprQ 5 4)
  labels : List (Nat × Nat × Nat)
  metric : LinearExprQ 5 4
  objective : LinearExprQ 5 4
  steps : Nat
  stepSize : ℚ

def checkSourceQ (s : SourceQ) : Bool :=
  decide (s.steps = 2 ∧ s.stepSize = 1 ∧ s.position = modelQ.position ∧
    s.gradient = modelQ.gradient ∧
    s.labels = [(0,0,0),(1,0,0),(2,0,1),(2,0,2),(2,0,3),(2,1,0),(2,1,2),(2,1,3),(2,2,0),(2,2,1),(2,2,3),(2,3,0),(2,3,1),(2,3,2)]) &&
  decide (s.rows.length = expectedRows.length) &&
  ((s.rows.zip expectedRows).all fun es => checkLinearExprEqQ es.1 es.2) &&
  checkLinearExprEqQ s.metric (liftExpr objectiveQ) && checkLinearExprEqQ s.objective tauQ

structure TraceQ where
  bound : ℚ
  multipliers : List ℚ
  residual : Gram 4 ℚ

def checkRawQ (s : SourceQ) (t : TraceQ) (r : UpperCertQ nativeModelQ) : Bool :=
  checkSourceQ s && checkLinearExprEqQ r.objective s.objective &&
  decide (r.bound = t.bound ∧ r.interpTerms = [] ∧
    r.assumptionTerms.map (fun a => a.index.val) = List.range 14 ∧
    r.assumptionTerms.map (fun a => a.weight) = t.multipliers ∧ r.dualMatrix = t.residual)

def centered (c : UpperCertQ nativeModelQ) : UpperCertQ modelQ :=
  { bound := c.bound, objective := objectiveQ,
    interpTerms := (pairs.zipIdx.map (fun (ij,k) =>
      { weight := (c.assumptionTerms[k+2]?.map (fun a => a.weight)).getD 0, i := ij.1, j := ij.2 })),
    assumptionTerms := [{ weight := (c.assumptionTerms[1]?.map (fun a => a.weight)).getD 0, index := ⟨0, by decide +kernel⟩ }],
    dualMatrix := c.dualMatrix, dualFactor := c.dualFactor }

/-- Exact tau := f2-fStar substitution, keeping every other coefficient. -/
def eraseTau (e : LinearExprQ 5 4) : LinearExprQ 4 4 :=
  { constCoeff := e.constCoeff,
    valueCoeff := ![e.valueCoeff 0-e.valueCoeff 4,e.valueCoeff 1,e.valueCoeff 2,e.valueCoeff 3+e.valueCoeff 4],
    gramCoeff := e.gramCoeff }

theorem tau_substitution :
    checkLinearExprEqQ (eraseTau tauQ) objectiveQ = true ∧
    (expectedRows.map eraseTau |>.map exprCoefficientsQ) =
      ([LinearExprQ.zero 4 4, LinearExprQ.neg normalizationQ] ++
        pairs.map (fun ij => LinearExprQ.neg (interpolationExprQ modelQ ij.1 ij.2)) |>.map exprCoefficientsQ) := by
  decide +kernel

def checkAcceptedQ (s : SourceQ) (t : TraceQ) (policy : PolicyQ)
    (raw c : UpperCertQ nativeModelQ) : Bool :=
  checkRawQ s t raw && checkChangesQ policy raw c && checkUpperCertQ c &&
    checkUpperCertQ (centered c)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Both cumulative GD equations realized by the actual two supplied updates. -/
theorem realizes_two {g : E → E} {xStar x0 x1 x2 : E}
    (h1 : x1 = x0-g x0) (h2 : x2 = x1-g x1) :
    ProfileGram.RealizesProfile (Profiles.GradientDescent.unitGDProfileQ 2)
      g xStar x0 ![x0,x1,x2] := by
  apply (ProfileGram.realizesProfile_iff_updates _ _ _ _ _).2
  intro i
  fin_cases i <;>
    simp [Profiles.GradientDescent.unitGDProfileQ, Profiles.GradientDescent.unitStepCoeffQ,
      Fin.sum_univ_three, h1, h2] <;> abel

theorem unit_upper (c : UpperCertQ modelQ) (hc : checkUpperCertQ c = true)
    (ho : c.objective = objectiveQ)
    {f : E → ℝ} {g : E → E} (h : IsOneSmoothConvexFirstOrder f g)
    {xStar x0 x1 x2 : E} (hs : g xStar = 0)
    (h1 : x1 = x0-g x0) (h2 : x2 = x1-g x1)
    (hr : ‖x0-xStar‖^2 ≤ 1) : f x2-f xStar ≤ (c.bound : ℝ) := by
  have hout := ProfileGram.certificate_upper
    (Profiles.GradientDescentGram.unitGDGramProfileQ 2) c hc ho h hs
    (realizes_two (xStar := xStar) h1 h2) (by
      simpa [Profiles.GradientDescentGram.unitGDGramProfileQ, Profiles.GramCompilation.unitRadiusNormalizationQ] using hr)
  simpa [ProfileGram.samplePoint, Profiles.GradientDescentGram.unitGDGramProfileQ,
    Profiles.GramCompilation.finalGapObjectiveProfileQ] using hout

variable [CompleteSpace E] {L : ℝ≥0} {f : E → ℝ} {g : E → E}

theorem upper_pos (c : UpperCertQ modelQ) (hc : checkUpperCertQ c = true)
    (ho : c.objective = objectiveQ) (hf : IsSmoothConvexAnalytic L f g)
    (hL : 0 < (L : ℝ)) {xStar x0 x1 x2 : E} {R : ℝ} (hR : 0 < R)
    (hs : g xStar = 0) (h1 : x1=x0-(L : ℝ)⁻¹ • g x0)
    (h2 : x2=x1-(L : ℝ)⁻¹ • g x1) (hr : ‖x0-xStar‖^2 ≤ R^2) :
    f x2-f xStar ≤ (L : ℝ)*R^2*(c.bound : ℝ) := by
  let F := SmoothScaling.normalizedFunction f xStar L R
  let G := SmoothScaling.normalizedGradient g xStar L R
  let z0 := R⁻¹ • (x0-xStar)
  let z1 := z0-G z0
  let z2 := z1-G z1
  have hL0 : (L : ℝ) ≠ 0 := ne_of_gt hL
  have hR0 : R ≠ 0 := ne_of_gt hR
  have hA : 0 < (L : ℝ)*R^2 := by positivity
  have hnormalized : IsOneSmoothConvexFirstOrder F G :=
    SmoothScaling.normalizedFirstOrder (xStar := xStar) hf.toFirstOrder hL hR
  have hGzero : G 0 = 0 := by
    simp [G, SmoothScaling.normalizedGradient, SmoothScaling.scaledPoint, hs]
  have hzradius : ‖z0‖^2 ≤ 1 := by
    have hnorm : ‖z0‖^2 = ‖x0-xStar‖^2/R^2 := by
      dsimp [z0]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
      field_simp [hR0] <;> ring
    rw [hnorm]
    apply (div_le_iff₀ (by positivity : 0 < R^2)).2
    simpa using hr
  have hscaledZ0 : SmoothScaling.scaledPoint xStar R z0 = x0 := by
    have hz : R • z0 = x0-xStar := by simp [z0,smul_smul,hR0]
    rw [SmoothScaling.scaledPoint,hz]
    abel
  have hcoeff : R*(1/((L : ℝ)*R)) = (L : ℝ)⁻¹ := by
    field_simp [hL0,hR0] <;> ring
  have hscaledStep (z : E) : SmoothScaling.scaledPoint xStar R (z-G z) =
      SmoothScaling.scaledPoint xStar R z - (L : ℝ)⁻¹ • g (SmoothScaling.scaledPoint xStar R z) := by
    dsimp [G,SmoothScaling.normalizedGradient,SmoothScaling.scaledPoint]
    rw [smul_sub,smul_smul,hcoeff]
    abel
  have hscaledZ1 : SmoothScaling.scaledPoint xStar R z1 = x1 := by
    dsimp [z1]
    rw [hscaledStep,hscaledZ0,h1]
  have hscaledZ2 : SmoothScaling.scaledPoint xStar R z2 = x2 := by
    dsimp only [z2]
    rw [hscaledStep,hscaledZ1,h2]
  have hunit : F z2-F 0 ≤ (c.bound : ℝ) :=
    unit_upper c hc ho hnormalized hGzero rfl rfl (by simpa using hzradius)
  have hgap : F z2-F 0 = (f x2-f xStar)/((L : ℝ)*R^2) := by
    dsimp [F,SmoothScaling.normalizedFunction]
    rw [hscaledZ2]
    simp [SmoothScaling.scaledPoint]
  rw [hgap] at hunit
  have hout := (div_le_iff₀ hA).1 hunit
  nlinarith

theorem upper_analytic (s : SourceQ) (t : TraceQ) (policy : PolicyQ)
    (raw c : UpperCertQ nativeModelQ) (hc : checkAcceptedQ s t policy raw c = true)
    (hf : IsSmoothConvexAnalytic L f g) (hL : 0 < (L : ℝ))
    {xStar x0 x1 x2 : E} {R : ℝ} (hR : 0 ≤ R) (hm : ∀ y, f xStar ≤ f y)
    (h1 : x1=x0-(L : ℝ)⁻¹ • g x0) (h2 : x2=x1-(L : ℝ)⁻¹ • g x1)
    (hr : ‖x0-xStar‖^2 ≤ R^2) :
    f x2-f xStar ≤ (L : ℝ)*R^2*(c.bound : ℝ) := by
  have hs := GDOneCapture.stationary_of_min hf hm
  have hcheck : checkUpperCertQ (centered c) = true := (Bool.and_eq_true_iff.mp hc).2
  rcases eq_or_lt_of_le hR with rfl | hRpos
  · have hnorm : ‖x0-xStar‖ = 0 := by
      have hsq : ‖x0-xStar‖^2 ≤ 0 := by simpa using hr
      nlinarith [norm_nonneg (x0-xStar)]
    have hx0 : x0=xStar := sub_eq_zero.mp (norm_eq_zero.mp hnorm)
    have hx1 : x1=xStar := by simpa [hx0,hs] using h1
    have hx2 : x2=xStar := by simpa [hx1,hs] using h2
    simp [hx2]
  · exact upper_pos (centered c) hcheck rfl hf hL hRpos hs h1 h2 hr
end LeanPEP.ActualFunction.GDTwoCapture
