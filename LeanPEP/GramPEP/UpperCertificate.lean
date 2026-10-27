import LeanPEP.GramPEP.RationalBridge
import LeanPEP.GramPEP.PSDFactorization

/-!
# General exact Gram-PEP upper-certificate semantics

For a fixed finite Gram formulation, every sampled position and gradient is a
rational coefficient vector over the abstract Gram basis. Function values and
Gram entries remain the optimization variables. Consequently, every
smooth-convex interpolation slack is affine-linear in those variables.

This module defines:

* exact affine-linear coefficient objects over function values and Gram entries;
* fixed rational Gram formulations and their real realizations;
* symbolic interpolation and assumption constraints;
* nonnegative interpolation and assumption multipliers; and
* a rational dual PSD matrix whose Frobenius pairing with the primal Gram
  matrix is represented by an exact factorization certificate.

The executable checker and its soundness theorem are in
`UpperCertificateChecker.lean`.
-/

namespace LeanPEP
namespace GramPEP

open scoped BigOperators

/-- Every sampled point index `0, ..., p - 1`. -/
def pointIndices (p : ℕ) : List (Fin p) :=
  List.finRange p

@[simp] theorem mem_pointIndices {p : ℕ} (i : Fin p) :
    i ∈ pointIndices p := by
  simp [pointIndices]

/-- Gram bilinear evaluation is symmetric when the Gram matrix is symmetric. -/
theorem gramInner_comm_of_symmetric
    {m : ℕ} {𝕜 : Type*} [CommSemiring 𝕜]
    (G : Gram m 𝕜) (hG : IsGramSymmetric G)
    (u v : VecExpr m 𝕜) :
    gramInner G u v = gramInner G v u := by
  calc
    gramInner G u v = ∑ i, ∑ j, u i * G i j * v j := rfl
    _ = ∑ j, ∑ i, u i * G i j * v j := by
      rw [Finset.sum_comm]
    _ = ∑ j, ∑ i, v j * G j i * u i := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi
      rw [← hG i j]
      ring
    _ = gramInner G v u := rfl

/-- An exact affine-linear expression in sampled function values and Gram
entries.

`constCoeff + Σ_i valueCoeff_i f_i + Σ_ab gramCoeff_ab G_ab`.
-/
@[ext]
structure LinearExprQ (p m : ℕ) where
  constCoeff : ℚ
  valueCoeff : Fin p → ℚ
  gramCoeff : Gram m ℚ

namespace LinearExprQ

/-- Zero affine-linear expression. -/
def zero (p m : ℕ) : LinearExprQ p m :=
  { constCoeff := 0
    valueCoeff := fun _ => 0
    gramCoeff := 0 }

/-- Constant affine-linear expression. -/
def const (p m : ℕ) (c : ℚ) : LinearExprQ p m :=
  { constCoeff := c
    valueCoeff := fun _ => 0
    gramCoeff := 0 }

/-- Addition of affine-linear expressions. -/
def add {p m : ℕ} (a b : LinearExprQ p m) : LinearExprQ p m :=
  { constCoeff := a.constCoeff + b.constCoeff
    valueCoeff := fun i => a.valueCoeff i + b.valueCoeff i
    gramCoeff := a.gramCoeff + b.gramCoeff }

/-- Negation of an affine-linear expression. -/
def neg {p m : ℕ} (a : LinearExprQ p m) : LinearExprQ p m :=
  { constCoeff := -a.constCoeff
    valueCoeff := fun i => -a.valueCoeff i
    gramCoeff := -a.gramCoeff }

/-- Subtraction of affine-linear expressions. -/
def sub {p m : ℕ} (a b : LinearExprQ p m) : LinearExprQ p m :=
  add a (neg b)

/-- Rational scaling of an affine-linear expression. -/
def scale {p m : ℕ} (c : ℚ) (a : LinearExprQ p m) : LinearExprQ p m :=
  { constCoeff := c * a.constCoeff
    valueCoeff := fun i => c * a.valueCoeff i
    gramCoeff := fun i j => c * a.gramCoeff i j }

/-- One function-value variable `f_i`. -/
def valueVar {p m : ℕ} (i : Fin p) : LinearExprQ p m :=
  { constCoeff := 0
    valueCoeff := fun j => if j = i then 1 else 0
    gramCoeff := 0 }

/-- Ordered outer-product Gram expression. -/
def gramOuter {p m : ℕ}
    (u v : VecExpr m ℚ) : LinearExprQ p m :=
  { constCoeff := 0
    valueCoeff := fun _ => 0
    gramCoeff := fun i j => u i * v j }

/-- Canonical symmetric bilinear Gram expression.  On symmetric Gram matrices
it evaluates to `uᵀ G v`. -/
def gramBilinear {p m : ℕ}
    (u v : VecExpr m ℚ) : LinearExprQ p m :=
  scale ((1 : ℚ) / 2) (add (gramOuter u v) (gramOuter v u))

/-- Squared Gram norm represented as an affine-linear expression in `G`. -/
def gramNorm {p m : ℕ} (u : VecExpr m ℚ) : LinearExprQ p m :=
  gramBilinear u u

/-- Frobenius pairing with one exact rational matrix. -/
def gramPairing {p m : ℕ} (S : Gram m ℚ) : LinearExprQ p m :=
  { constCoeff := 0
    valueCoeff := fun _ => 0
    gramCoeff := S }

/-- Real evaluation on sampled Gram data. -/
noncomputable def evalR {p m : ℕ}
    (e : LinearExprQ p m) (d : DataR (Fin p) m) : ℝ :=
  (e.constCoeff : ℝ)
    + ∑ i, (e.valueCoeff i : ℝ) * d.value i
    + ∑ i, ∑ j, (e.gramCoeff i j : ℝ) * d.gram i j

@[simp] theorem evalR_zero {p m : ℕ} (d : DataR (Fin p) m) :
    (zero p m).evalR d = 0 := by
  simp [evalR, zero]

@[simp] theorem evalR_const {p m : ℕ} (c : ℚ)
    (d : DataR (Fin p) m) :
    (const p m c).evalR d = (c : ℝ) := by
  simp [evalR, const]

@[simp] theorem evalR_add {p m : ℕ}
    (a b : LinearExprQ p m) (d : DataR (Fin p) m) :
    (add a b).evalR d = a.evalR d + b.evalR d := by
  simp [evalR, add, Finset.sum_add_distrib, add_mul]
  ring

@[simp] theorem evalR_neg {p m : ℕ}
    (a : LinearExprQ p m) (d : DataR (Fin p) m) :
    (neg a).evalR d = -a.evalR d := by
  simp [evalR, neg]
  ring

@[simp] theorem evalR_sub {p m : ℕ}
    (a b : LinearExprQ p m) (d : DataR (Fin p) m) :
    (sub a b).evalR d = a.evalR d - b.evalR d := by
  simp [sub]
  ring

@[simp] theorem evalR_scale {p m : ℕ}
    (c : ℚ) (a : LinearExprQ p m) (d : DataR (Fin p) m) :
    (scale c a).evalR d = (c : ℝ) * a.evalR d := by
  unfold evalR scale
  simp only [Rat.cast_mul]
  have hvalue :
      (∑ i, (c : ℝ) * (a.valueCoeff i : ℝ) * d.value i) =
        (c : ℝ) * (∑ i, (a.valueCoeff i : ℝ) * d.value i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hgram :
      (∑ i, ∑ j,
          (c : ℝ) * (a.gramCoeff i j : ℝ) * d.gram i j) =
        (c : ℝ) *
          (∑ i, ∑ j, (a.gramCoeff i j : ℝ) * d.gram i j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hvalue, hgram]
  ring

@[simp] theorem evalR_valueVar {p m : ℕ}
    (i : Fin p) (d : DataR (Fin p) m) :
    (valueVar (m := m) i).evalR d = d.value i := by
  classical
  unfold evalR valueVar
  rw [Fintype.sum_eq_single i]
  · simp
  · intro j hji
    simp [hji]

/-- Ordered rational Gram coefficients evaluate to the corresponding real
ordered bilinear form. -/
@[simp] theorem evalR_gramOuter {p m : ℕ}
    (u v : VecExpr m ℚ) (d : DataR (Fin p) m) :
    (gramOuter (p := p) u v).evalR d =
      gramInner d.gram (castVecQ u) (castVecQ v) := by
  simp [evalR, gramOuter, gramInner, castVecQ]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Symmetric rational Gram coefficients have exact bilinear semantics on a
symmetric real Gram matrix. -/
@[simp] theorem evalR_gramBilinear {p m : ℕ}
    (u v : VecExpr m ℚ) (d : DataR (Fin p) m)
    (hG : IsGramSymmetric d.gram) :
    (gramBilinear (p := p) u v).evalR d =
      gramInner d.gram (castVecQ u) (castVecQ v) := by
  simp [gramBilinear]
  rw [gramInner_comm_of_symmetric d.gram hG
    (castVecQ v) (castVecQ u)]
  ring

@[simp] theorem evalR_gramNorm {p m : ℕ}
    (u : VecExpr m ℚ) (d : DataR (Fin p) m)
    (hG : IsGramSymmetric d.gram) :
    (gramNorm (p := p) u).evalR d =
      gramNormSq d.gram (castVecQ u) := by
  unfold gramNorm gramNormSq
  exact evalR_gramBilinear u u d hG

/-- Evaluation of the symbolic dual term is the exact rational/real Frobenius
pairing. -/
@[simp] theorem evalR_gramPairing {p m : ℕ}
    (S : Gram m ℚ) (d : DataR (Fin p) m) :
    (gramPairing (p := p) S).evalR d =
      ∑ i, ∑ j, (S i j : ℝ) * d.gram i j := by
  simp [evalR, gramPairing]

end LinearExprQ

/-- A fixed rational Gram formulation. Positions and gradients are symbolic
coefficient vectors. Additional affine-linear assumptions include
normalization constraints such as `1 - ‖x₀ - x★‖²_G ≥ 0`.
-/
@[ext]
structure ModelQ (p m : ℕ) where
  position : Fin p → VecExpr m ℚ
  gradient : Fin p → VecExpr m ℚ
  assumptions : List (LinearExprQ p m)

/-- A real datum realizes the fixed rational position/gradient semantics. -/
structure RealizesModelQ {p m : ℕ}
    (model : ModelQ p m) (d : DataR (Fin p) m) : Prop where
  position : ∀ i, d.position i = castVecQ (model.position i)
  gradient : ∀ i, d.gradient i = castVecQ (model.gradient i)

/-- Symbolic smooth-convex interpolation slack for a fixed Gram formulation. -/
def interpolationExprQ {p m : ℕ}
    (model : ModelQ p m) (i j : Fin p) : LinearExprQ p m :=
  LinearExprQ.sub
    (LinearExprQ.sub
      (LinearExprQ.sub
        (LinearExprQ.valueVar (m := m) i)
        (LinearExprQ.valueVar (m := m) j))
      (LinearExprQ.gramBilinear
        (model.gradient j)
        (model.position i - model.position j)))
    (LinearExprQ.scale ((1 : ℚ) / 2)
      (LinearExprQ.gramNorm
        (model.gradient i - model.gradient j)))

/-- The symbolic interpolation expression has the exact real Gram-PEP slack
semantics for every realization of the model. -/
theorem evalR_interpolationExprQ
    {p m : ℕ} (model : ModelQ p m)
    (d : DataR (Fin p) m) (h : RealizesModelQ model d)
    (hG : IsGramSymmetric d.gram)
    (i j : Fin p) :
    (interpolationExprQ model i j).evalR d =
      interpolationSlack d i j := by
  simp [interpolationExprQ, interpolationSlack,
    h.position i, h.position j, h.gradient i, h.gradient j,
    castVecQ_sub,
    LinearExprQ.evalR_gramBilinear
      (model.gradient j) (model.position i - model.position j) d hG,
    LinearExprQ.evalR_gramNorm
      (model.gradient i - model.gradient j) d hG]

/-- Every additional formulation assumption evaluates nonnegatively. -/
def AssumptionsFeasibleR {p m : ℕ}
    (model : ModelQ p m) (d : DataR (Fin p) m) : Prop :=
  ∀ k : Fin model.assumptions.length,
    0 ≤ (model.assumptions.get k).evalR d

/-- One nonnegative multiplier on an ordered interpolation inequality. -/
structure InterpTermQ (p : ℕ) where
  weight : ℚ
  i : Fin p
  j : Fin p
  deriving DecidableEq, Repr

/-- One nonnegative multiplier on a formulation assumption. -/
structure AssumptionTermQ {p m : ℕ} (model : ModelQ p m) where
  weight : ℚ
  index : Fin model.assumptions.length

/-- General exact Gram upper certificate. -/
structure UpperCertQ {p m : ℕ} (model : ModelQ p m) where
  bound : ℚ
  objective : LinearExprQ p m
  interpTerms : List (InterpTermQ p)
  assumptionTerms : List (AssumptionTermQ model)
  dualMatrix : Gram m ℚ
  dualFactor : PSDFactorCertQ m

/-- Symbolic weighted sum of interpolation constraints. -/
def interpExprSumQ {p m : ℕ} (model : ModelQ p m) :
    List (InterpTermQ p) → LinearExprQ p m
  | [] => LinearExprQ.zero p m
  | t :: ts =>
      LinearExprQ.add
        (LinearExprQ.scale t.weight
          (interpolationExprQ model t.i t.j))
        (interpExprSumQ model ts)

/-- Symbolic weighted sum of formulation assumptions. -/
def assumptionExprSumQ {p m : ℕ} (model : ModelQ p m) :
    List (AssumptionTermQ model) → LinearExprQ p m
  | [] => LinearExprQ.zero p m
  | t :: ts =>
      LinearExprQ.add
        (LinearExprQ.scale t.weight
          (model.assumptions.get t.index))
        (assumptionExprSumQ model ts)

/-- Complete symbolic right-hand side of a Gram upper certificate. -/
def certificateRhsExprQ {p m : ℕ} {model : ModelQ p m}
    (c : UpperCertQ model) : LinearExprQ p m :=
  LinearExprQ.add
    (interpExprSumQ model c.interpTerms)
    (LinearExprQ.add
      (assumptionExprSumQ model c.assumptionTerms)
      (LinearExprQ.gramPairing c.dualMatrix))

/-- Symbolic target `bound - objective`. -/
def upperTargetExprQ {p m : ℕ}
    (bound : ℚ) (objective : LinearExprQ p m) : LinearExprQ p m :=
  LinearExprQ.sub (LinearExprQ.const p m bound) objective

/-- Real value of weighted interpolation constraints. -/
noncomputable def interpTermsValueR {p m : ℕ}
    (d : DataR (Fin p) m) : List (InterpTermQ p) → ℝ
  | [] => 0
  | t :: ts =>
      (t.weight : ℝ) * interpolationSlack d t.i t.j
        + interpTermsValueR d ts

/-- Real value of weighted formulation assumptions. -/
noncomputable def assumptionTermsValueR {p m : ℕ}
    (model : ModelQ p m) (d : DataR (Fin p) m) :
    List (AssumptionTermQ model) → ℝ
  | [] => 0
  | t :: ts =>
      (t.weight : ℝ) * (model.assumptions.get t.index).evalR d
        + assumptionTermsValueR model d ts

/-- Exact rational/real Frobenius pairing used by the dual PSD term. -/
noncomputable def gramPairingR {m : ℕ}
    (S : Gram m ℚ) (G : Gram m ℝ) : ℝ :=
  ∑ i, ∑ j, (S i j : ℝ) * G i j

/-- Real value of the complete certificate right-hand side. -/
noncomputable def certificateRhsValueR {p m : ℕ}
    {model : ModelQ p m} (c : UpperCertQ model)
    (d : DataR (Fin p) m) : ℝ :=
  interpTermsValueR d c.interpTerms
    + assumptionTermsValueR model d c.assumptionTerms
    + gramPairingR c.dualMatrix d.gram

@[simp] theorem evalR_interpExprSumQ
    {p m : ℕ} (model : ModelQ p m)
    (d : DataR (Fin p) m) (h : RealizesModelQ model d)
    (hG : IsGramSymmetric d.gram)
    (terms : List (InterpTermQ p)) :
    (interpExprSumQ model terms).evalR d =
      interpTermsValueR d terms := by
  induction terms with
  | nil =>
      simp [interpExprSumQ, interpTermsValueR]
  | cons t ts ih =>
      simp [interpExprSumQ, interpTermsValueR, ih,
        evalR_interpolationExprQ model d h hG]

@[simp] theorem evalR_assumptionExprSumQ
    {p m : ℕ} (model : ModelQ p m)
    (d : DataR (Fin p) m)
    (terms : List (AssumptionTermQ model)) :
    (assumptionExprSumQ model terms).evalR d =
      assumptionTermsValueR model d terms := by
  induction terms with
  | nil =>
      simp [assumptionExprSumQ, assumptionTermsValueR]
  | cons t ts ih =>
      simp [assumptionExprSumQ, assumptionTermsValueR, ih]

@[simp] theorem evalR_certificateRhsExprQ
    {p m : ℕ} {model : ModelQ p m}
    (c : UpperCertQ model) (d : DataR (Fin p) m)
    (h : RealizesModelQ model d)
    (hG : IsGramSymmetric d.gram) :
    (certificateRhsExprQ c).evalR d = certificateRhsValueR c d := by
  simp [certificateRhsExprQ, certificateRhsValueR,
    gramPairingR, evalR_interpExprSumQ model d h hG, add_assoc]

@[simp] theorem evalR_upperTargetExprQ
    {p m : ℕ} (bound : ℚ) (objective : LinearExprQ p m)
    (d : DataR (Fin p) m) :
    (upperTargetExprQ bound objective).evalR d =
      (bound : ℝ) - objective.evalR d := by
  simp [upperTargetExprQ]

end GramPEP
end LeanPEP
