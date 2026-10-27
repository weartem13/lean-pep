import LeanPEP.Profiles.GradientDescentGram

/-!
# Arbitrary-length gradient-descent certificates in the general Gram checker

This module is the third profile/compiler slice.  It transports the existing
arbitrary-`N` scalar SOS certificate for normalized unit-step gradient descent
to the compiler-generated general Gram formulation.

The scalar quadratic-polynomial identity is homogenized in the Gram basis

```text
(x_0 - x_star, g_0, ..., g_N).
```

Under this map:

* a scalar constant becomes the `(x_0 - x_star)` squared Gram coordinate;
* a scalar function value `f_i` becomes the relative value `f_i - f_star`;
* a scalar affine square becomes a weighted rank-one dual PSD factor; and
* the missing difference between the homogeneous radius and the unit-radius
  bound is supplied by the compiled assumption
  `1 - ||x_0 - x_star||^2_G >= 0`.

The resulting certificate is accepted by the existing general
`GramPEP.checkUpperCertQ` for every natural horizon.  No Gram semantics,
checker, PSD checker, scalar certificate, or generated artifact is changed.
-/

namespace LeanPEP
namespace Profiles
namespace GradientDescentGramCertificate

open scoped BigOperators

open LeanPEP.Toy.FiniteGD
open LeanPEP.Toy.FiniteGD.ParametricUpper
open LeanPEP.Profiles.GramCompilation
open LeanPEP.Profiles.GradientDescentGram
open LeanPEP.GramPEP

/-- Lift scalar function-value coefficients to relative Gram-model values.
The new point order is `x_star, x_0, ..., x_N`, so the coefficient at
`x_star` is the negative sum of all scalar coefficients. -/
def relativeValueCoeffQ {N : ℕ}
    (a : Fin (N + 1) → ℚ) : Fin (N + 2) → ℚ :=
  Fin.cases (-∑ i, a i) a

/-- Homogenize scalar constant, linear-gradient, and quadratic-gradient
coefficients into the Gram basis
`(x_0 - x_star, g_0, ..., g_N)`.

The two off-diagonal blocks store half of each scalar linear coefficient,
because the general Gram expression language uses the full Frobenius pairing
against a symmetric Gram matrix. -/
def homogenizedGramCoeffQ {N : ℕ}
    (p : QuadPolyQ N) : Gram (N + 2) ℚ :=
  fun i j =>
    Fin.cases
      (Fin.cases p.constCoeff (fun s => p.gradCoeff s / 2) j)
      (fun r =>
        Fin.cases (p.gradCoeff r / 2) (fun s => p.quadCoeff r s) j)
      i

/-- Exact scalar-polynomial-to-Gram-expression homogenization. -/
def homogenizeQuadPolyQ {N : ℕ}
    (p : QuadPolyQ N) : LinearExprQ (N + 2) (N + 2) :=
  { constCoeff := 0
    valueCoeff := relativeValueCoeffQ p.valueCoeff
    gramCoeff := homogenizedGramCoeffQ p }

@[simp] theorem relativeValueCoeffQ_zero {N : ℕ}
    (a : Fin (N + 1) → ℚ) :
    relativeValueCoeffQ a (0 : Fin (N + 2)) = -∑ i, a i := rfl

@[simp] theorem relativeValueCoeffQ_succ {N : ℕ}
    (a : Fin (N + 1) → ℚ) (i : Fin (N + 1)) :
    relativeValueCoeffQ a (Fin.succ i) = a i := rfl


/-- The total coefficient of one scalar value variable is one. -/
@[simp] theorem sum_unitCoeffQ {N : ℕ} (i : Fin (N + 1)) :
    ∑ j, unitCoeff i j = (1 : ℚ) := by
  classical
  rw [Fintype.sum_eq_single i (by
    intro j hji
    simp [unitCoeff, hji])]
  simp [unitCoeff]

@[simp] theorem homogenizedGramCoeffQ_zero_zero {N : ℕ}
    (p : QuadPolyQ N) :
    homogenizedGramCoeffQ p (0 : Fin (N + 2)) (0 : Fin (N + 2)) =
      p.constCoeff := rfl

@[simp] theorem homogenizedGramCoeffQ_zero_succ {N : ℕ}
    (p : QuadPolyQ N) (j : Fin (N + 1)) :
    homogenizedGramCoeffQ p (0 : Fin (N + 2)) (Fin.succ j) =
      p.gradCoeff j / 2 := rfl

@[simp] theorem homogenizedGramCoeffQ_succ_zero {N : ℕ}
    (p : QuadPolyQ N) (i : Fin (N + 1)) :
    homogenizedGramCoeffQ p (Fin.succ i) (0 : Fin (N + 2)) =
      p.gradCoeff i / 2 := rfl

@[simp] theorem homogenizedGramCoeffQ_succ_succ {N : ℕ}
    (p : QuadPolyQ N) (i j : Fin (N + 1)) :
    homogenizedGramCoeffQ p (Fin.succ i) (Fin.succ j) =
      p.quadCoeff i j := rfl

/-- Homogenization sends the zero scalar polynomial to the zero Gram
expression. -/
@[simp] theorem homogenizeQuadPolyQ_zero (N : ℕ) :
    homogenizeQuadPolyQ (QuadPolyQ.zero N) =
      LinearExprQ.zero (N + 2) (N + 2) := by
  apply LinearExprQ.ext
  · rfl
  · funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [homogenizeQuadPolyQ, relativeValueCoeffQ, QuadPolyQ.zero,
        LinearExprQ.zero]
    · rfl
  · funext i j
    refine Fin.cases ?_ (fun r => ?_) i
    · refine Fin.cases ?_ (fun s => ?_) j <;>
        simp [homogenizeQuadPolyQ, homogenizedGramCoeffQ,
          QuadPolyQ.zero, LinearExprQ.zero]
    · refine Fin.cases ?_ (fun s => ?_) j <;>
        simp [homogenizeQuadPolyQ, homogenizedGramCoeffQ,
          QuadPolyQ.zero, LinearExprQ.zero]

/-- Homogenization preserves scalar-polynomial addition. -/
@[simp] theorem homogenizeQuadPolyQ_add {N : ℕ}
    (p q : QuadPolyQ N) :
    homogenizeQuadPolyQ (QuadPolyQ.add p q) =
      LinearExprQ.add (homogenizeQuadPolyQ p) (homogenizeQuadPolyQ q) := by
  apply LinearExprQ.ext
  · simp [homogenizeQuadPolyQ, LinearExprQ.add]
  · funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · change
        -(∑ r, (p.valueCoeff r + q.valueCoeff r)) =
          -(∑ r, p.valueCoeff r) + -(∑ r, q.valueCoeff r)
      rw [Finset.sum_add_distrib]
      ring
    · rfl
  · funext i j
    refine Fin.cases ?_ (fun r => ?_) i
    · refine Fin.cases ?_ (fun s => ?_) j
      · rfl
      · change
          (p.gradCoeff s + q.gradCoeff s) / 2 =
            p.gradCoeff s / 2 + q.gradCoeff s / 2
        ring
    · refine Fin.cases ?_ (fun s => ?_) j
      · change
          (p.gradCoeff r + q.gradCoeff r) / 2 =
            p.gradCoeff r / 2 + q.gradCoeff r / 2
        ring
      · rfl

/-- Homogenization preserves scalar-polynomial negation. -/
@[simp] theorem homogenizeQuadPolyQ_neg {N : ℕ}
    (p : QuadPolyQ N) :
    homogenizeQuadPolyQ (QuadPolyQ.neg p) =
      LinearExprQ.neg (homogenizeQuadPolyQ p) := by
  apply LinearExprQ.ext
  · simp [homogenizeQuadPolyQ, LinearExprQ.neg]
  · funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · change -(∑ r, -p.valueCoeff r) = -(-(∑ r, p.valueCoeff r))
      simp
    · rfl
  · funext i j
    refine Fin.cases ?_ (fun r => ?_) i
    · refine Fin.cases ?_ (fun s => ?_) j
      · rfl
      · change (-p.gradCoeff s) / 2 = -(p.gradCoeff s / 2)
        ring
    · refine Fin.cases ?_ (fun s => ?_) j
      · change (-p.gradCoeff r) / 2 = -(p.gradCoeff r / 2)
        ring
      · rfl

/-- Homogenization preserves scalar-polynomial subtraction. -/
@[simp] theorem homogenizeQuadPolyQ_sub {N : ℕ}
    (p q : QuadPolyQ N) :
    homogenizeQuadPolyQ (QuadPolyQ.sub p q) =
      LinearExprQ.sub (homogenizeQuadPolyQ p) (homogenizeQuadPolyQ q) := by
  simp [QuadPolyQ.sub, LinearExprQ.sub]

/-- Homogenization preserves exact rational scaling. -/
@[simp] theorem homogenizeQuadPolyQ_scale {N : ℕ}
    (c : ℚ) (p : QuadPolyQ N) :
    homogenizeQuadPolyQ (QuadPolyQ.scale c p) =
      LinearExprQ.scale c (homogenizeQuadPolyQ p) := by
  apply LinearExprQ.ext
  · simp [homogenizeQuadPolyQ, LinearExprQ.scale]
  · funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · change
        -(∑ r, c * p.valueCoeff r) =
          c * (-(∑ r, p.valueCoeff r))
      rw [← Finset.mul_sum]
      ring
    · rfl
  · funext i j
    refine Fin.cases ?_ (fun r => ?_) i
    · refine Fin.cases ?_ (fun s => ?_) j
      · rfl
      · change (c * p.gradCoeff s) / 2 = c * (p.gradCoeff s / 2)
        ring
    · refine Fin.cases ?_ (fun s => ?_) j
      · change (c * p.gradCoeff r) / 2 = c * (p.gradCoeff r / 2)
        ring
      · rfl

/-- Homogenizing a scalar function-value variable produces its value relative
to `f_star`. -/
@[simp] theorem homogenizeQuadPolyQ_valueVar {N : ℕ}
    (i : Fin (N + 1)) :
    homogenizeQuadPolyQ (QuadPolyQ.valueVar i) =
      LinearExprQ.sub
        (LinearExprQ.valueVar (m := N + 2)
          (pointIndex (Point.iter i)))
        (LinearExprQ.valueVar (m := N + 2)
          (pointIndex (Point.star : Point N))) := by
  classical
  apply LinearExprQ.ext
  · simp [homogenizeQuadPolyQ, QuadPolyQ.valueVar,
      LinearExprQ.sub, LinearExprQ.add, LinearExprQ.neg,
      LinearExprQ.valueVar]
  · funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [homogenizeQuadPolyQ, relativeValueCoeffQ,
        QuadPolyQ.valueVar, sum_unitCoeffQ, LinearExprQ.sub,
        LinearExprQ.add, LinearExprQ.neg, LinearExprQ.valueVar,
        Ne.symm (Fin.succ_ne_zero i)]
    · simp [homogenizeQuadPolyQ, relativeValueCoeffQ,
        QuadPolyQ.valueVar, unitCoeff, LinearExprQ.sub,
        LinearExprQ.add, LinearExprQ.neg, LinearExprQ.valueVar,
        pointIndex]
  · funext r s
    refine Fin.cases ?_ (fun i => ?_) r
    · refine Fin.cases ?_ (fun j => ?_) s <;>
        simp [homogenizeQuadPolyQ, homogenizedGramCoeffQ,
          QuadPolyQ.valueVar, LinearExprQ.sub, LinearExprQ.add,
          LinearExprQ.neg, LinearExprQ.valueVar]
    · refine Fin.cases ?_ (fun j => ?_) s <;>
        simp [homogenizeQuadPolyQ, homogenizedGramCoeffQ,
          QuadPolyQ.valueVar, LinearExprQ.sub, LinearExprQ.add,
          LinearExprQ.neg, LinearExprQ.valueVar]

/-- Homogenizing a scalar product of affine gradient forms is exactly the
canonical symmetric Gram bilinear expression of their lifted vectors. -/
@[simp] theorem homogenizeQuadPolyQ_mulAffine {N : ℕ}
    (a b : GradAffineQ N) :
    homogenizeQuadPolyQ (QuadPolyQ.mulAffine a b) =
      LinearExprQ.gramBilinear (affineVecQ a) (affineVecQ b) := by
  apply LinearExprQ.ext
  · simp [homogenizeQuadPolyQ, QuadPolyQ.mulAffine,
      LinearExprQ.gramBilinear, LinearExprQ.scale,
      LinearExprQ.add, LinearExprQ.gramOuter]
  · funext i
    refine Fin.cases ?_ (fun k => ?_) i <;>
      simp [homogenizeQuadPolyQ, relativeValueCoeffQ,
        QuadPolyQ.mulAffine, LinearExprQ.gramBilinear,
        LinearExprQ.scale, LinearExprQ.add, LinearExprQ.gramOuter]
  · funext i j
    refine Fin.cases ?_ (fun r => ?_) i
    · refine Fin.cases ?_ (fun s => ?_) j
      · simp [homogenizeQuadPolyQ, homogenizedGramCoeffQ,
          QuadPolyQ.mulAffine, LinearExprQ.gramBilinear,
          LinearExprQ.scale, LinearExprQ.add, LinearExprQ.gramOuter,
          affineVecQ]
        ring
      · simp [homogenizeQuadPolyQ, homogenizedGramCoeffQ,
          QuadPolyQ.mulAffine, LinearExprQ.gramBilinear,
          LinearExprQ.scale, LinearExprQ.add, LinearExprQ.gramOuter,
          affineVecQ]
        ring
    · refine Fin.cases ?_ (fun s => ?_) j
      · simp [homogenizeQuadPolyQ, homogenizedGramCoeffQ,
          QuadPolyQ.mulAffine, LinearExprQ.gramBilinear,
          LinearExprQ.scale, LinearExprQ.add, LinearExprQ.gramOuter,
          affineVecQ]
        ring
      · simp [homogenizeQuadPolyQ, homogenizedGramCoeffQ,
          QuadPolyQ.mulAffine, symOuterQ,
          LinearExprQ.gramBilinear, LinearExprQ.scale,
          LinearExprQ.add, LinearExprQ.gramOuter, affineVecQ]
        ring

/-- A scalar affine square becomes one Gram squared norm. -/
@[simp] theorem homogenizeQuadPolyQ_square {N : ℕ}
    (a : GradAffineQ N) :
    homogenizeQuadPolyQ (QuadPolyQ.square a) =
      LinearExprQ.gramNorm (affineVecQ a) := by
  simpa [QuadPolyQ.square, LinearExprQ.gramNorm] using
    homogenizeQuadPolyQ_mulAffine a a

/-- A scalar affine constant is homogenized to the initial-displacement norm. -/
@[simp] theorem homogenizeQuadPolyQ_constAffine (N : ℕ) (c : ℚ) :
    homogenizeQuadPolyQ
        (QuadPolyQ.ofAffine (GradAffineQ.const N c)) =
      LinearExprQ.scale c
        (LinearExprQ.gramNorm (initialBasisQ N)) := by
  apply LinearExprQ.ext
  · simp [homogenizeQuadPolyQ, QuadPolyQ.ofAffine,
      GradAffineQ.const, LinearExprQ.scale,
      LinearExprQ.gramNorm, LinearExprQ.gramBilinear,
      LinearExprQ.add, LinearExprQ.gramOuter]
  · funext i
    refine Fin.cases ?_ (fun k => ?_) i <;>
      simp [homogenizeQuadPolyQ, relativeValueCoeffQ,
        QuadPolyQ.ofAffine, GradAffineQ.const,
        LinearExprQ.scale, LinearExprQ.gramNorm,
        LinearExprQ.gramBilinear, LinearExprQ.add,
        LinearExprQ.gramOuter, initialBasisQ,
        initialBasisIndex, standardBasisExpr] <;>
      ring
  · funext i j
    refine Fin.cases ?_ (fun r => ?_) i
    · refine Fin.cases ?_ (fun s => ?_) j
      · simp [homogenizeQuadPolyQ, homogenizedGramCoeffQ,
          QuadPolyQ.ofAffine, GradAffineQ.const,
          LinearExprQ.scale, LinearExprQ.gramNorm,
          LinearExprQ.gramBilinear, LinearExprQ.add,
          LinearExprQ.gramOuter, initialBasisQ,
          initialBasisIndex, standardBasisExpr]
        ring
      · simp [homogenizeQuadPolyQ, homogenizedGramCoeffQ,
          QuadPolyQ.ofAffine, GradAffineQ.const,
          LinearExprQ.scale, LinearExprQ.gramNorm,
          LinearExprQ.gramBilinear, LinearExprQ.add,
          LinearExprQ.gramOuter, initialBasisQ,
          initialBasisIndex, standardBasisExpr]
    · refine Fin.cases ?_ (fun s => ?_) j
      · simp [homogenizeQuadPolyQ, homogenizedGramCoeffQ,
          QuadPolyQ.ofAffine, GradAffineQ.const,
          LinearExprQ.scale, LinearExprQ.gramNorm,
          LinearExprQ.gramBilinear, LinearExprQ.add,
          LinearExprQ.gramOuter, initialBasisQ,
          initialBasisIndex, standardBasisExpr]
      · simp [homogenizeQuadPolyQ, homogenizedGramCoeffQ,
          QuadPolyQ.ofAffine, GradAffineQ.const,
          LinearExprQ.scale, LinearExprQ.gramNorm,
          LinearExprQ.gramBilinear, LinearExprQ.add,
          LinearExprQ.gramOuter, initialBasisQ,
          initialBasisIndex, standardBasisExpr]

/-- Lifted affine vectors preserve subtraction. -/
@[simp] theorem affineVecQ_sub {N : ℕ}
    (a b : GradAffineQ N) :
    affineVecQ (GradAffineQ.sub a b) = affineVecQ a - affineVecQ b := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i <;>
    simp [affineVecQ, GradAffineQ.sub, GradAffineQ.add,
      GradAffineQ.neg, sub_eq_add_neg]

/-- The legacy scalar gradient form and the compiled Gram gradient vector are
identical under homogenization. -/
@[simp] theorem affineVecQ_gradAffineQ {N : ℕ} (i : Point N) :
    affineVecQ (gradAffineQ i) = pointGradientVecQ i := by
  cases i with
  | star =>
      funext k
      refine Fin.cases ?_ (fun r => ?_) k <;>
        simp [gradAffineQ, pointGradientVecQ, affineVecQ,
          GradAffineQ.zero]
  | iter i =>
      funext k
      refine Fin.cases ?_ (fun r => ?_) k
      · simp [gradAffineQ, pointGradientVecQ, affineVecQ,
          GradAffineQ.basis, unitCoeff, sampledGradientBasisQ,
          gradientBasisIndex, standardBasisExpr,
          Ne.symm (Fin.succ_ne_zero i)]
      · simp [gradAffineQ, pointGradientVecQ, affineVecQ,
          GradAffineQ.basis, unitCoeff, sampledGradientBasisQ,
          gradientBasisIndex, standardBasisExpr]

/-- Relative function-value expression attached to a source point. -/
def relativePointValueExprQ {N : ℕ}
    (i : Point N) : LinearExprQ (N + 2) (N + 2) :=
  LinearExprQ.sub
    (LinearExprQ.valueVar (m := N + 2) (pointIndex i))
    (LinearExprQ.valueVar (m := N + 2)
      (pointIndex (Point.star : Point N)))

/-- Source point-value polynomials homogenize to relative Gram-model values. -/
@[simp] theorem homogenizePointValuePolyQ {N : ℕ} (i : Point N) :
    homogenizeQuadPolyQ (pointValuePolyQ i) =
      relativePointValueExprQ i := by
  cases i with
  | star =>
      apply LinearExprQ.ext
      · simp [pointValuePolyQ, relativePointValueExprQ,
          homogenizeQuadPolyQ_zero, LinearExprQ.sub,
          LinearExprQ.add, LinearExprQ.neg,
          LinearExprQ.valueVar, LinearExprQ.zero]
      · funext k
        simp [pointValuePolyQ, relativePointValueExprQ,
          homogenizeQuadPolyQ_zero, LinearExprQ.sub,
          LinearExprQ.add, LinearExprQ.neg,
          LinearExprQ.valueVar, LinearExprQ.zero]
      · funext r s
        simp [pointValuePolyQ, relativePointValueExprQ,
          homogenizeQuadPolyQ_zero, LinearExprQ.sub,
          LinearExprQ.add, LinearExprQ.neg,
          LinearExprQ.valueVar, LinearExprQ.zero]
  | iter i =>
      exact homogenizeQuadPolyQ_valueVar i

/-- Subtracting relative point values cancels the common `f_star` offset. -/
theorem relativePointValueExprQ_sub {N : ℕ} (i j : Point N) :
    LinearExprQ.sub (relativePointValueExprQ i)
        (relativePointValueExprQ j) =
      LinearExprQ.sub
        (LinearExprQ.valueVar (m := N + 2) (pointIndex i))
        (LinearExprQ.valueVar (m := N + 2) (pointIndex j)) := by
  apply LinearExprQ.ext
  · simp [relativePointValueExprQ, LinearExprQ.sub,
      LinearExprQ.add, LinearExprQ.neg, LinearExprQ.valueVar]
  · funext k
    simp [relativePointValueExprQ, LinearExprQ.sub,
      LinearExprQ.add, LinearExprQ.neg, LinearExprQ.valueVar]
  · funext r s
    simp [relativePointValueExprQ, LinearExprQ.sub,
      LinearExprQ.add, LinearExprQ.neg, LinearExprQ.valueVar]

/-- Every legacy scalar interpolation polynomial becomes exactly the ordered
interpolation expression of the compiler-generated Gram model. -/
theorem homogenizeSlackPolyQ_unitGD {N : ℕ} (i j : Point N) :
    homogenizeQuadPolyQ (slackPolyQ i j) =
      interpolationExprQ (unitGDModelQ N) (pointIndex i) (pointIndex j) := by
  unfold slackPolyQ interpolationExprQ
  rw [homogenizeQuadPolyQ_sub, homogenizeQuadPolyQ_sub,
    homogenizeQuadPolyQ_sub, homogenizePointValuePolyQ,
    homogenizePointValuePolyQ, relativePointValueExprQ_sub,
    homogenizeQuadPolyQ_mulAffine, homogenizeQuadPolyQ_scale,
    homogenizeQuadPolyQ_square]
  simp only [affineVecQ_sub, affineVecQ_gradAffineQ,
    unitGDModelQ_position_pointIndex,
    unitGDModelQ_gradient_pointIndex]

/-- Translate one scalar interpolation multiplier to the declared Gram point
order. -/
def gramInterpTermQ {N : ℕ}
    (t : LeanPEP.Toy.FiniteGD.InterpTermQ N) :
    LeanPEP.GramPEP.InterpTermQ (N + 2) :=
  { weight := t.weight
    i := pointIndex t.i
    j := pointIndex t.j }

/-- Homogenization commutes with a complete scalar interpolation sum. -/
theorem homogenizeInterpPolySumQ_unitGD {N : ℕ}
    (terms : List (LeanPEP.Toy.FiniteGD.InterpTermQ N)) :
    homogenizeQuadPolyQ (LeanPEP.Toy.FiniteGD.interpPolySumQ terms) =
      LeanPEP.GramPEP.interpExprSumQ (unitGDModelQ N)
        (terms.map gramInterpTermQ) := by
  induction terms with
  | nil =>
      simp [LeanPEP.Toy.FiniteGD.interpPolySumQ,
        LeanPEP.GramPEP.interpExprSumQ]
  | cons t ts ih =>
      simp [LeanPEP.Toy.FiniteGD.interpPolySumQ,
        LeanPEP.GramPEP.interpExprSumQ, ih,
        homogenizeSlackPolyQ_unitGD, gramInterpTermQ]

/-- Translate one scalar weighted affine square to one exact rational rank-one
dual factor over the compiled Gram basis. -/
def gramSquareFactorQ {N : ℕ}
    (t : SquareTermQ N) : RankOneFactorQ (N + 2) :=
  { weight := t.weight
    vector := affineVecQ t.form }

/-- The symbolic Gram pairing of one weighted outer product is exactly its
weighted squared-norm expression. -/
theorem gramPairingExpr_weightedOuterQ {m p : ℕ}
    (t : RankOneFactorQ m) :
    LinearExprQ.gramPairing (p := p) (weightedOuterQ t) =
      LinearExprQ.scale t.weight
        (LinearExprQ.gramNorm t.vector) := by
  apply LinearExprQ.ext
  · simp [LinearExprQ.gramPairing, LinearExprQ.scale,
      LinearExprQ.gramNorm, LinearExprQ.gramBilinear,
      LinearExprQ.add, LinearExprQ.gramOuter]
  · funext i
    simp [LinearExprQ.gramPairing, LinearExprQ.scale,
      LinearExprQ.gramNorm, LinearExprQ.gramBilinear,
      LinearExprQ.add, LinearExprQ.gramOuter]
  · funext i j
    simp [LinearExprQ.gramPairing, weightedOuterQ,
      LinearExprQ.scale, LinearExprQ.gramNorm,
      LinearExprQ.gramBilinear, LinearExprQ.add,
      LinearExprQ.gramOuter]
    ring

/-- Symbolic Gram pairing is additive in its exact rational matrix. -/
theorem gramPairingExpr_add {m p : ℕ} (S T : Gram m ℚ) :
    LinearExprQ.gramPairing (p := p) (S + T) =
      LinearExprQ.add
        (LinearExprQ.gramPairing (p := p) S)
        (LinearExprQ.gramPairing (p := p) T) := by
  apply LinearExprQ.ext
  · simp [LinearExprQ.gramPairing, LinearExprQ.add]
  · funext i
    simp [LinearExprQ.gramPairing, LinearExprQ.add]
  · funext i j
    rfl

/-- Homogenization of all scalar affine squares is the Frobenius pairing with
the exact dual matrix reconstructed from the corresponding rank-one factors. -/
theorem homogenizeSquarePolySumQ {N : ℕ}
    (terms : List (SquareTermQ N)) :
    homogenizeQuadPolyQ (squarePolySumQ terms) =
      LinearExprQ.gramPairing (p := N + 2)
        (factorGramQ (terms.map gramSquareFactorQ)) := by
  induction terms with
  | nil =>
      simp [squarePolySumQ, factorGramQ,
        LinearExprQ.gramPairing, LinearExprQ.zero]
  | cons t ts ih =>
      simp [squarePolySumQ, factorGramQ, ih,
        gramPairingExpr_add, gramPairingExpr_weightedOuterQ,
        gramSquareFactorQ]

/-- Complete scalar certificate right-hand sides homogenize to a Gram
interpolation sum plus the dual PSD pairing. -/
theorem homogenizeCertificateRhsPolyQ_unitGD {N : ℕ}
    (c : LeanPEP.Toy.FiniteGD.UpperCertQ N) :
    homogenizeQuadPolyQ
        (LeanPEP.Toy.FiniteGD.certificateRhsPolyQ c) =
      LinearExprQ.add
        (LeanPEP.GramPEP.interpExprSumQ (unitGDModelQ N)
          (c.interpTerms.map gramInterpTermQ))
        (LinearExprQ.gramPairing (p := N + 2)
          (factorGramQ (c.squareTerms.map gramSquareFactorQ))) := by
  simp [LeanPEP.Toy.FiniteGD.certificateRhsPolyQ,
    homogenizeInterpPolySumQ_unitGD, homogenizeSquarePolySumQ]

/-- Exact dual-factor list obtained from the arbitrary-`N` scalar SOS terms. -/
def gdGramDualFactorsQ (N : ℕ) : List (RankOneFactorQ (N + 2)) :=
  (gdSquareTermsQ N).map gramSquareFactorQ

/-- Exact dual matrix reconstructed from the transported rank-one factors. -/
def gdGramDualMatrixQ (N : ℕ) : Gram (N + 2) ℚ :=
  factorGramQ (gdGramDualFactorsQ N)

/-- Factor certificate submitted to the unchanged Gram PSD checker. -/
def gdGramDualFactorCertQ (N : ℕ) : PSDFactorCertQ (N + 2) :=
  { factors := gdGramDualFactorsQ N }

/-- The compiled GD model has exactly one unit-radius assumption. -/
@[simp] theorem unitGDModelQ_assumptions (N : ℕ) :
    (unitGDModelQ N).assumptions =
      [initialRadiusExprQ (N := N) unitRadiusNormalizationQ] := rfl

/-- Index of the sole compiled unit-radius assumption. -/
def unitGDRadiusAssumptionIndexQ (N : ℕ) :
    Fin (unitGDModelQ N).assumptions.length :=
  ⟨0, by simp⟩

@[simp] theorem unitGDRadiusAssumption_get (N : ℕ) :
    (unitGDModelQ N).assumptions.get (unitGDRadiusAssumptionIndexQ N) =
      initialRadiusExprQ (N := N) unitRadiusNormalizationQ := by
  simp [unitGDRadiusAssumptionIndexQ]

/-- The single radius multiplier needed to dehomogenize the scalar identity. -/
def gdGramAssumptionTermsQ (N : ℕ) :
    List (AssumptionTermQ (unitGDModelQ N)) :=
  [{ weight := gdBoundQ N
     index := unitGDRadiusAssumptionIndexQ N }]

/-- Arbitrary-horizon Gram upper certificate transported from the existing
scalar certificate. -/
def gdGramUpperCertQ (N : ℕ) :
    LeanPEP.GramPEP.UpperCertQ (unitGDModelQ N) :=
  { bound := gdBoundQ N
    objective := unitGDObjectiveQ N
    interpTerms := (gdInterpTermsQ N).map gramInterpTermQ
    assumptionTerms := gdGramAssumptionTermsQ N
    dualMatrix := gdGramDualMatrixQ N
    dualFactor := gdGramDualFactorCertQ N }

/-- Transported interpolation weights remain nonnegative. -/
theorem gdGramInterpWeights_nonneg (N : ℕ) :
    ∀ t ∈ (gdInterpTermsQ N).map gramInterpTermQ, 0 ≤ t.weight := by
  intro t ht
  rcases List.mem_map.mp ht with ⟨s, hs, rfl⟩
  exact gdInterpTermsQ_weights_nonneg N s hs

/-- Transported rank-one factor weights remain nonnegative. -/
theorem gdGramDualWeights_nonneg (N : ℕ) :
    ∀ t ∈ gdGramDualFactorsQ N, 0 ≤ t.weight := by
  intro t ht
  rcases List.mem_map.mp ht with ⟨s, hs, rfl⟩
  exact gdSquareTermsQ_weights_nonneg N s hs

/-- The radius multiplier is nonnegative for every natural horizon. -/
theorem gdGramAssumptionWeights_nonneg (N : ℕ) :
    ∀ t ∈ gdGramAssumptionTermsQ N, 0 ≤ t.weight := by
  intro t ht
  have ht' :
      t = { weight := gdBoundQ N
            index := unitGDRadiusAssumptionIndexQ N } := by
    simpa [gdGramAssumptionTermsQ] using ht
  subst t
  unfold gdBoundQ
  positivity

/-- The transported dual matrix has an exact accepted-by-construction
rank-one PSD factorization. -/
theorem gdGramDualValidQ (N : ℕ) :
    PSDFactorValidQ (gdGramDualMatrixQ N) (gdGramDualFactorCertQ N) := by
  exact
    { symmetric := factorGramQ_symmetric (gdGramDualFactorsQ N)
      weights := gdGramDualWeights_nonneg N
      identity := rfl }

/-- The singleton assumption sum is exactly the bound times the compiled
unit-radius expression. -/
theorem gdGramAssumptionExprSumQ (N : ℕ) :
    assumptionExprSumQ (unitGDModelQ N) (gdGramAssumptionTermsQ N) =
      LinearExprQ.scale (gdBoundQ N)
        (initialRadiusExprQ (N := N) unitRadiusNormalizationQ) := by
  apply LinearExprQ.ext
  · simp [gdGramAssumptionTermsQ, assumptionExprSumQ,
      LinearExprQ.add, LinearExprQ.zero]
  · funext i
    simp [gdGramAssumptionTermsQ, assumptionExprSumQ,
      LinearExprQ.add, LinearExprQ.zero]
  · funext i j
    simp [gdGramAssumptionTermsQ, assumptionExprSumQ,
      LinearExprQ.add, LinearExprQ.zero]

/-- Commuting the middle two summands in the custom exact expression syntax. -/
theorem linearExprQ_add_middle_comm {p m : ℕ}
    (a b c : LinearExprQ p m) :
    LinearExprQ.add a (LinearExprQ.add b c) =
      LinearExprQ.add b (LinearExprQ.add a c) := by
  apply LinearExprQ.ext
  · simp [LinearExprQ.add]
    ring
  · funext i
    simp [LinearExprQ.add]
    ring
  · funext i j
    simp [LinearExprQ.add]
    ring

/-- The complete transported Gram right-hand side has the expected three
channels: interpolation, radius assumption, and dual PSD pairing. -/
theorem gdGramCertificateRhsExprQ (N : ℕ) :
    certificateRhsExprQ (gdGramUpperCertQ N) =
      LinearExprQ.add
        (interpExprSumQ (unitGDModelQ N)
          ((gdInterpTermsQ N).map gramInterpTermQ))
        (LinearExprQ.add
          (LinearExprQ.scale (gdBoundQ N)
            (initialRadiusExprQ (N := N) unitRadiusNormalizationQ))
          (LinearExprQ.gramPairing (p := N + 2)
            (gdGramDualMatrixQ N))) := by
  unfold certificateRhsExprQ gdGramUpperCertQ
  rw [gdGramAssumptionExprSumQ]

/-- The scalar objective index is the final iterate index. -/
theorem gdObjective_eq_last (N : ℕ) :
    gdObjective N = Fin.last N := by
  apply Fin.ext
  rfl

/-- The compiler-generated objective is the scalar objective interpreted as a
function-value gap relative to `f_star`. -/
theorem unitGDObjectiveQ_eq_relativeGDObjective (N : ℕ) :
    unitGDObjectiveQ N = relativePointValueExprQ (Point.iter (gdObjective N)) := by
  have hobjective : gdObjective N = Fin.last N := gdObjective_eq_last N
  simp [unitGDObjectiveQ, unitGDGramProfileQ, compileObjectiveQ,
    finalGapObjectiveProfileQ, objectiveExprQ,
    relativePointValueExprQ, hobjective]

/-- Exact algebra that combines the homogeneous scalar constant with the
compiled radius assumption. -/
theorem radiusHomogenizationIdentityQ {N : ℕ}
    (bound : ℚ) (objective : LinearExprQ (N + 2) (N + 2)) :
    LinearExprQ.add
        (LinearExprQ.scale bound
          (initialRadiusExprQ (N := N) unitRadiusNormalizationQ))
        (LinearExprQ.sub
          (LinearExprQ.scale bound
            (LinearExprQ.gramNorm (initialBasisQ N)))
          objective) =
      LinearExprQ.sub
        (LinearExprQ.const (N + 2) (N + 2) bound)
        objective := by
  apply LinearExprQ.ext
  · simp [initialRadiusExprQ, unitRadiusNormalizationQ,
      LinearExprQ.sub, LinearExprQ.add, LinearExprQ.neg,
      LinearExprQ.scale, LinearExprQ.const]
    ring
  · funext i
    simp [initialRadiusExprQ, unitRadiusNormalizationQ,
      LinearExprQ.sub, LinearExprQ.add, LinearExprQ.neg,
      LinearExprQ.scale, LinearExprQ.const]
  · funext i j
    simp [initialRadiusExprQ, unitRadiusNormalizationQ,
      LinearExprQ.sub, LinearExprQ.add, LinearExprQ.neg,
      LinearExprQ.scale, LinearExprQ.const]

/-- The bound-weighted radius assumption plus the homogenized scalar target is
exactly the general Gram target `bound - (f_N - f_star)`. -/
theorem gdGramUpperTargetDecompositionQ (N : ℕ) :
    LinearExprQ.add
        (LinearExprQ.scale (gdBoundQ N)
          (initialRadiusExprQ (N := N) unitRadiusNormalizationQ))
        (homogenizeQuadPolyQ
          (upperTargetPolyQ (gdBoundQ N) (gdObjective N))) =
      upperTargetExprQ (gdBoundQ N) (unitGDObjectiveQ N) := by
  rw [upperTargetPolyQ, homogenizeQuadPolyQ_sub,
    homogenizeQuadPolyQ_constAffine,
    homogenizeQuadPolyQ_valueVar,
    unitGDObjectiveQ_eq_relativeGDObjective]
  unfold upperTargetExprQ relativePointValueExprQ
  exact radiusHomogenizationIdentityQ
    (N := N) (gdBoundQ N)
    (LinearExprQ.sub
      (LinearExprQ.valueVar (m := N + 2)
        (pointIndex (Point.iter (gdObjective N))))
      (LinearExprQ.valueVar (m := N + 2)
        (pointIndex (Point.star : Point N))))

/-- The arbitrary-`N` scalar polynomial identity transports to the complete
Gram certificate identity. -/
theorem gdGramUpperCertQ_identity_all (N : ℕ) :
    certificateRhsExprQ (gdGramUpperCertQ N) =
      upperTargetExprQ (gdBoundQ N) (unitGDObjectiveQ N) := by
  rw [gdGramCertificateRhsExprQ]
  rw [linearExprQ_add_middle_comm]
  change
    LinearExprQ.add
        (LinearExprQ.scale (gdBoundQ N)
          (initialRadiusExprQ (N := N) unitRadiusNormalizationQ))
        (LinearExprQ.add
          (interpExprSumQ (unitGDModelQ N)
            ((gdUpperCertQ N).interpTerms.map gramInterpTermQ))
          (LinearExprQ.gramPairing (p := N + 2)
            (factorGramQ ((gdUpperCertQ N).squareTerms.map gramSquareFactorQ)))) =
      upperTargetExprQ (gdBoundQ N) (unitGDObjectiveQ N)
  rw [← homogenizeCertificateRhsPolyQ_unitGD (gdUpperCertQ N)]
  have hscalar :
      certificateRhsPolyQ (gdUpperCertQ N) =
        upperTargetPolyQ (gdBoundQ N) (gdObjective N) :=
    gdCertificateIdentityQ_all N
  rw [hscalar]
  exact gdGramUpperTargetDecompositionQ N

/-- Proposition-level validity of the transported general Gram certificate for
all horizons. -/
theorem gdGramUpperCertQ_valid_all (N : ℕ) :
    LeanPEP.GramPEP.UpperCertValidQ (gdGramUpperCertQ N) := by
  exact
    { interpWeights := gdGramInterpWeights_nonneg N
      assumptionWeights := gdGramAssumptionWeights_nonneg N
      dualValid := gdGramDualValidQ N
      identity := gdGramUpperCertQ_identity_all N }

/-- The unchanged executable general Gram checker accepts the transported
closed-form GD certificate for every natural horizon. -/
theorem gdGramUpperCertQ_check_all (N : ℕ) :
    LeanPEP.GramPEP.checkUpperCertQ (gdGramUpperCertQ N) = true :=
  LeanPEP.GramPEP.checkUpperCertQ_complete
    (gdGramUpperCertQ N) (gdGramUpperCertQ_valid_all N)

/-- Arbitrary-horizon finite Gram-PEP upper theorem routed entirely through the
compiler-generated model and the unchanged general Gram checker. -/
theorem gdGram_upper_all
    (N : ℕ)
    (d : LeanPEP.GramPEP.DataR (Fin (N + 2)) (N + 2))
    (hrealizes : RealizesModelQ (unitGDModelQ N) d)
    (hcore : CoreFeasible d)
    (hassumptions : AssumptionsFeasibleR (unitGDModelQ N) d) :
    (unitGDObjectiveQ N).evalR d ≤ (gdBoundQ N : ℝ) := by
  simpa [gdGramUpperCertQ] using
    LeanPEP.GramPEP.checkUpperCertQ_sound_real
      (gdGramUpperCertQ N) (gdGramUpperCertQ_check_all N)
      d hrealizes hcore hassumptions

end GradientDescentGramCertificate
end Profiles
end LeanPEP
