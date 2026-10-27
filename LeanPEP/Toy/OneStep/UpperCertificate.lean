import LeanPEP.Toy.OneStep.RationalData

/-!
# Explicit exact upper-certificate data for the one-step finite PEP

A certificate represents an identity

`bound - f1 = Σ λᵢⱼ * slack i j + Σ μₖ * (affine form in g0,g1)^2`.

The interpolation multipliers `λᵢⱼ` and square weights `μₖ` must be
nonnegative.  The polynomial identity is checked coefficient by coefficient
using exact rational arithmetic.
-/

namespace LeanPEP
namespace Toy
namespace OneStep

/-- The quadratic polynomial basis needed by the normalized one-step problem:
`1, g0, g1, f0, f1, g0^2, g0*g1, g1^2`. -/
structure QuadPolyQ where
  constCoeff : ℚ
  g0Coeff : ℚ
  g1Coeff : ℚ
  f0Coeff : ℚ
  f1Coeff : ℚ
  g0SqCoeff : ℚ
  g0g1Coeff : ℚ
  g1SqCoeff : ℚ
  deriving DecidableEq, Repr

namespace QuadPolyQ

/-- Zero polynomial. -/
def zero : QuadPolyQ :=
  { constCoeff := 0
    g0Coeff := 0
    g1Coeff := 0
    f0Coeff := 0
    f1Coeff := 0
    g0SqCoeff := 0
    g0g1Coeff := 0
    g1SqCoeff := 0 }

/-- Constant polynomial. -/
def constant (a : ℚ) : QuadPolyQ :=
  { constCoeff := a
    g0Coeff := 0
    g1Coeff := 0
    f0Coeff := 0
    f1Coeff := 0
    g0SqCoeff := 0
    g0g1Coeff := 0
    g1SqCoeff := 0 }

/-- Coefficientwise addition. -/
def add (p q : QuadPolyQ) : QuadPolyQ :=
  { constCoeff := p.constCoeff + q.constCoeff
    g0Coeff := p.g0Coeff + q.g0Coeff
    g1Coeff := p.g1Coeff + q.g1Coeff
    f0Coeff := p.f0Coeff + q.f0Coeff
    f1Coeff := p.f1Coeff + q.f1Coeff
    g0SqCoeff := p.g0SqCoeff + q.g0SqCoeff
    g0g1Coeff := p.g0g1Coeff + q.g0g1Coeff
    g1SqCoeff := p.g1SqCoeff + q.g1SqCoeff }

/-- Multiply every coefficient by an exact rational scalar. -/
def scale (a : ℚ) (p : QuadPolyQ) : QuadPolyQ :=
  { constCoeff := a * p.constCoeff
    g0Coeff := a * p.g0Coeff
    g1Coeff := a * p.g1Coeff
    f0Coeff := a * p.f0Coeff
    f1Coeff := a * p.f1Coeff
    g0SqCoeff := a * p.g0SqCoeff
    g0g1Coeff := a * p.g0g1Coeff
    g1SqCoeff := a * p.g1SqCoeff }

/-- Coefficientwise negation. -/
def neg (p : QuadPolyQ) : QuadPolyQ := scale (-1) p

/-- Coefficientwise subtraction. -/
def sub (p q : QuadPolyQ) : QuadPolyQ := add p (neg q)

/-- Evaluate a symbolic polynomial on rational finite PEP data. -/
def evalQ (p : QuadPolyQ) (d : OneStepDataQ) : ℚ :=
  p.constCoeff
    + p.g0Coeff * d.g0
    + p.g1Coeff * d.g1
    + p.f0Coeff * d.f0
    + p.f1Coeff * d.f1
    + p.g0SqCoeff * d.g0^2
    + p.g0g1Coeff * (d.g0 * d.g1)
    + p.g1SqCoeff * d.g1^2

/-- Evaluate the same exact rational coefficients on real finite PEP data. -/
noncomputable def evalR (p : QuadPolyQ) (d : OneStepData) : ℝ :=
  (p.constCoeff : ℝ)
    + (p.g0Coeff : ℝ) * d.g0
    + (p.g1Coeff : ℝ) * d.g1
    + (p.f0Coeff : ℝ) * d.f0
    + (p.f1Coeff : ℝ) * d.f1
    + (p.g0SqCoeff : ℝ) * d.g0^2
    + (p.g0g1Coeff : ℝ) * (d.g0 * d.g1)
    + (p.g1SqCoeff : ℝ) * d.g1^2

@[simp] theorem evalQ_zero (d : OneStepDataQ) : zero.evalQ d = 0 := by
  norm_num [zero, evalQ]

@[simp] theorem evalR_zero (d : OneStepData) : zero.evalR d = 0 := by
  norm_num [zero, evalR]

@[simp] theorem evalQ_add (p q : QuadPolyQ) (d : OneStepDataQ) :
    (add p q).evalQ d = p.evalQ d + q.evalQ d := by
  simp [add, evalQ]
  ring

@[simp] theorem evalR_add (p q : QuadPolyQ) (d : OneStepData) :
    (add p q).evalR d = p.evalR d + q.evalR d := by
  simp [add, evalR]
  ring

@[simp] theorem evalQ_scale (a : ℚ) (p : QuadPolyQ) (d : OneStepDataQ) :
    (scale a p).evalQ d = a * p.evalQ d := by
  simp [scale, evalQ]
  ring

@[simp] theorem evalR_scale (a : ℚ) (p : QuadPolyQ) (d : OneStepData) :
    (scale a p).evalR d = (a : ℝ) * p.evalR d := by
  simp [scale, evalR]
  ring

end QuadPolyQ

/-- Exact symbolic polynomial for each interpolation slack. -/
def slackPolyQ : Pt → Pt → QuadPolyQ
  | Pt.star, Pt.star => QuadPolyQ.zero
  | Pt.star, Pt.p0 =>
      { constCoeff := 0
        g0Coeff := 1
        g1Coeff := 0
        f0Coeff := -1
        f1Coeff := 0
        g0SqCoeff := -((1 : ℚ) / 2)
        g0g1Coeff := 0
        g1SqCoeff := 0 }
  | Pt.star, Pt.p1 =>
      { constCoeff := 0
        g0Coeff := 0
        g1Coeff := 1
        f0Coeff := 0
        f1Coeff := -1
        g0SqCoeff := 0
        g0g1Coeff := -1
        g1SqCoeff := -((1 : ℚ) / 2) }
  | Pt.p0, Pt.star =>
      { constCoeff := 0
        g0Coeff := 0
        g1Coeff := 0
        f0Coeff := 1
        f1Coeff := 0
        g0SqCoeff := -((1 : ℚ) / 2)
        g0g1Coeff := 0
        g1SqCoeff := 0 }
  | Pt.p0, Pt.p0 => QuadPolyQ.zero
  | Pt.p0, Pt.p1 =>
      { constCoeff := 0
        g0Coeff := 0
        g1Coeff := 0
        f0Coeff := 1
        f1Coeff := -1
        g0SqCoeff := -((1 : ℚ) / 2)
        g0g1Coeff := 0
        g1SqCoeff := -((1 : ℚ) / 2) }
  | Pt.p1, Pt.star =>
      { constCoeff := 0
        g0Coeff := 0
        g1Coeff := 0
        f0Coeff := 0
        f1Coeff := 1
        g0SqCoeff := 0
        g0g1Coeff := 0
        g1SqCoeff := -((1 : ℚ) / 2) }
  | Pt.p1, Pt.p0 =>
      { constCoeff := 0
        g0Coeff := 0
        g1Coeff := 0
        f0Coeff := -1
        f1Coeff := 1
        g0SqCoeff := (1 : ℚ) / 2
        g0g1Coeff := 1
        g1SqCoeff := -((1 : ℚ) / 2) }
  | Pt.p1, Pt.p1 => QuadPolyQ.zero

/-- The symbolic rational polynomial agrees with the executable rational slack. -/
@[simp] theorem evalQ_slackPolyQ
    (d : OneStepDataQ) (i j : Pt) :
    (slackPolyQ i j).evalQ d = slackQ d i j := by
  cases i <;> cases j <;>
    simp [slackPolyQ, QuadPolyQ.zero, QuadPolyQ.evalQ,
      slackQ, xQ, gradQ, valQ] <;>
    ring

/-- The same symbolic rational polynomial agrees with the main real slack. -/
@[simp] theorem evalR_slackPolyQ
    (d : OneStepData) (i j : Pt) :
    (slackPolyQ i j).evalR d = slack d i j := by
  cases i <;> cases j <;>
    simp [slackPolyQ, QuadPolyQ.zero, QuadPolyQ.evalR,
      slack, x, grad, val] <;>
    ring

/-- An affine form in the two free gradient variables. -/
structure GradAffineQ where
  constCoeff : ℚ
  g0Coeff : ℚ
  g1Coeff : ℚ
  deriving DecidableEq, Repr

namespace GradAffineQ

/-- Rational evaluation of an affine gradient form. -/
def evalQ (a : GradAffineQ) (d : OneStepDataQ) : ℚ :=
  a.constCoeff + a.g0Coeff * d.g0 + a.g1Coeff * d.g1

/-- Real evaluation of an affine form with exact rational coefficients. -/
noncomputable def evalR (a : GradAffineQ) (d : OneStepData) : ℝ :=
  (a.constCoeff : ℝ) + (a.g0Coeff : ℝ) * d.g0 + (a.g1Coeff : ℝ) * d.g1

/-- Expand the square of an affine form in the fixed quadratic basis. -/
def squarePoly (a : GradAffineQ) : QuadPolyQ :=
  { constCoeff := a.constCoeff^2
    g0Coeff := 2 * a.constCoeff * a.g0Coeff
    g1Coeff := 2 * a.constCoeff * a.g1Coeff
    f0Coeff := 0
    f1Coeff := 0
    g0SqCoeff := a.g0Coeff^2
    g0g1Coeff := 2 * a.g0Coeff * a.g1Coeff
    g1SqCoeff := a.g1Coeff^2 }

@[simp] theorem evalQ_squarePoly (a : GradAffineQ) (d : OneStepDataQ) :
    a.squarePoly.evalQ d = (a.evalQ d)^2 := by
  simp [squarePoly, QuadPolyQ.evalQ, evalQ]
  ring

@[simp] theorem evalR_squarePoly (a : GradAffineQ) (d : OneStepData) :
    a.squarePoly.evalR d = (a.evalR d)^2 := by
  simp [squarePoly, QuadPolyQ.evalR, evalR]
  ring

end GradAffineQ

/-- One nonnegative multiplier attached to an interpolation inequality. -/
structure InterpTermQ where
  weight : ℚ
  i : Pt
  j : Pt
  deriving DecidableEq, Repr

/-- One nonnegative weighted square in the certificate remainder. -/
structure SquareTermQ where
  weight : ℚ
  form : GradAffineQ
  deriving DecidableEq, Repr

/-- A data-level exact upper certificate. -/
structure OneStepUpperCertQ where
  bound : ℚ
  interpTerms : List InterpTermQ
  squareTerms : List SquareTermQ
  deriving DecidableEq, Repr

/-- Sum the symbolic interpolation part of a certificate. -/
def interpPolySumQ : List InterpTermQ → QuadPolyQ
  | [] => QuadPolyQ.zero
  | t :: ts =>
      QuadPolyQ.add
        (QuadPolyQ.scale t.weight (slackPolyQ t.i t.j))
        (interpPolySumQ ts)

/-- Sum the symbolic square part of a certificate. -/
def squarePolySumQ : List SquareTermQ → QuadPolyQ
  | [] => QuadPolyQ.zero
  | t :: ts =>
      QuadPolyQ.add
        (QuadPolyQ.scale t.weight t.form.squarePoly)
        (squarePolySumQ ts)

/-- Complete right-hand-side polynomial represented by a certificate. -/
def certificateRhsPolyQ (c : OneStepUpperCertQ) : QuadPolyQ :=
  QuadPolyQ.add (interpPolySumQ c.interpTerms) (squarePolySumQ c.squareTerms)

/-- Symbolic target polynomial `bound - f1`. -/
def upperTargetPolyQ (bound : ℚ) : QuadPolyQ :=
  { constCoeff := bound
    g0Coeff := 0
    g1Coeff := 0
    f0Coeff := 0
    f1Coeff := -1
    g0SqCoeff := 0
    g0g1Coeff := 0
    g1SqCoeff := 0 }

/-- Coefficient mismatch reported by the audit layer. -/
def upperCertDifferenceQ (c : OneStepUpperCertQ) : QuadPolyQ :=
  QuadPolyQ.sub (upperTargetPolyQ c.bound) (certificateRhsPolyQ c)

/-- Numerical real value of all weighted interpolation terms. -/
noncomputable def interpTermsValueR
    (d : OneStepData) : List InterpTermQ → ℝ
  | [] => 0
  | t :: ts =>
      (t.weight : ℝ) * slack d t.i t.j + interpTermsValueR d ts

/-- Numerical real value of all weighted square terms. -/
noncomputable def squareTermsValueR
    (d : OneStepData) : List SquareTermQ → ℝ
  | [] => 0
  | t :: ts =>
      (t.weight : ℝ) * (t.form.evalR d)^2 + squareTermsValueR d ts

@[simp] theorem evalR_interpPolySumQ
    (d : OneStepData) (terms : List InterpTermQ) :
    (interpPolySumQ terms).evalR d = interpTermsValueR d terms := by
  induction terms with
  | nil =>
      simp [interpPolySumQ, interpTermsValueR]
  | cons t ts ih =>
      simp [interpPolySumQ, interpTermsValueR, ih]

@[simp] theorem evalR_squarePolySumQ
    (d : OneStepData) (terms : List SquareTermQ) :
    (squarePolySumQ terms).evalR d = squareTermsValueR d terms := by
  induction terms with
  | nil =>
      simp [squarePolySumQ, squareTermsValueR]
  | cons t ts ih =>
      simp [squarePolySumQ, squareTermsValueR, ih]

@[simp] theorem evalR_certificateRhsPolyQ
    (d : OneStepData) (c : OneStepUpperCertQ) :
    (certificateRhsPolyQ c).evalR d =
      interpTermsValueR d c.interpTerms + squareTermsValueR d c.squareTerms := by
  simp [certificateRhsPolyQ]

@[simp] theorem evalR_upperTargetPolyQ
    (d : OneStepData) (bound : ℚ) :
    (upperTargetPolyQ bound).evalR d = (bound : ℝ) - d.f1 := by
  simp [upperTargetPolyQ, QuadPolyQ.evalR]
  ring

/-- The centered form `g0 - 1/3`. -/
def centeredG0Q : GradAffineQ :=
  { constCoeff := -((1 : ℚ) / 3), g0Coeff := 1, g1Coeff := 0 }

/-- The centered form `g1 - 1/3`. -/
def centeredG1Q : GradAffineQ :=
  { constCoeff := -((1 : ℚ) / 3), g0Coeff := 0, g1Coeff := 1 }

/-- The centered form `(g0 - 1/3) + (g1 - 1/3)`. -/
def centeredSumQ : GradAffineQ :=
  { constCoeff := -((2 : ℚ) / 3), g0Coeff := 1, g1Coeff := 1 }

/-- The exact data-level certificate for the upper bound `1 / 6`. -/
def exactUpperCertQ : OneStepUpperCertQ :=
  { bound := (1 : ℚ) / 6
    interpTerms :=
      [ { weight := (1 : ℚ) / 2, i := Pt.star, j := Pt.p1 }
      , { weight := (1 : ℚ) / 2, i := Pt.star, j := Pt.p0 }
      , { weight := (1 : ℚ) / 2, i := Pt.p0, j := Pt.p1 } ]
    squareTerms :=
      [ { weight := (1 : ℚ) / 4, form := centeredG0Q }
      , { weight := (1 : ℚ) / 4, form := centeredG1Q }
      , { weight := (1 : ℚ) / 4, form := centeredSumQ } ] }

/-- An algebraically unchanged certificate containing a negative interpolation
multiplier.  The appended `-1` and `+1` copies cancel exactly, so only the
nonnegativity condition fails. -/
def negativeInterpUpperCertQ : OneStepUpperCertQ :=
  { exactUpperCertQ with
    interpTerms := exactUpperCertQ.interpTerms ++
      [ { weight := -1, i := Pt.star, j := Pt.p1 }
      , { weight := 1, i := Pt.star, j := Pt.p1 } ] }

/-- An algebraically unchanged certificate containing a negative square weight. -/
def negativeSquareUpperCertQ : OneStepUpperCertQ :=
  { exactUpperCertQ with
    squareTerms := exactUpperCertQ.squareTerms ++
      [ { weight := -1, form := centeredG0Q }
      , { weight := 1, form := centeredG0Q } ] }

/-- A certificate with nonnegative weights but the wrong claimed bound. -/
def wrongBoundUpperCertQ : OneStepUpperCertQ :=
  { exactUpperCertQ with bound := (1 : ℚ) / 5 }

end OneStep
end Toy
end LeanPEP
