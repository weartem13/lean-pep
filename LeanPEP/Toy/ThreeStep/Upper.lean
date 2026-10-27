import LeanPEP.Toy.ThreeStep.Data
import LeanPEP.Toy.FiniteGD.UpperCertificateChecker

/-!
# Exact generic upper certificate for the normalized three-step finite PEP

The interpolation multipliers satisfy the function-value flow equations, and
the remaining affine quadratic polynomial is represented by four exact rational
squares.  The generic executable checker verifies every sign and every
coefficient of the identity.
-/

namespace LeanPEP
namespace Toy
namespace ThreeStep

/-- Centered gradient variable `g_i - 1/7`. -/
def centeredGradQ (i : Fin 4) : FiniteGD.GradAffineQ 3 :=
  FiniteGD.GradAffineQ.sub
    (FiniteGD.GradAffineQ.basis i)
    (FiniteGD.GradAffineQ.const 3 ((1 : ℚ) / 7))

/-- Centered gradient variables. -/
def aQ : FiniteGD.GradAffineQ 3 := centeredGradQ 0
def bQ : FiniteGD.GradAffineQ 3 := centeredGradQ 1
def cQ : FiniteGD.GradAffineQ 3 := centeredGradQ 2
def dQ : FiniteGD.GradAffineQ 3 := centeredGradQ 3

/-- First affine factor in the exact LDL/SOS remainder. -/
def squareForm0Q : FiniteGD.GradAffineQ 3 :=
  FiniteGD.GradAffineQ.add
    (FiniteGD.GradAffineQ.add
      aQ
      (FiniteGD.GradAffineQ.scale ((7 : ℚ) / 5) bQ))
    (FiniteGD.GradAffineQ.add
      (FiniteGD.GradAffineQ.scale ((21 : ℚ) / 10) cQ)
      (FiniteGD.GradAffineQ.scale ((3 : ℚ) / 2) dQ))

/-- Second affine factor in the exact LDL/SOS remainder. -/
def squareForm1Q : FiniteGD.GradAffineQ 3 :=
  FiniteGD.GradAffineQ.add
    (FiniteGD.GradAffineQ.add
      aQ
      (FiniteGD.GradAffineQ.scale (-((7 : ℚ) / 25)) bQ))
    (FiniteGD.GradAffineQ.add
      (FiniteGD.GradAffineQ.scale (-((21 : ℚ) / 50)) cQ)
      (FiniteGD.GradAffineQ.scale (-((3 : ℚ) / 10)) dQ))

/-- Third affine factor in the exact LDL/SOS remainder. -/
def squareForm2Q : FiniteGD.GradAffineQ 3 :=
  FiniteGD.GradAffineQ.add
    bQ
    (FiniteGD.GradAffineQ.add
      (FiniteGD.GradAffineQ.scale (-((7 : ℚ) / 12)) cQ)
      (FiniteGD.GradAffineQ.scale (-((5 : ℚ) / 12)) dQ))

/-- Fourth affine factor in the exact LDL/SOS remainder. -/
def squareForm3Q : FiniteGD.GradAffineQ 3 :=
  FiniteGD.GradAffineQ.sub cQ dQ

/-- Generic data-level upper certificate for the exact three-step value `1/14`.

The star-to-iterate multipliers are
`1/6, 7/30, 7/20, 1/4`.  Their cumulative sums give the consecutive-iterate
multipliers `1/6, 2/5, 3/4`, which exactly cancel all function-value
coefficients except the target coefficient `-f₃`.
-/
def threeStepUpperCertQ : FiniteGD.UpperCertQ 3 :=
  { bound := (1 : ℚ) / 14
    objective := 3
    interpTerms :=
      [ { weight := (1 : ℚ) / 6, i := star, j := p0 }
      , { weight := (7 : ℚ) / 30, i := star, j := p1 }
      , { weight := (7 : ℚ) / 20, i := star, j := p2 }
      , { weight := (1 : ℚ) / 4, i := star, j := p3 }
      , { weight := (1 : ℚ) / 6, i := p0, j := p1 }
      , { weight := (2 : ℚ) / 5, i := p1, j := p2 }
      , { weight := (3 : ℚ) / 4, i := p2, j := p3 } ]
    squareTerms :=
      [ { weight := (7 : ℚ) / 72, form := squareForm0Q }
      , { weight := (5 : ℚ) / 72, form := squareForm1Q }
      , { weight := (51 : ℚ) / 250, form := squareForm2Q }
      , { weight := (23 : ℚ) / 96, form := squareForm3Q } ] }

/-- The generic checker accepts the exact three-step upper certificate. -/
theorem threeStepUpperCertQ_check :
    FiniteGD.checkUpperCertQ threeStepUpperCertQ = true := by
  native_decide

/-- Every feasible normalized three-step finite PEP datum satisfies
`f₃ ≤ 1 / 14`. -/
theorem threeStep_upper
    (d : ThreeStepData)
    (h : FiniteGD.Feasible d) :
    d.value 3 ≤ (1 : ℝ) / 14 := by
  simpa [threeStepUpperCertQ] using
    FiniteGD.checkUpperCertQ_sound_real
      threeStepUpperCertQ threeStepUpperCertQ_check d h

end ThreeStep
end Toy
end LeanPEP
