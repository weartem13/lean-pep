import LeanPEP.Toy.FiniteGD.UpperCertificateChecker

/-!
# Generic upper-certificate instances for `N = 1` and `N = 2`

The same certificate data type and Boolean checker validate both exact finite
PEP upper bounds:

* `N = 1`: `f₁ ≤ 1/6`;
* `N = 2`: `f₂ ≤ 1/10`.

The file also supplies deliberately invalid certificates for each rejection
path of the generic audit layer.
-/

namespace LeanPEP
namespace Toy
namespace FiniteGD

/-- Centered gradient variable `g_i - center`. -/
def centeredGradQ
    {N : ℕ} (i : Fin (N + 1)) (center : ℚ) : GradAffineQ N :=
  GradAffineQ.sub
    (GradAffineQ.basis i)
    (GradAffineQ.const N center)

/-- The optimum in the generic one-step point type. -/
def oneStar : Point 1 := Point.star

/-- Initial point in the generic one-step point type. -/
def oneP0 : Point 1 := Point.iter 0

/-- Final point in the generic one-step point type. -/
def oneP1 : Point 1 := Point.iter 1

/-- `g₀ - 1/3`. -/
def oneCenteredG0Q : GradAffineQ 1 :=
  centeredGradQ 0 ((1 : ℚ) / 3)

/-- `g₁ - 1/3`. -/
def oneCenteredG1Q : GradAffineQ 1 :=
  centeredGradQ 1 ((1 : ℚ) / 3)

/-- `(g₀ - 1/3) + (g₁ - 1/3)`. -/
def oneCenteredSumQ : GradAffineQ 1 :=
  GradAffineQ.add oneCenteredG0Q oneCenteredG1Q

/-- Generic data-level upper certificate for the exact one-step value `1/6`. -/
def oneStepUpperCertQ : UpperCertQ 1 :=
  { bound := (1 : ℚ) / 6
    objective := 1
    interpTerms :=
      [ { weight := (1 : ℚ) / 2, i := oneStar, j := oneP1 }
      , { weight := (1 : ℚ) / 2, i := oneStar, j := oneP0 }
      , { weight := (1 : ℚ) / 2, i := oneP0, j := oneP1 } ]
    squareTerms :=
      [ { weight := (1 : ℚ) / 4, form := oneCenteredG0Q }
      , { weight := (1 : ℚ) / 4, form := oneCenteredG1Q }
      , { weight := (1 : ℚ) / 4, form := oneCenteredSumQ } ] }

/-- The generic checker accepts the exact one-step upper certificate. -/
theorem oneStepUpperCertQ_check :
    checkUpperCertQ oneStepUpperCertQ = true := by
  native_decide

/-- The generic accepted certificate proves the real one-step bound. -/
theorem oneStep_upper_from_generic_certificate
    (d : DataR 1)
    (h : Feasible d) :
    d.value 1 ≤ (1 : ℝ) / 6 := by
  simpa [oneStepUpperCertQ] using
    checkUpperCertQ_sound_real
      oneStepUpperCertQ oneStepUpperCertQ_check d h

/-- The optimum in the generic two-step point type. -/
def twoStar : Point 2 := Point.star

/-- Initial iterate in the generic two-step point type. -/
def twoP0 : Point 2 := Point.iter 0

/-- First iterate in the generic two-step point type. -/
def twoP1 : Point 2 := Point.iter 1

/-- Second iterate in the generic two-step point type. -/
def twoP2 : Point 2 := Point.iter 2

/-- Centered two-step gradient variables. -/
def twoA : GradAffineQ 2 := centeredGradQ 0 ((1 : ℚ) / 5)
def twoB : GradAffineQ 2 := centeredGradQ 1 ((1 : ℚ) / 5)
def twoC : GradAffineQ 2 := centeredGradQ 2 ((1 : ℚ) / 5)

/-- `b + (1/4)c + (5/16)a`. -/
def twoSquareForm1Q : GradAffineQ 2 :=
  GradAffineQ.add
    (GradAffineQ.add
      twoB
      (GradAffineQ.scale ((1 : ℚ) / 4) twoC))
    (GradAffineQ.scale ((5 : ℚ) / 16) twoA)

/-- `c + (1/4)a`. -/
def twoSquareForm2Q : GradAffineQ 2 :=
  GradAffineQ.add
    twoC
    (GradAffineQ.scale ((1 : ℚ) / 4) twoA)

/-- Generic data-level upper certificate for the exact two-step value `1/10`. -/
def twoStepUpperCertQ : UpperCertQ 2 :=
  { bound := (1 : ℚ) / 10
    objective := 2
    interpTerms :=
      [ { weight := (1 : ℚ) / 4, i := twoStar, j := twoP0 }
      , { weight := (1 : ℚ) / 4, i := twoP0, j := twoP1 }
      , { weight := (1 : ℚ) / 4, i := twoP1, j := twoP2 }
      , { weight := (5 : ℚ) / 12, i := twoStar, j := twoP1 }
      , { weight := (5 : ℚ) / 12, i := twoP1, j := twoP2 }
      , { weight := (1 : ℚ) / 3, i := twoStar, j := twoP2 } ]
    squareTerms :=
      [ { weight := (2 : ℚ) / 3, form := twoSquareForm1Q }
      , { weight := (11 : ℚ) / 24, form := twoSquareForm2Q }
      , { weight := (5 : ℚ) / 32, form := twoA } ] }

/-- The generic checker accepts the exact two-step upper certificate. -/
theorem twoStepUpperCertQ_check :
    checkUpperCertQ twoStepUpperCertQ = true := by
  native_decide

/-- The generic accepted certificate proves the real two-step bound. -/
theorem twoStep_upper_from_generic_certificate
    (d : DataR 2)
    (h : Feasible d) :
    d.value 2 ≤ (1 : ℝ) / 10 := by
  simpa [twoStepUpperCertQ] using
    checkUpperCertQ_sound_real
      twoStepUpperCertQ twoStepUpperCertQ_check d h

/-- Algebraically unchanged one-step certificate containing a negative
interpolation multiplier. -/
def badNegativeInterpUpperCertQ : UpperCertQ 1 :=
  { oneStepUpperCertQ with
    interpTerms := oneStepUpperCertQ.interpTerms ++
      [ { weight := -1, i := oneStar, j := oneP1 }
      , { weight := 1, i := oneStar, j := oneP1 } ] }

/-- Algebraically unchanged two-step certificate containing a negative square
weight. -/
def badNegativeSquareUpperCertQ : UpperCertQ 2 :=
  { twoStepUpperCertQ with
    squareTerms := twoStepUpperCertQ.squareTerms ++
      [ { weight := -1, form := twoA }
      , { weight := 1, form := twoA } ] }

/-- Two-step certificate with nonnegative weights but the wrong claimed bound. -/
def badWrongBoundUpperCertQ : UpperCertQ 2 :=
  { twoStepUpperCertQ with bound := (1 : ℚ) / 9 }

/-- The negative-interpolation certificate is rejected. -/
theorem badNegativeInterpUpperCertQ_check :
    checkUpperCertQ badNegativeInterpUpperCertQ = false := by
  native_decide

/-- The negative-square certificate is rejected. -/
theorem badNegativeSquareUpperCertQ_check :
    checkUpperCertQ badNegativeSquareUpperCertQ = false := by
  native_decide

/-- The wrong-bound certificate is rejected by exact coefficient comparison. -/
theorem badWrongBoundUpperCertQ_check :
    checkUpperCertQ badWrongBoundUpperCertQ = false := by
  native_decide

end FiniteGD
end Toy
end LeanPEP
