import LeanPEP.Profiles

open LeanPEP
open LeanPEP.Toy.FiniteGD
open LeanPEP.Toy.FiniteGD.ParametricUpper
open LeanPEP.GramPEP

#check LeanPEP.Profiles.GradientDescentGramCertificate.relativeValueCoeffQ
#check LeanPEP.Profiles.GradientDescentGramCertificate.homogenizedGramCoeffQ
#check LeanPEP.Profiles.GradientDescentGramCertificate.homogenizeQuadPolyQ
#check LeanPEP.Profiles.GradientDescentGramCertificate.homogenizeQuadPolyQ_zero
#check LeanPEP.Profiles.GradientDescentGramCertificate.homogenizeQuadPolyQ_add
#check LeanPEP.Profiles.GradientDescentGramCertificate.homogenizeQuadPolyQ_sub
#check LeanPEP.Profiles.GradientDescentGramCertificate.homogenizeQuadPolyQ_scale
#check LeanPEP.Profiles.GradientDescentGramCertificate.homogenizeQuadPolyQ_valueVar
#check LeanPEP.Profiles.GradientDescentGramCertificate.homogenizeQuadPolyQ_mulAffine
#check LeanPEP.Profiles.GradientDescentGramCertificate.homogenizeQuadPolyQ_square
#check LeanPEP.Profiles.GradientDescentGramCertificate.homogenizeQuadPolyQ_constAffine
#check LeanPEP.Profiles.GradientDescentGramCertificate.affineVecQ_gradAffineQ
#check LeanPEP.Profiles.GradientDescentGramCertificate.relativePointValueExprQ
#check LeanPEP.Profiles.GradientDescentGramCertificate.homogenizePointValuePolyQ
#check LeanPEP.Profiles.GradientDescentGramCertificate.relativePointValueExprQ_sub
#check LeanPEP.Profiles.GradientDescentGramCertificate.homogenizeSlackPolyQ_unitGD
#check LeanPEP.Profiles.GradientDescentGramCertificate.gramInterpTermQ
#check LeanPEP.Profiles.GradientDescentGramCertificate.homogenizeInterpPolySumQ_unitGD
#check LeanPEP.Profiles.GradientDescentGramCertificate.gramSquareFactorQ
#check LeanPEP.Profiles.GradientDescentGramCertificate.gramPairingExpr_weightedOuterQ
#check LeanPEP.Profiles.GradientDescentGramCertificate.homogenizeSquarePolySumQ
#check LeanPEP.Profiles.GradientDescentGramCertificate.homogenizeCertificateRhsPolyQ_unitGD
#check LeanPEP.Profiles.GradientDescentGramCertificate.gdGramDualFactorsQ
#check LeanPEP.Profiles.GradientDescentGramCertificate.gdGramDualMatrixQ
#check LeanPEP.Profiles.GradientDescentGramCertificate.gdGramDualFactorCertQ
#check LeanPEP.Profiles.GradientDescentGramCertificate.unitGDRadiusAssumptionIndexQ
#check LeanPEP.Profiles.GradientDescentGramCertificate.unitGDRadiusAssumption_get
#check LeanPEP.Profiles.GradientDescentGramCertificate.gdGramAssumptionTermsQ
#check LeanPEP.Profiles.GradientDescentGramCertificate.gdGramAssumptionExprSumQ
#check LeanPEP.Profiles.GradientDescentGramCertificate.gdGramUpperCertQ
#check LeanPEP.Profiles.GradientDescentGramCertificate.gdGramInterpWeights_nonneg
#check LeanPEP.Profiles.GradientDescentGramCertificate.gdGramDualWeights_nonneg
#check LeanPEP.Profiles.GradientDescentGramCertificate.gdGramAssumptionWeights_nonneg
#check LeanPEP.Profiles.GradientDescentGramCertificate.gdGramDualValidQ
#check LeanPEP.Profiles.GradientDescentGramCertificate.gdGramCertificateRhsExprQ
#check LeanPEP.Profiles.GradientDescentGramCertificate.gdGramUpperTargetDecompositionQ
#check LeanPEP.Profiles.GradientDescentGramCertificate.gdGramUpperCertQ_identity_all
#check LeanPEP.Profiles.GradientDescentGramCertificate.gdGramUpperCertQ_valid_all
#check LeanPEP.Profiles.GradientDescentGramCertificate.gdGramUpperCertQ_check_all
#check LeanPEP.Profiles.GradientDescentGramCertificate.gdGram_upper_all

example (N : ℕ) :
    LeanPEP.GramPEP.checkUpperCertQ
      (LeanPEP.Profiles.GradientDescentGramCertificate.gdGramUpperCertQ N) =
        true := by
  exact
    LeanPEP.Profiles.GradientDescentGramCertificate.gdGramUpperCertQ_check_all N

example :
    LeanPEP.GramPEP.checkUpperCertQ
      (LeanPEP.Profiles.GradientDescentGramCertificate.gdGramUpperCertQ 0) =
        true := by
  exact
    LeanPEP.Profiles.GradientDescentGramCertificate.gdGramUpperCertQ_check_all 0

example :
    LeanPEP.GramPEP.checkUpperCertQ
      (LeanPEP.Profiles.GradientDescentGramCertificate.gdGramUpperCertQ 4) =
        true := by
  exact
    LeanPEP.Profiles.GradientDescentGramCertificate.gdGramUpperCertQ_check_all 4

example :
    LeanPEP.GramPEP.checkUpperCertQ
      (LeanPEP.Profiles.GradientDescentGramCertificate.gdGramUpperCertQ 8) =
        true := by
  exact
    LeanPEP.Profiles.GradientDescentGramCertificate.gdGramUpperCertQ_check_all 8
