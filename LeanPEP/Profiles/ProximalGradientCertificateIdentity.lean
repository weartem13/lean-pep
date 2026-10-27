import LeanPEP.Profiles.ProximalGradientCertificateIndexing
import LeanPEP.Profiles.ProximalGradientCertificateTelescoping

/-!
# Arbitrary-positive-horizon identity for the unchanged C3A certificate

The proof reads the actual row-major constraints, cancels the component-local
value flows, and sums the local full-coefficient identities. All operations
are exact rational operations on the old LinearExprQ fields. No feasibility,
PSD, witness values, small-horizon enumeration, or external computation is
used to establish the symbolic identity.
-/

namespace LeanPEP.Profiles.ProximalGradientCertificate

open LeanPEP.GramPEP
open LeanPEP.GramPEP.CoefficientAlgebra
open LeanPEP.Profiles.ProximalGradient
open scoped BigOperators

private abbrev C (n : ℕ) := CoefficientsQ (valueCount n) (basisCount n)
private def fStar (n : ℕ) : C n := coefficients (LinearExprQ.valueVar (smoothValueIndex 0))
private def hStar (n : ℕ) : C n := coefficients (LinearExprQ.valueVar (nonsmoothValueIndex 0))
private def fValue (n : ℕ) (i : Fin (n + 2)) : C n :=
  coefficients (LinearExprQ.valueVar (smoothValueIndex i.succ))
private def hValue (n : ℕ) (i : Fin (n + 1)) : C n :=
  coefficients (LinearExprQ.valueVar (nonsmoothValueIndex i.succ))

private def smoothStarBody (n : ℕ) (i : Fin (n + 2)) : C n :=
  fStar n - fValue n i + bilinear (gradientVecQ i) (positionVecQ n i.val) -
    (1/2 : ℚ) • normSquare (gradientVecQ i - starGradientQ n)
private def smoothChainBody (n : ℕ) (i : Fin (n + 1)) : C n :=
  fValue n i.castSucc - fValue n i.succ -
    bilinear (gradientVecQ i.succ) (positionVecQ n i.val - positionVecQ n (i.val + 1)) -
    (1/2 : ℚ) • normSquare (gradientVecQ i.castSucc - gradientVecQ i.succ)
private def nonsmoothStarBody (n : ℕ) (i : Fin (n + 1)) : C n :=
  hStar n - hValue n i + bilinear (residualVecQ i) (positionVecQ n (i.val + 1))
private def nonsmoothChainBody (n : ℕ) (i : Fin n) : C n :=
  hValue n i.castSucc - hValue n i.succ -
    bilinear (residualVecQ i.succ)
      (positionVecQ n (i.val + 1) - positionVecQ n (i.val + 1 + 1))

private def smoothStarSum (n : ℕ) : C n :=
  ∑ i : Fin (n + 2), smoothStarWeightQ n i • smoothStarBody n i
private def smoothChainSum (n : ℕ) : C n :=
  ∑ i : Fin (n + 1), smoothChainWeightQ n i • smoothChainBody n i
private def nonsmoothStarSum (n : ℕ) : C n :=
  ∑ i : Fin (n + 1), nonsmoothStarWeightQ n i • nonsmoothStarBody n i
private def nonsmoothChainSum (n : ℕ) : C n :=
  ∑ i : Fin n, nonsmoothChainWeightQ n i • nonsmoothChainBody n i
private def mixedSquares (n : ℕ) : C n :=
  ∑ i : Fin (n + 1), mixedWeightQ n i • normSquare (mixedFactorQ n i).vector
private def starSquares (n : ℕ) : C n :=
  ∑ i : Fin (n + 2), (smoothStarWeightQ n i / 2) •
    normSquare (gradientVecQ i - starGradientQ n)
private def differenceSquares (n : ℕ) : C n :=
  ∑ i : Fin (n + 1), gradientDifferenceWeightQ n i •
    normSquare (gradientVecQ i.castSucc - gradientVecQ i.succ)
private def radiusPart (n : ℕ) : C n :=
  boundQ n • (coefficients (LinearExprQ.const _ _ 1) - normSquare (initialVecQ n))

private theorem smoothStarBody_eq (n : ℕ) (i : Fin (n + 2)) :
    coefficients (Composite.interpolationExprQ .oneSmoothConvex
      (smoothSamplesQ n 0) (smoothSamplesQ n i.succ)) = smoothStarBody n i := by
  simp only [Composite.interpolationExprQ, smoothSamplesQ, Fin.cases_zero, Fin.cases_succ,
    coefficients_sub, coefficients_scale, coefficients_gramBilinear, coefficients_gramNorm,
    zero_sub, bilinear_neg_right, sub_neg_eq_add,
    normSquare_sub_comm (starGradientQ n), smoothStarBody, fStar, fValue]

private theorem smoothChainBody_eq (n : ℕ) (i : Fin (n + 1)) :
    coefficients (Composite.interpolationExprQ .oneSmoothConvex
      (smoothSamplesQ n i.castSucc.succ) (smoothSamplesQ n i.succ.succ)) =
      smoothChainBody n i := by
  simp only [Composite.interpolationExprQ, smoothSamplesQ, Fin.cases_succ,
    coefficients_sub, coefficients_scale, coefficients_gramBilinear, coefficients_gramNorm,
    smoothChainBody, fValue, Fin.val_castSucc, Fin.val_succ]

private theorem nonsmoothStarBody_eq (n : ℕ) (i : Fin (n + 1)) :
    coefficients (Composite.interpolationExprQ .convex
      (nonsmoothSamplesQ n 0) (nonsmoothSamplesQ n i.succ)) = nonsmoothStarBody n i := by
  simp only [Composite.interpolationExprQ, nonsmoothSamplesQ, Fin.cases_zero, Fin.cases_succ,
    coefficients_sub, coefficients_gramBilinear, zero_sub, bilinear_neg_right,
    sub_neg_eq_add, nonsmoothStarBody, hStar, hValue]

private theorem nonsmoothChainBody_eq (n : ℕ) (i : Fin n) :
    coefficients (Composite.interpolationExprQ .convex
      (nonsmoothSamplesQ n i.castSucc.succ) (nonsmoothSamplesQ n i.succ.succ)) =
      nonsmoothChainBody n i := by
  simp only [Composite.interpolationExprQ, nonsmoothSamplesQ, Fin.cases_succ,
    coefficients_sub, coefficients_gramBilinear, nonsmoothChainBody, hValue,
    Fin.val_castSucc, Fin.val_succ]

/-- Expand the ACTUAL certificate, using proved bounded list lookups. -/
private theorem rhs_coefficients (n : ℕ) :
    coefficients (certificateRhsExprQ (upperCertQ n)) =
      smoothStarSum n + smoothChainSum n + nonsmoothStarSum n + nonsmoothChainSum n +
        radiusPart n + mixedSquares n + starSquares n + differenceSquares n := by
  simp only [upperCertQ, certificateRhsExprQ, interpExprSumQ, coefficients_add,
    coefficients_zero, zero_add, coefficients_assumptionExprSumQ, coefficients_factorGramQ,
    assumptionTermsQ, dualFactorsQ, List.map_append, List.sum_append, List.map_map,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  -- Introduce the bound Fin index before simplifying composed term functions.
  simp only [← Fin.sum_univ_def]
  simp only [Function.comp_apply, smoothStarTermQ, smoothChainTermQ,
    nonsmoothStarTermQ, nonsmoothChainTermQ, smoothIndex_get, nonsmoothIndex_get,
    radiusIndex_get, smoothStarBody_eq, smoothChainBody_eq, nonsmoothStarBody_eq,
    nonsmoothChainBody_eq, radiusExprQ, coefficients_sub, coefficients_gramNorm,
    starGradientFactorQ, gradientDifferenceFactorQ]
  -- List.sum_append preserves left-associated block sums; change must do so too.
  change (smoothStarSum n + smoothChainSum n + nonsmoothStarSum n +
      nonsmoothChainSum n + radiusPart n) +
      (mixedSquares n + starSquares n + differenceSquares n) = _
  abel

private def smoothCross (n : ℕ) : C n :=
  ∑ i : Fin (n + 1), smoothChainWeightQ n i •
    (bilinear (gradientVecQ i.castSucc - gradientVecQ i.succ) (positionVecQ n i.val) -
      (1/2 : ℚ) • normSquare (gradientVecQ i.castSucc - gradientVecQ i.succ))
private def nonsmoothEdges (n : ℕ) : C n :=
  ∑ i : Fin (n + 1),
    (nodeFluxQ n (i.val + 1) • bilinear (residualVecQ i) (positionVecQ n (i.val + 1)) -
      nodeFluxQ n i.val • bilinear (residualVecQ i) (positionVecQ n i.val))
private def endPair (n : ℕ) : C n :=
  bilinear (gradientVecQ (Fin.last (n + 1))) (positionVecQ n (n + 1))

private theorem smooth_balance (n : ℕ) :
    smoothStarSum n + smoothChainSum n + starSquares n =
      fStar n - fValue n (Fin.last (n + 1)) + endPair n + smoothCross n := by
  have hb := smooth_component_balance n (fValue n)
    (fun i : Fin (n + 2) => (bilinear (gradientVecQ i) (positionVecQ n i.val) : C n))
    (fun i : Fin (n + 2) => (normSquare (gradientVecQ i - starGradientQ n) : C n))
    (fun i : Fin (n + 1) => (bilinear (gradientVecQ i.succ)
      (positionVecQ n i.val - positionVecQ n (i.val + 1)) : C n))
    (fun i : Fin (n + 1) => (normSquare (gradientVecQ i.castSucc - gradientVecQ i.succ) : C n))
    (fStar n)
  have hgeom (i : Fin (n + 1)) :
      (bilinear (gradientVecQ i.castSucc) (positionVecQ n i.val) : C n) -
        bilinear (gradientVecQ i.succ) (positionVecQ n (i.val + 1)) -
        bilinear (gradientVecQ i.succ) (positionVecQ n i.val - positionVecQ n (i.val + 1)) =
      bilinear (gradientVecQ i.castSucc - gradientVecQ i.succ) (positionVecQ n i.val) := by
    simp only [bilinear_sub_right, bilinear_sub_left]
    abel
  simpa only [smoothStarSum, smoothChainSum, starSquares, smoothStarBody, smoothChainBody,
    endPair, smoothCross, Fin.val_castSucc, Fin.val_succ, Fin.val_last, hgeom] using hb

private theorem nonsmooth_balance (n : ℕ) :
    nonsmoothStarSum n + nonsmoothChainSum n =
      hStar n - hValue n (Fin.last n) + nonsmoothEdges n := by
  have hb := nonsmooth_component_balance n (hValue n)
    (fun i : Fin (n + 1) => (bilinear (residualVecQ i) (positionVecQ n i.val) : C n))
    (fun i : Fin (n + 1) => (bilinear (residualVecQ i) (positionVecQ n (i.val + 1)) : C n))
    (hStar n)
  simpa only [nonsmoothStarSum, nonsmoothChainSum, nonsmoothStarBody, nonsmoothChainBody,
    nonsmoothEdges, Fin.val_castSucc, Fin.val_succ, bilinear_sub_right] using hb

/-- Local Gram identities telescope in the full coefficient module. -/
private theorem quadratic_sum (n : ℕ) :
    mixedSquares n + differenceSquares n + smoothCross n + nonsmoothEdges n =
      boundQ n • normSquare (initialVecQ n) - endPair n := by
  let P : Fin (n + 2) → C n := fun i =>
    potentialQ n i.val • normSquare (positionVecQ n i.val) +
      nodeFluxQ n i.val • bilinear (gradientVecQ i) (positionVecQ n i.val)
  have hedge (i : Fin (n + 1)) :
      mixedWeightQ n i • (normSquare (mixedFactorQ n i).vector : C n) +
        gradientDifferenceWeightQ n i • normSquare (gradientVecQ i.castSucc - gradientVecQ i.succ) +
        smoothChainWeightQ n i •
          (bilinear (gradientVecQ i.castSucc - gradientVecQ i.succ) (positionVecQ n i.val) -
            (1/2 : ℚ) • normSquare (gradientVecQ i.castSucc - gradientVecQ i.succ)) +
        (nodeFluxQ n (i.val + 1) • bilinear (residualVecQ i) (positionVecQ n (i.val + 1)) -
          nodeFluxQ n i.val • bilinear (residualVecQ i) (positionVecQ n i.val)) =
        P i.castSucc - P i.succ := by
    have hres : residualVecQ i = positionVecQ n i.val - positionVecQ n (i.val + 1) -
        gradientVecQ i.castSucc := by
      rw [positionVecQ_succ]
      abel
    have hl := local_gram_identity (p := valueCount n) n i
      (positionVecQ n i.val) (positionVecQ n (i.val + 1))
      (gradientVecQ i.castSucc) (gradientVecQ i.succ)
    rw [← hres] at hl
    dsimp only [mixedFactorQ, P, Fin.val_castSucc, Fin.val_succ]
    calc
      _ = mixedWeightQ n i • normSquare
          (positionVecQ n i.val - mixedRatioQ n i • positionVecQ n (i.val + 1) -
            mixedGradientQ n i • (gradientVecQ i.castSucc - gradientVecQ i.succ)) +
          gradientDifferenceWeightQ n i • normSquare (gradientVecQ i.castSucc - gradientVecQ i.succ) +
          smoothChainWeightQ n i •
            (bilinear (gradientVecQ i.castSucc - gradientVecQ i.succ) (positionVecQ n i.val) -
              (1/2 : ℚ) • normSquare (gradientVecQ i.castSucc - gradientVecQ i.succ)) +
          nodeFluxQ n (i.val + 1) • bilinear (residualVecQ i) (positionVecQ n (i.val + 1)) -
          nodeFluxQ n i.val • bilinear (residualVecQ i) (positionVecQ n i.val) := by abel
      _ = _ := hl
      _ = _ := by abel
  calc
    _ = ∑ i : Fin (n + 1),
        (mixedWeightQ n i • (normSquare (mixedFactorQ n i).vector : C n) +
          gradientDifferenceWeightQ n i • normSquare (gradientVecQ i.castSucc - gradientVecQ i.succ) +
          smoothChainWeightQ n i •
            (bilinear (gradientVecQ i.castSucc - gradientVecQ i.succ) (positionVecQ n i.val) -
              (1/2 : ℚ) • normSquare (gradientVecQ i.castSucc - gradientVecQ i.succ)) +
          (nodeFluxQ n (i.val + 1) • bilinear (residualVecQ i) (positionVecQ n (i.val + 1)) -
            nodeFluxQ n i.val • bilinear (residualVecQ i) (positionVecQ n i.val))) := by
      simp only [mixedSquares, differenceSquares, smoothCross, nonsmoothEdges,
        Finset.sum_add_distrib]
    _ = ∑ i : Fin (n + 1), (P i.castSucc - P i.succ) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hedge i
    _ = P 0 - P (Fin.last (n + 1)) := fin_telescope (n + 1) P
    _ = _ := by
      simp only [P, Fin.val_zero, Fin.val_last, potentialQ_zero, potentialQ_last,
        nodeFluxQ_zero, nodeFluxQ_last, positionVecQ_zero, zero_smul, one_smul,
        add_zero, zero_add, endPair]

private theorem target_coefficients (n : ℕ) :
    coefficients (upperTargetExprQ (boundQ n) (objectiveQ n)) =
      boundQ n • coefficients (LinearExprQ.const _ _ 1) +
        (fStar n - fValue n (Fin.last (n + 1))) + (hStar n - hValue n (Fin.last n)) := by
  have hc : coefficients (LinearExprQ.const (valueCount n) (basisCount n) (boundQ n)) =
      boundQ n • coefficients (LinearExprQ.const _ _ 1) := by
    apply coeff_ext <;> intros <;> simp [coefficients, LinearExprQ.const, smul_eq_mul]
  simp only [upperTargetExprQ, objectiveQ, coefficients_sub, coefficients_add, hc,
    fStar, fValue, hStar, hValue, Fin.succ_last]
  abel

/-- The entire original C3A coefficient identity, for EVERY n : Nat. -/
theorem certificateIdentityQ_all (n : ℕ) : CertificateIdentityQ n := by
  apply coefficients_injective
  rw [rhs_coefficients, target_coefficients]
  calc
    _ = (smoothStarSum n + smoothChainSum n + starSquares n) +
        (nonsmoothStarSum n + nonsmoothChainSum n) + radiusPart n +
        mixedSquares n + differenceSquares n := by abel
    _ = (fStar n - fValue n (Fin.last (n + 1)) + endPair n + smoothCross n) +
        (hStar n - hValue n (Fin.last n) + nonsmoothEdges n) + radiusPart n +
        mixedSquares n + differenceSquares n := by rw [smooth_balance, nonsmooth_balance]
    _ = (fStar n - fValue n (Fin.last (n + 1))) + (hStar n - hValue n (Fin.last n)) +
        radiusPart n + endPair n +
        (mixedSquares n + differenceSquares n + smoothCross n + nonsmoothEdges n) := by abel
    _ = _ := by
      rw [quadratic_sum]
      simp only [radiusPart, smul_sub]
      abel

/-- Full original-checker acceptance; no horizon bound or identity premise remains. -/
theorem upperCertQ_check_all (n : ℕ) : checkUpperCertQ (upperCertQ n) = true :=
  (upperCertQ_check_iff_identity n).mpr (certificateIdentityQ_all n)

/-- Proposition-level validity of the same certificate, with no new checker. -/
theorem upperCertQ_valid_all (n : ℕ) : UpperCertValidQ (upperCertQ n) :=
  checkUpperCertQ_sound _ (upperCertQ_check_all n)

end LeanPEP.Profiles.ProximalGradientCertificate
