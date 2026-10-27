import LeanPEP.Profiles.ProximalGradientCertificateFlow
import LeanPEP.GramPEP.CoefficientAlgebra

/-!
# A local, exact coefficient identity for each proximal-gradient edge

The potential is rho_i = (T-i)/(2T-i)^2, with rho_0=1/(4T)
and rho_T=0.  No limiting argument or division by T-i is used.
This file proves an equality of full Gram coefficient objects for arbitrary
vectors, not just an equality at the lower witness or on PSD matrices.
-/

namespace LeanPEP.Profiles.ProximalGradientCertificate

open LeanPEP.GramPEP
open LeanPEP.GramPEP.CoefficientAlgebra
open scoped BigOperators

def potentialQ (n k : ℕ) : ℚ :=
  (((n : ℚ) + 1) - k) / (2 * ((n : ℚ) + 1) - k) ^ 2

@[simp] theorem potentialQ_zero (n : ℕ) : potentialQ n 0 = boundQ n := by
  have hn : (0 : ℚ) < (n : ℚ) + 1 := by positivity
  simp only [potentialQ, Nat.cast_zero, sub_zero, boundQ]
  field_simp [ne_of_gt hn] <;> ring

@[simp] theorem potentialQ_last (n : ℕ) : potentialQ n (n + 1) = 0 := by
  simp [potentialQ]

/-- All six coefficients of the local quadratic identity, including the
potential diagonal terms, are consequences of the UNCHANGED C3A formulas. -/
theorem local_weight_identities (n : ℕ) (i : Fin (n + 1)) :
    mixedWeightQ n i - nodeFluxQ n i.val = potentialQ n i.val ∧
    mixedWeightQ n i * mixedRatioQ n i ^ 2 - nodeFluxQ n (i.val + 1) =
      -potentialQ n (i.val + 1) ∧
    2 * mixedWeightQ n i * mixedRatioQ n i =
      nodeFluxQ n i.val + nodeFluxQ n (i.val + 1) ∧
    2 * mixedWeightQ n i * mixedGradientQ n i = smoothChainWeightQ n i ∧
    2 * mixedWeightQ n i * mixedRatioQ n i * mixedGradientQ n i =
      nodeFluxQ n (i.val + 1) ∧
    mixedWeightQ n i * mixedGradientQ n i ^ 2 + gradientDifferenceWeightQ n i =
      smoothChainWeightQ n i / 2 := by
  -- Keep denominators atomic until all inverses have been cleared.  Their
  -- defining polynomials are substituted only in the resulting ring goals.
  have algebra (T j d e P : ℚ)
      (hd0 : d ≠ 0) (he0 : e ≠ 0) (hP0 : P ≠ 0)
      (hd_def : d = 2 * T - j) (he_def : e = d - 1)
      (hP_def : P = T + j * e) :
      P / d ^ 2 - j / d = (T - j) / d ^ 2 ∧
      P / d ^ 2 * (d / e) ^ 2 - (j + 1) / e = -((T - j - 1) / e ^ 2) ∧
      2 * (P / d ^ 2) * (d / e) = j / d + (j + 1) / e ∧
      2 * (P / d ^ 2) * (((j + 1) * d) / (2 * P)) = (j + 1) / d ∧
      2 * (P / d ^ 2) * (d / e) * (((j + 1) * d) / (2 * P)) = (j + 1) / e ∧
      P / d ^ 2 * (((j + 1) * d) / (2 * P)) ^ 2 +
          (j * (j + 1) * e) / (4 * P * d) = ((j + 1) / d) / 2 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      field_simp [hd0, he0, hP0] <;>
      (subst P; subst e; subst d; ring)
  have hd := edge_den_pos n i
  have hd' : (0 : ℚ) < 2 * ((n : ℚ) + 1) - i.val := by linarith
  have hp := pivotNumeratorQ_pos n i
  have h := algebra ((n : ℚ) + 1) (i.val : ℚ)
    (2 * ((n : ℚ) + 1) - i.val)
    (2 * ((n : ℚ) + 1) - i.val - 1)
    (pivotNumeratorQ n i)
    (ne_of_gt hd') (ne_of_gt hd) (ne_of_gt hp) rfl rfl rfl
  simpa only [mixedWeightQ, mixedRatioQ, mixedGradientQ, gradientDifferenceWeightQ,
    smoothChainWeightQ, nodeFluxQ, potentialQ, pivotNumeratorQ,
    Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub] using h

/-- Scalar diagonal form of the local identity, with unrestricted scalar data.
The residual used in this identity is exactly X-Y-G. -/
theorem local_scalar_identity (n : ℕ) (i : Fin (n + 1)) (X Y G H : ℚ) :
    mixedWeightQ n i * (X - mixedRatioQ n i * Y - mixedGradientQ n i * (G - H)) ^ 2 +
      gradientDifferenceWeightQ n i * (G - H) ^ 2 +
      smoothChainWeightQ n i * ((G - H) * X - (1/2 : ℚ) * (G - H) ^ 2) +
      nodeFluxQ n (i.val + 1) * (X - Y - G) * Y -
      nodeFluxQ n i.val * (X - Y - G) * X =
    potentialQ n i.val * X ^ 2 - potentialQ n (i.val + 1) * Y ^ 2 +
      nodeFluxQ n i.val * G * X - nodeFluxQ n (i.val + 1) * H * Y := by
  rcases local_weight_identities n i with ⟨hX, hY, hXY, hG, hH, hD⟩
  linear_combination X^2 * hX + Y^2 * hY - (X*Y) * hXY -
    (X*(G-H)) * hG + (Y*(G-H)) * hH + (G-H)^2 * hD

/-- Polarization proves ALL exact matrix entries, including off-diagonals.
This equality is stronger than evaluation on a particular feasible Gram datum. -/
theorem local_gram_identity {p m : ℕ} (n : ℕ) (i : Fin (n + 1))
    (X Y G H : VecExpr m ℚ) :
    mixedWeightQ n i • normSquare (p := p)
        (X - mixedRatioQ n i • Y - mixedGradientQ n i • (G - H)) +
      gradientDifferenceWeightQ n i • normSquare (G - H) +
      smoothChainWeightQ n i • (bilinear (G - H) X - (1/2 : ℚ) • normSquare (G - H)) +
      nodeFluxQ n (i.val + 1) • bilinear (X - Y - G) Y -
      nodeFluxQ n i.val • bilinear (X - Y - G) X =
    potentialQ n i.val • normSquare X - potentialQ n (i.val + 1) • normSquare Y +
      nodeFluxQ n i.val • bilinear G X - nodeFluxQ n (i.val + 1) • bilinear H Y := by
  apply coeff_ext
  · simp [normSquare, bilinear, coefficients, LinearExprQ.gramBilinear,
      LinearExprQ.scale, LinearExprQ.add, LinearExprQ.gramOuter]
  · intro k
    simp [normSquare, bilinear, coefficients, LinearExprQ.gramBilinear,
      LinearExprQ.scale, LinearExprQ.add, LinearExprQ.gramOuter]
  · intro r s
    have hsum := local_scalar_identity n i (X r + X s) (Y r + Y s) (G r + G s) (H r + H s)
    have hr := local_scalar_identity n i (X r) (Y r) (G r) (H r)
    have hs := local_scalar_identity n i (X s) (Y s) (G s) (H s)
    dsimp [normSquare, bilinear, coefficients, LinearExprQ.gramBilinear,
      LinearExprQ.scale, LinearExprQ.add, LinearExprQ.gramOuter]
    linear_combination (1/2 : ℚ) * hsum - (1/2 : ℚ) * hr - (1/2 : ℚ) * hs

/-- Finite telescoping needs neither positivity nor nonzero endpoint values. -/
theorem fin_telescope {M : Type*} [AddCommGroup M] (k : ℕ) (z : Fin (k + 1) → M) :
    (∑ i : Fin k, (z i.castSucc - z i.succ)) = z 0 - z (Fin.last k) := by
  have hleft := Fin.sum_univ_castSucc z
  have hright := Fin.sum_univ_succ z
  rw [Finset.sum_sub_distrib]
  have h : (∑ i : Fin k, z i.castSucc) + z (Fin.last k) =
      z 0 + ∑ i : Fin k, z i.succ := hleft.symm.trans hright
  exact sub_eq_sub_iff_add_eq_add.mpr (by simpa [add_comm] using h)

end LeanPEP.Profiles.ProximalGradientCertificate
