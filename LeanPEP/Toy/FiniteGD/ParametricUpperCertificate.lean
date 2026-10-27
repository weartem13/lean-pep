import LeanPEP.Toy.FiniteGD.UpperCertificateChecker

/-!
# Closed-form gradient-descent upper-certificate generator

This module is the first arbitrary-trajectory-length slice of the normalized
finite-GD upper-bound development.  It defines, for every `N`, the exact
rational interpolation multipliers and affine-square factors suggested by the
closed form `1 / (4 * N + 2)`.

The interpolation multipliers are generated from the cumulative flow

`c_k = (k + 1) / (2 * N - k)` for `k < N`.

The star-to-iterate weights are the successive increments of this flow, with
`c_N = 1`; the consecutive-iterate weight at step `k` is `c_k`.  The exact SOS
remainder is a reverse-order LDL factorization centered at the constant
sampled gradient `1 / (2 * N + 1)`.

The constructor is fully parameterized and is consumed by the existing generic
`UpperCertQ` checker.  This slice kernel-checks concrete generated certificates
for `N = 0, ..., 8`.  A subsequent slice must prove checker acceptance for all
`N`; the finite regression sweep below is not itself that universal theorem.
-/

namespace LeanPEP
namespace Toy
namespace FiniteGD
namespace ParametricUpper

/-- The constant gradient of the conjectured exact finite witness. -/
def gdCenterQ (N : ℕ) : ℚ :=
  (1 : ℚ) / (((2 * N + 1 : ℕ) : ℚ))

/-- The target normalized upper bound `1 / (4N + 2)`. -/
def gdBoundQ (N : ℕ) : ℚ :=
  (1 : ℚ) / (((4 * N + 2 : ℕ) : ℚ))

/-- The final sampled function-value index. -/
def gdObjective (N : ℕ) : Fin (N + 1) :=
  ⟨N, by omega⟩

/-- Cumulative interpolation-flow weight on the consecutive pair `(k,k+1)`. -/
def gdChainWeightQ (N : ℕ) (k : Fin N) : ℚ :=
  (((k.val + 1 : ℕ) : ℚ)) /
    (((2 * N - k.val : ℕ) : ℚ))

/-- Star-to-iterate interpolation weight.

For `k < N` this is

`(2N+1) / ((2N-k)(2N-k+1))`,

and the final star weight is `1/(N+1)`. -/
def gdStarWeightQ (N : ℕ) (k : Fin (N + 1)) : ℚ :=
  if k.val = N then
    (1 : ℚ) / (((N + 1 : ℕ) : ℚ))
  else
    (((2 * N + 1 : ℕ) : ℚ)) /
      ((((2 * N - k.val : ℕ) : ℚ)) *
        (((2 * N - k.val + 1 : ℕ) : ℚ)))

/-- `g_k - 1/(2N+1)`. -/
def gdCenteredGradQ (N : ℕ) (k : Fin (N + 1)) : GradAffineQ N :=
  GradAffineQ.sub
    (GradAffineQ.basis k)
    (GradAffineQ.const N (gdCenterQ N))

/-- Sum of the first `k` centered sampled gradients. -/
def gdCenteredPrefixQ (N : ℕ) (k : Fin (N + 1)) : GradAffineQ N :=
  GradAffineQ.sub
    (GradAffineQ.prefixAffine k.val (by omega))
    (GradAffineQ.const N (((k.val : ℕ) : ℚ) * gdCenterQ N))

/-- Closed-form affine factor in the reverse-order LDL decomposition.

The factor at `k` is

`(g_k-q) + (1/(2N-k+1)) * sum_{r<k} (g_r-q)`,

where `q = 1/(2N+1)`. -/
def gdSquareFormQ (N : ℕ) (k : Fin (N + 1)) : GradAffineQ N :=
  GradAffineQ.add
    (gdCenteredGradQ N k)
    (GradAffineQ.scale
      ((1 : ℚ) / (((2 * N - k.val + 1 : ℕ) : ℚ)))
      (gdCenteredPrefixQ N k))

/-- Nonnegative diagonal weight in the reverse-order LDL decomposition. -/
def gdSquareWeightQ (N : ℕ) (k : Fin (N + 1)) : ℚ :=
  if k.val = N then
    (1 : ℚ) / 2
  else
    let t : ℕ := 2 * N - k.val
    (((2 * k.val * t + 2 * N + 1 : ℕ) : ℚ)) /
      (2 * (((t : ℕ) : ℚ)) ^ 2)

/-- All star-to-iterate interpolation terms. -/
def gdStarTermsQ (N : ℕ) : List (InterpTermQ N) :=
  (List.finRange (N + 1)).map (fun k =>
    { weight := gdStarWeightQ N k
      i := Point.star
      j := Point.iter k })

/-- All consecutive-iterate interpolation terms. -/
def gdChainTermsQ (N : ℕ) : List (InterpTermQ N) :=
  (List.finRange N).map (fun k =>
    { weight := gdChainWeightQ N k
      i := Point.iter ⟨k.val, by omega⟩
      j := Point.iter ⟨k.val + 1, by omega⟩ })

/-- Complete closed-form interpolation term list. -/
def gdInterpTermsQ (N : ℕ) : List (InterpTermQ N) :=
  gdStarTermsQ N ++ gdChainTermsQ N

/-- Complete closed-form affine-square term list. -/
def gdSquareTermsQ (N : ℕ) : List (SquareTermQ N) :=
  (List.finRange (N + 1)).map (fun k =>
    { weight := gdSquareWeightQ N k
      form := gdSquareFormQ N k })

/-- Closed-form normalized finite-GD upper-certificate candidate. -/
def gdUpperCertQ (N : ℕ) : UpperCertQ N :=
  { bound := gdBoundQ N
    objective := gdObjective N
    interpTerms := gdInterpTermsQ N
    squareTerms := gdSquareTermsQ N }

/-- Any concrete acceptance proof for the generated certificate yields the
corresponding real finite-PEP upper bound. -/
theorem gd_upper_of_check
    (N : ℕ)
    (hcheck : checkUpperCertQ (gdUpperCertQ N) = true)
    (d : DataR N)
    (hfeasible : Feasible d) :
    d.value (gdObjective N) ≤ (gdBoundQ N : ℝ) := by
  simpa [gdUpperCertQ] using
    checkUpperCertQ_sound_real
      (gdUpperCertQ N) hcheck d hfeasible

/-- Exact generated-certificate regressions. -/
theorem gdUpperCertQ_check_0 :
    checkUpperCertQ (gdUpperCertQ 0) = true := by
  native_decide

theorem gdUpperCertQ_check_1 :
    checkUpperCertQ (gdUpperCertQ 1) = true := by
  native_decide

theorem gdUpperCertQ_check_2 :
    checkUpperCertQ (gdUpperCertQ 2) = true := by
  native_decide

theorem gdUpperCertQ_check_3 :
    checkUpperCertQ (gdUpperCertQ 3) = true := by
  native_decide

theorem gdUpperCertQ_check_4 :
    checkUpperCertQ (gdUpperCertQ 4) = true := by
  native_decide

theorem gdUpperCertQ_check_5 :
    checkUpperCertQ (gdUpperCertQ 5) = true := by
  native_decide

theorem gdUpperCertQ_check_6 :
    checkUpperCertQ (gdUpperCertQ 6) = true := by
  native_decide

theorem gdUpperCertQ_check_7 :
    checkUpperCertQ (gdUpperCertQ 7) = true := by
  native_decide

theorem gdUpperCertQ_check_8 :
    checkUpperCertQ (gdUpperCertQ 8) = true := by
  native_decide

end ParametricUpper
end FiniteGD
end Toy
end LeanPEP
