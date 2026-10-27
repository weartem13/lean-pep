import LeanPEP.Toy.FiniteGD.ParametricUpperCertificate

/-!
# Universal proof obligations for the closed-form finite-GD certificate

This module separates the arbitrary-`N` proof into the two obligations that
are logically present in the generic checker:

1. all generated interpolation and affine-square weights are nonnegative; and
2. the generated symbolic polynomial is exactly `bound - f_N`.

The first obligation is discharged here for every natural `N`.  Consequently,
checker acceptance for `gdUpperCertQ N` is equivalent to one exact polynomial
identity.  The remaining identity is deliberately exposed as
`gdCertificateIdentityQ N`; proving it for every `N` is the next algebraic
slice.
-/

namespace LeanPEP
namespace Toy
namespace FiniteGD
namespace ParametricUpper

/-- Every generated consecutive-pair interpolation multiplier is
nonnegative. -/
theorem gdChainWeightQ_nonneg
    (N : ℕ) (k : Fin N) :
    0 ≤ gdChainWeightQ N k := by
  unfold gdChainWeightQ
  positivity

/-- Every generated star-to-iterate interpolation multiplier is
nonnegative. -/
theorem gdStarWeightQ_nonneg
    (N : ℕ) (k : Fin (N + 1)) :
    0 ≤ gdStarWeightQ N k := by
  unfold gdStarWeightQ
  split <;> positivity

/-- Every generated diagonal SOS weight is nonnegative. -/
theorem gdSquareWeightQ_nonneg
    (N : ℕ) (k : Fin (N + 1)) :
    0 ≤ gdSquareWeightQ N k := by
  unfold gdSquareWeightQ
  split
  · norm_num
  · dsimp
    positivity

/-- All generated star interpolation terms carry nonnegative weights. -/
theorem gdStarTermsQ_weights_nonneg
    (N : ℕ) :
    ∀ t ∈ gdStarTermsQ N, 0 ≤ t.weight := by
  intro t ht
  rcases List.mem_map.mp ht with ⟨k, _hk, rfl⟩
  exact gdStarWeightQ_nonneg N k

/-- All generated consecutive interpolation terms carry nonnegative weights. -/
theorem gdChainTermsQ_weights_nonneg
    (N : ℕ) :
    ∀ t ∈ gdChainTermsQ N, 0 ≤ t.weight := by
  intro t ht
  rcases List.mem_map.mp ht with ⟨k, _hk, rfl⟩
  exact gdChainWeightQ_nonneg N k

/-- Every interpolation multiplier in the complete generated certificate is
nonnegative, uniformly in `N`. -/
theorem gdInterpTermsQ_weights_nonneg
    (N : ℕ) :
    ∀ t ∈ gdInterpTermsQ N, 0 ≤ t.weight := by
  intro t ht
  rw [gdInterpTermsQ, List.mem_append] at ht
  rcases ht with ht | ht
  · exact gdStarTermsQ_weights_nonneg N t ht
  · exact gdChainTermsQ_weights_nonneg N t ht

/-- Every SOS multiplier in the complete generated certificate is
nonnegative, uniformly in `N`. -/
theorem gdSquareTermsQ_weights_nonneg
    (N : ℕ) :
    ∀ t ∈ gdSquareTermsQ N, 0 ≤ t.weight := by
  intro t ht
  rcases List.mem_map.mp ht with ⟨k, _hk, rfl⟩
  exact gdSquareWeightQ_nonneg N k

/-- The sole remaining arbitrary-`N` certificate obligation after weight
nonnegativity: exact coefficient equality with `bound - f_N`. -/
def gdCertificateIdentityQ (N : ℕ) : Prop :=
  certificateRhsPolyQ (gdUpperCertQ N) =
    upperTargetPolyQ (gdBoundQ N) (gdObjective N)

/-- The generated certificate is propositionally valid whenever its exact
polynomial identity has been proved. -/
theorem gdUpperCertQ_valid_of_identity
    (N : ℕ)
    (hidentity : gdCertificateIdentityQ N) :
    UpperCertValidQ (gdUpperCertQ N) := by
  refine
    { interpWeights := ?_
      squareWeights := ?_
      identity := ?_ }
  · simpa [gdUpperCertQ] using gdInterpTermsQ_weights_nonneg N
  · simpa [gdUpperCertQ] using gdSquareTermsQ_weights_nonneg N
  · simpa [gdCertificateIdentityQ, gdUpperCertQ] using hidentity

/-- For the generated certificate, executable acceptance is equivalent to the
single exact polynomial identity.  All sign obligations have already been
proved for every `N`. -/
theorem gdUpperCertQ_check_eq_true_iff_identity
    (N : ℕ) :
    checkUpperCertQ (gdUpperCertQ N) = true ↔
      gdCertificateIdentityQ N := by
  rw [checkUpperCertQ_eq_true_iff]
  constructor
  · intro hvalid
    simpa [gdCertificateIdentityQ, gdUpperCertQ] using hvalid.identity
  · exact gdUpperCertQ_valid_of_identity N

/-- An exact proof of the remaining identity produces Boolean checker
acceptance. -/
theorem gdUpperCertQ_check_of_identity
    (N : ℕ)
    (hidentity : gdCertificateIdentityQ N) :
    checkUpperCertQ (gdUpperCertQ N) = true :=
  (gdUpperCertQ_check_eq_true_iff_identity N).2 hidentity

/-- The remaining identity is sufficient for the claimed real upper bound on
all feasible normalized finite-GD data. -/
theorem gd_upper_of_identity
    (N : ℕ)
    (hidentity : gdCertificateIdentityQ N)
    (d : DataR N)
    (hfeasible : Feasible d) :
    d.value (gdObjective N) ≤ (gdBoundQ N : ℝ) :=
  gd_upper_of_check N
    (gdUpperCertQ_check_of_identity N hidentity)
    d hfeasible

/-- The concrete regression proofs from v0.12B2 are compatible with the
universal identity reduction. -/
theorem gdCertificateIdentityQ_0 :
    gdCertificateIdentityQ 0 :=
  (gdUpperCertQ_check_eq_true_iff_identity 0).1 gdUpperCertQ_check_0

theorem gdCertificateIdentityQ_4 :
    gdCertificateIdentityQ 4 :=
  (gdUpperCertQ_check_eq_true_iff_identity 4).1 gdUpperCertQ_check_4

theorem gdCertificateIdentityQ_8 :
    gdCertificateIdentityQ 8 :=
  (gdUpperCertQ_check_eq_true_iff_identity 8).1 gdUpperCertQ_check_8

end ParametricUpper
end FiniteGD
end Toy
end LeanPEP
