import LeanPEP.Toy.OneStep.UpperCertificate

/-!
# Executable checker and soundness theorem for exact upper certificates

The checker verifies three independent obligations:

1. every interpolation multiplier is nonnegative;
2. every square weight is nonnegative;
3. the certificate polynomial equals `bound - f1` coefficient by coefficient.

Its soundness theorem applies an accepted rational certificate to arbitrary real
finite PEP data.  Thus the executable exact check is connected to the main
mathematical semantics rather than merely testing a rational sample.
-/

namespace LeanPEP
namespace Toy
namespace OneStep

/-- Proposition-level meaning of a valid exact upper certificate. -/
structure UpperCertValidQ (c : OneStepUpperCertQ) : Prop where
  interpWeights : ∀ t ∈ c.interpTerms, 0 ≤ t.weight
  squareWeights : ∀ t ∈ c.squareTerms, 0 ≤ t.weight
  identity : certificateRhsPolyQ c = upperTargetPolyQ c.bound

/-- Executably check nonnegative weights and the exact polynomial identity. -/
def checkUpperCertQ (c : OneStepUpperCertQ) : Bool :=
  c.interpTerms.all (fun t => decide (0 ≤ t.weight)) &&
    (c.squareTerms.all (fun t => decide (0 ≤ t.weight)) &&
      decide (certificateRhsPolyQ c = upperTargetPolyQ c.bound))

/-- A successful Boolean upper-certificate check has the proposition-level
meaning stated by `UpperCertValidQ`. -/
theorem checkUpperCertQ_sound
    (c : OneStepUpperCertQ)
    (h : checkUpperCertQ c = true) :
    UpperCertValidQ c := by
  have hparts :
      (∀ t ∈ c.interpTerms, 0 ≤ t.weight) ∧
      (∀ t ∈ c.squareTerms, 0 ≤ t.weight) ∧
      certificateRhsPolyQ c = upperTargetPolyQ c.bound := by
    simpa [checkUpperCertQ] using h
  exact
    { interpWeights := hparts.1
      squareWeights := hparts.2.1
      identity := hparts.2.2 }

/-- Every propositionally valid exact upper certificate is accepted. -/
theorem checkUpperCertQ_complete
    (c : OneStepUpperCertQ)
    (h : UpperCertValidQ c) :
    checkUpperCertQ c = true := by
  have hinterp :
      c.interpTerms.all (fun t => decide (0 ≤ t.weight)) = true := by
    apply List.all_eq_true.mpr
    intro t ht
    simpa using h.interpWeights t ht
  have hsquare :
      c.squareTerms.all (fun t => decide (0 ≤ t.weight)) = true := by
    apply List.all_eq_true.mpr
    intro t ht
    simpa using h.squareWeights t ht
  simp [checkUpperCertQ, hinterp, hsquare, h.identity]

/-- The Boolean checker exactly decides proposition-level certificate validity. -/
theorem checkUpperCertQ_eq_true_iff
    (c : OneStepUpperCertQ) :
    checkUpperCertQ c = true ↔ UpperCertValidQ c := by
  constructor
  · exact checkUpperCertQ_sound c
  · exact checkUpperCertQ_complete c

/-- A nonnegative weighted sum of feasible interpolation slacks is nonnegative. -/
theorem interpTermsValueR_nonneg
    (d : OneStepData)
    (hd : OneStepFeasible d)
    (terms : List InterpTermQ)
    (hweights : ∀ t ∈ terms, 0 ≤ t.weight) :
    0 ≤ interpTermsValueR d terms := by
  revert hweights
  induction terms with
  | nil =>
      intro hweights
      simp [interpTermsValueR]
  | cons t ts ih =>
      intro hweights
      have hweightQ : 0 ≤ t.weight := hweights t (by simp)
      have hweightR : 0 ≤ (t.weight : ℝ) := Rat.cast_nonneg.mpr hweightQ
      have hslack : 0 ≤ slack d t.i t.j := hd.interp t.i t.j
      have htailWeights : ∀ u ∈ ts, 0 ≤ u.weight := by
        intro u hu
        exact hweights u (by simp [hu])
      have htail : 0 ≤ interpTermsValueR d ts := ih htailWeights
      simp only [interpTermsValueR]
      exact add_nonneg (mul_nonneg hweightR hslack) htail

/-- A nonnegative weighted sum of exact squares is nonnegative. -/
theorem squareTermsValueR_nonneg
    (d : OneStepData)
    (terms : List SquareTermQ)
    (hweights : ∀ t ∈ terms, 0 ≤ t.weight) :
    0 ≤ squareTermsValueR d terms := by
  revert hweights
  induction terms with
  | nil =>
      intro hweights
      simp [squareTermsValueR]
  | cons t ts ih =>
      intro hweights
      have hweightQ : 0 ≤ t.weight := hweights t (by simp)
      have hweightR : 0 ≤ (t.weight : ℝ) := Rat.cast_nonneg.mpr hweightQ
      have hsquare : 0 ≤ (t.form.evalR d)^2 := sq_nonneg (t.form.evalR d)
      have htailWeights : ∀ u ∈ ts, 0 ≤ u.weight := by
        intro u hu
        exact hweights u (by simp [hu])
      have htail : 0 ≤ squareTermsValueR d ts := ih htailWeights
      simp only [squareTermsValueR]
      exact add_nonneg (mul_nonneg hweightR hsquare) htail

/-- A valid rational upper certificate proves its bound for every real feasible
one-step datum. -/
theorem upperCertValidQ_sound_real
    (c : OneStepUpperCertQ)
    (hc : UpperCertValidQ c)
    (d : OneStepData)
    (hd : OneStepFeasible d) :
    d.f1 ≤ (c.bound : ℝ) := by
  have hinterp : 0 ≤ interpTermsValueR d c.interpTerms :=
    interpTermsValueR_nonneg d hd c.interpTerms hc.interpWeights
  have hsquares : 0 ≤ squareTermsValueR d c.squareTerms :=
    squareTermsValueR_nonneg d c.squareTerms hc.squareWeights
  have htotal :
      0 ≤ interpTermsValueR d c.interpTerms +
        squareTermsValueR d c.squareTerms :=
    add_nonneg hinterp hsquares
  have hidentity :
      (c.bound : ℝ) - d.f1 =
        interpTermsValueR d c.interpTerms +
          squareTermsValueR d c.squareTerms := by
    simpa using
      (congrArg (fun p : QuadPolyQ => p.evalR d) hc.identity).symm
  nlinarith

/-- An accepted executable upper certificate proves its claimed real bound. -/
theorem checkUpperCertQ_sound_real
    (c : OneStepUpperCertQ)
    (h : checkUpperCertQ c = true)
    (d : OneStepData)
    (hd : OneStepFeasible d) :
    d.f1 ≤ (c.bound : ℝ) :=
  upperCertValidQ_sound_real c (checkUpperCertQ_sound c h) d hd

/-- Scan interpolation terms for the first negative multiplier. -/
def firstNegativeInterpTermQ : List InterpTermQ → Option InterpTermQ
  | [] => none
  | t :: ts =>
      if t.weight < 0 then some t else firstNegativeInterpTermQ ts

/-- Scan square terms for the first negative weight. -/
def firstNegativeSquareTermQ : List SquareTermQ → Option SquareTermQ
  | [] => none
  | t :: ts =>
      if t.weight < 0 then some t else firstNegativeSquareTermQ ts

/-- Reasons for exact upper-certificate rejection. -/
inductive UpperCertFailureQ where
  | negativeInterpWeight (term : InterpTermQ)
  | negativeSquareWeight (term : SquareTermQ)
  | identityMismatch (difference : QuadPolyQ)
  deriving DecidableEq, Repr

/-- Human-readable executable audit result. -/
inductive UpperCertAuditQ where
  | accepted
  | rejected (failure : UpperCertFailureQ)
  deriving DecidableEq, Repr

/-- Return the first nonnegativity failure, otherwise return the exact coefficient
mismatch, or accept when all three obligations hold. -/
def auditUpperCertQ (c : OneStepUpperCertQ) : UpperCertAuditQ :=
  match firstNegativeInterpTermQ c.interpTerms with
  | some t => .rejected (.negativeInterpWeight t)
  | none =>
      match firstNegativeSquareTermQ c.squareTerms with
      | some t => .rejected (.negativeSquareWeight t)
      | none =>
          if certificateRhsPolyQ c = upperTargetPolyQ c.bound then
            .accepted
          else
            .rejected (.identityMismatch (upperCertDifferenceQ c))

/-- Every interpolation term returned by the negative-weight scanner is a list
member with a strictly negative weight. -/
theorem firstNegativeInterpTermQ_some_sound
    (terms : List InterpTermQ)
    (t : InterpTermQ)
    (h : firstNegativeInterpTermQ terms = some t) :
    t ∈ terms ∧ t.weight < 0 := by
  induction terms with
  | nil =>
      simp [firstNegativeInterpTermQ] at h
  | cons u us ih =>
      by_cases hu : u.weight < 0
      · have hut : u = t := by
          simpa [firstNegativeInterpTermQ, hu] using h
        subst t
        exact ⟨by simp, hu⟩
      · have hrest : firstNegativeInterpTermQ us = some t := by
          simpa [firstNegativeInterpTermQ, hu] using h
        rcases ih hrest with ⟨hmem, hneg⟩
        exact ⟨by simp [hmem], hneg⟩

/-- Every square term returned by the negative-weight scanner is a list member
with a strictly negative weight. -/
theorem firstNegativeSquareTermQ_some_sound
    (terms : List SquareTermQ)
    (t : SquareTermQ)
    (h : firstNegativeSquareTermQ terms = some t) :
    t ∈ terms ∧ t.weight < 0 := by
  induction terms with
  | nil =>
      simp [firstNegativeSquareTermQ] at h
  | cons u us ih =>
      by_cases hu : u.weight < 0
      · have hut : u = t := by
          simpa [firstNegativeSquareTermQ, hu] using h
        subst t
        exact ⟨by simp, hu⟩
      · have hrest : firstNegativeSquareTermQ us = some t := by
          simpa [firstNegativeSquareTermQ, hu] using h
        rcases ih hrest with ⟨hmem, hneg⟩
        exact ⟨by simp [hmem], hneg⟩

/-- The interpolation scanner returns `none` exactly when every multiplier is
nonnegative. -/
theorem firstNegativeInterpTermQ_eq_none_iff
    (terms : List InterpTermQ) :
    firstNegativeInterpTermQ terms = none ↔
      ∀ t ∈ terms, 0 ≤ t.weight := by
  induction terms with
  | nil =>
      simp [firstNegativeInterpTermQ]
  | cons t ts ih =>
      by_cases hneg : t.weight < 0
      · have hnot : ¬ 0 ≤ t.weight := not_le_of_gt hneg
        simp [firstNegativeInterpTermQ, hneg, hnot]
      · have hnonneg : 0 ≤ t.weight := le_of_not_gt hneg
        simp [firstNegativeInterpTermQ, hneg, hnonneg, ih]

/-- The square scanner returns `none` exactly when every square weight is
nonnegative. -/
theorem firstNegativeSquareTermQ_eq_none_iff
    (terms : List SquareTermQ) :
    firstNegativeSquareTermQ terms = none ↔
      ∀ t ∈ terms, 0 ≤ t.weight := by
  induction terms with
  | nil =>
      simp [firstNegativeSquareTermQ]
  | cons t ts ih =>
      by_cases hneg : t.weight < 0
      · have hnot : ¬ 0 ≤ t.weight := not_le_of_gt hneg
        simp [firstNegativeSquareTermQ, hneg, hnot]
      · have hnonneg : 0 ≤ t.weight := le_of_not_gt hneg
        simp [firstNegativeSquareTermQ, hneg, hnonneg, ih]

/-- An accepted audit report is equivalent to proposition-level upper-certificate
validity. -/
theorem auditUpperCertQ_accepted_iff
    (c : OneStepUpperCertQ) :
    auditUpperCertQ c = .accepted ↔ UpperCertValidQ c := by
  constructor
  · intro h
    cases hinterp : firstNegativeInterpTermQ c.interpTerms with
    | some t =>
        simp [auditUpperCertQ, hinterp] at h
    | none =>
        cases hsquare : firstNegativeSquareTermQ c.squareTerms with
        | some t =>
            simp [auditUpperCertQ, hinterp, hsquare] at h
        | none =>
            by_cases hidentity :
                certificateRhsPolyQ c = upperTargetPolyQ c.bound
            · exact
                { interpWeights :=
                    (firstNegativeInterpTermQ_eq_none_iff c.interpTerms).mp hinterp
                  squareWeights :=
                    (firstNegativeSquareTermQ_eq_none_iff c.squareTerms).mp hsquare
                  identity := hidentity }
            · simp [auditUpperCertQ, hinterp, hsquare, hidentity] at h
  · intro h
    have hinterp : firstNegativeInterpTermQ c.interpTerms = none :=
      (firstNegativeInterpTermQ_eq_none_iff c.interpTerms).mpr h.interpWeights
    have hsquare : firstNegativeSquareTermQ c.squareTerms = none :=
      (firstNegativeSquareTermQ_eq_none_iff c.squareTerms).mpr h.squareWeights
    simp [auditUpperCertQ, hinterp, hsquare, h.identity]

/-- The executable audit accepts exactly the certificates accepted by the
Boolean checker. -/
theorem auditUpperCertQ_accepted_iff_check
    (c : OneStepUpperCertQ) :
    auditUpperCertQ c = .accepted ↔ checkUpperCertQ c = true := by
  exact (auditUpperCertQ_accepted_iff c).trans
    (checkUpperCertQ_eq_true_iff c).symm

/-- The exact certificate is accepted by exact computation. -/
theorem exactUpperCertQ_check :
    checkUpperCertQ exactUpperCertQ = true := by
  native_decide

/-- The exact certificate's claimed bound is exactly `1 / 6`. -/
theorem exactUpperCertQ_bound :
    exactUpperCertQ.bound = (1 : ℚ) / 6 := by
  norm_num [exactUpperCertQ]

/-- The accepted data-level certificate independently reconstructs the main
real upper bound. -/
theorem oneStep_upper_from_exact_certificate
    (d : OneStepData)
    (h : OneStepFeasible d) :
    d.f1 ≤ (1 : ℝ) / 6 := by
  have hbound :=
    checkUpperCertQ_sound_real exactUpperCertQ exactUpperCertQ_check d h
  simpa [exactUpperCertQ] using hbound

/-- The exact upper certificate receives an accepted audit report. -/
theorem exactUpperCertQ_audit :
    auditUpperCertQ exactUpperCertQ = .accepted := by
  native_decide

/-- A negative interpolation multiplier is rejected before identity checking. -/
theorem negativeInterpUpperCertQ_audit :
    auditUpperCertQ negativeInterpUpperCertQ =
      .rejected
        (.negativeInterpWeight
          { weight := -1, i := Pt.star, j := Pt.p1 }) := by
  native_decide

/-- A negative square weight is rejected before identity checking. -/
theorem negativeSquareUpperCertQ_audit :
    auditUpperCertQ negativeSquareUpperCertQ =
      .rejected
        (.negativeSquareWeight
          { weight := -1, form := centeredG0Q }) := by
  native_decide

/-- The wrong claimed bound is rejected with the exact residual polynomial
`1 / 30`. -/
theorem wrongBoundUpperCertQ_audit :
    auditUpperCertQ wrongBoundUpperCertQ =
      .rejected
        (.identityMismatch (QuadPolyQ.constant ((1 : ℚ) / 30))) := by
  native_decide

/-- Each intentionally invalid upper certificate fails the Boolean checker. -/
theorem negativeInterpUpperCertQ_check :
    checkUpperCertQ negativeInterpUpperCertQ = false := by
  native_decide

theorem negativeSquareUpperCertQ_check :
    checkUpperCertQ negativeSquareUpperCertQ = false := by
  native_decide

theorem wrongBoundUpperCertQ_check :
    checkUpperCertQ wrongBoundUpperCertQ = false := by
  native_decide

end OneStep
end Toy
end LeanPEP
