import LeanPEP.Toy.FiniteGD.UpperCertificate

/-!
# Generic executable upper-certificate checker

For arbitrary trajectory length `N`, the checker verifies:

1. every interpolation multiplier is nonnegative;
2. every affine-square weight is nonnegative; and
3. the parameterized quadratic-polynomial identity holds coefficient by
   coefficient.

The soundness theorem applies an accepted rational certificate to every real
finite PEP datum satisfying the generated interpolation constraints.
-/

namespace LeanPEP
namespace Toy
namespace FiniteGD

/-- Executable coefficient-by-coefficient equality for generic quadratic
polynomials. -/
def checkPolyEqQ {N : ℕ} (p q : QuadPolyQ N) : Bool :=
  decide (p.constCoeff = q.constCoeff) &&
    ((indices N).all (fun i =>
      decide (p.gradCoeff i = q.gradCoeff i)) &&
    ((indices N).all (fun i =>
      decide (p.valueCoeff i = q.valueCoeff i)) &&
    (indexPairs N).all (fun ij =>
      decide (p.quadCoeff ij.1 ij.2 = q.quadCoeff ij.1 ij.2))))

/-- A successful coefficient check proves equality of the represented
quadratic polynomials. -/
theorem checkPolyEqQ_sound
    {N : ℕ} (p q : QuadPolyQ N)
    (h : checkPolyEqQ p q = true) :
    p = q := by
  have hparts :
      p.constCoeff = q.constCoeff ∧
      (∀ i ∈ indices N, p.gradCoeff i = q.gradCoeff i) ∧
      (∀ i ∈ indices N, p.valueCoeff i = q.valueCoeff i) ∧
      (∀ ij ∈ indexPairs N,
        p.quadCoeff ij.1 ij.2 = q.quadCoeff ij.1 ij.2) := by
    simpa [checkPolyEqQ, List.all_eq_true] using h
  apply QuadPolyQ.ext
  · exact hparts.1
  · funext i
    exact hparts.2.1 i (mem_indices i)
  · funext i
    exact hparts.2.2.1 i (mem_indices i)
  · funext i j
    exact hparts.2.2.2 (i, j) (mem_indexPairs i j)

/-- Equal coefficient objects are accepted by the executable checker. -/
theorem checkPolyEqQ_complete
    {N : ℕ} (p q : QuadPolyQ N)
    (h : p = q) :
    checkPolyEqQ p q = true := by
  subst q
  simp [checkPolyEqQ]

/-- The coefficient checker exactly decides equality. -/
theorem checkPolyEqQ_eq_true_iff
    {N : ℕ} (p q : QuadPolyQ N) :
    checkPolyEqQ p q = true ↔ p = q := by
  constructor
  · exact checkPolyEqQ_sound p q
  · exact checkPolyEqQ_complete p q

/-- Proposition-level meaning of a valid generic upper certificate. -/
structure UpperCertValidQ {N : ℕ} (c : UpperCertQ N) : Prop where
  interpWeights : ∀ t ∈ c.interpTerms, 0 ≤ t.weight
  squareWeights : ∀ t ∈ c.squareTerms, 0 ≤ t.weight
  identity :
    certificateRhsPolyQ c = upperTargetPolyQ c.bound c.objective

/-- Executably check all certificate obligations. -/
def checkUpperCertQ {N : ℕ} (c : UpperCertQ N) : Bool :=
  c.interpTerms.all (fun t => decide (0 ≤ t.weight)) &&
    (c.squareTerms.all (fun t => decide (0 ≤ t.weight)) &&
      checkPolyEqQ
        (certificateRhsPolyQ c)
        (upperTargetPolyQ c.bound c.objective))

/-- Boolean acceptance has the proposition-level certificate meaning. -/
theorem checkUpperCertQ_sound
    {N : ℕ} (c : UpperCertQ N)
    (h : checkUpperCertQ c = true) :
    UpperCertValidQ c := by
  have hparts :
      (∀ t ∈ c.interpTerms, 0 ≤ t.weight) ∧
      (∀ t ∈ c.squareTerms, 0 ≤ t.weight) ∧
      checkPolyEqQ
        (certificateRhsPolyQ c)
        (upperTargetPolyQ c.bound c.objective) = true := by
    simpa [checkUpperCertQ, List.all_eq_true] using h
  exact
    { interpWeights := hparts.1
      squareWeights := hparts.2.1
      identity := checkPolyEqQ_sound _ _ hparts.2.2 }

/-- Every propositionally valid certificate is accepted. -/
theorem checkUpperCertQ_complete
    {N : ℕ} (c : UpperCertQ N)
    (h : UpperCertValidQ c) :
    checkUpperCertQ c = true := by
  have hinterp :
      c.interpTerms.all (fun t => decide (0 ≤ t.weight)) = true := by
    apply List.all_eq_true.mpr
    intro t ht
    exact decide_eq_true (h.interpWeights t ht)
  have hsquare :
      c.squareTerms.all (fun t => decide (0 ≤ t.weight)) = true := by
    apply List.all_eq_true.mpr
    intro t ht
    exact decide_eq_true (h.squareWeights t ht)
  have hidentity :
      checkPolyEqQ
        (certificateRhsPolyQ c)
        (upperTargetPolyQ c.bound c.objective) = true :=
    checkPolyEqQ_complete _ _ h.identity
  simp [checkUpperCertQ, hinterp, hsquare, hidentity]

/-- The generic Boolean checker exactly decides proposition-level validity. -/
theorem checkUpperCertQ_eq_true_iff
    {N : ℕ} (c : UpperCertQ N) :
    checkUpperCertQ c = true ↔ UpperCertValidQ c := by
  constructor
  · exact checkUpperCertQ_sound c
  · exact checkUpperCertQ_complete c

/-- A nonnegative weighted sum of feasible interpolation slacks is
nonnegative. -/
theorem interpTermsValueR_nonneg
    {N : ℕ}
    (d : DataR N)
    (hd : Feasible d)
    (terms : List (InterpTermQ N))
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
      have hweightR : 0 ≤ (t.weight : ℝ) :=
        Rat.cast_nonneg.mpr hweightQ
      have hslack : 0 ≤ slack d t.i t.j := hd t.i t.j
      have htailWeights : ∀ u ∈ ts, 0 ≤ u.weight := by
        intro u hu
        exact hweights u (by simp [hu])
      have htail : 0 ≤ interpTermsValueR d ts := ih htailWeights
      simp only [interpTermsValueR]
      exact add_nonneg (mul_nonneg hweightR hslack) htail

/-- A nonnegative weighted sum of affine squares is nonnegative. -/
theorem squareTermsValueR_nonneg
    {N : ℕ}
    (d : DataR N)
    (terms : List (SquareTermQ N))
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
      have hweightR : 0 ≤ (t.weight : ℝ) :=
        Rat.cast_nonneg.mpr hweightQ
      have hsquare : 0 ≤ (t.form.evalR d)^2 :=
        sq_nonneg (t.form.evalR d)
      have htailWeights : ∀ u ∈ ts, 0 ≤ u.weight := by
        intro u hu
        exact hweights u (by simp [hu])
      have htail : 0 ≤ squareTermsValueR d ts := ih htailWeights
      simp only [squareTermsValueR]
      exact add_nonneg (mul_nonneg hweightR hsquare) htail

/-- A valid rational certificate proves its claimed upper bound for every real
feasible finite trajectory. -/
theorem upperCertValidQ_sound_real
    {N : ℕ}
    (c : UpperCertQ N)
    (hc : UpperCertValidQ c)
    (d : DataR N)
    (hd : Feasible d) :
    d.value c.objective ≤ (c.bound : ℝ) := by
  have hinterp : 0 ≤ interpTermsValueR d c.interpTerms :=
    interpTermsValueR_nonneg d hd c.interpTerms hc.interpWeights
  have hsquares : 0 ≤ squareTermsValueR d c.squareTerms :=
    squareTermsValueR_nonneg d c.squareTerms hc.squareWeights
  have htotal :
      0 ≤ interpTermsValueR d c.interpTerms +
        squareTermsValueR d c.squareTerms :=
    add_nonneg hinterp hsquares
  have hidentity :
      (c.bound : ℝ) - d.value c.objective =
        interpTermsValueR d c.interpTerms +
          squareTermsValueR d c.squareTerms := by
    have heval := congrArg
      (fun p : QuadPolyQ N => p.evalR d) hc.identity
    simpa using heval.symm
  nlinarith

/-- An accepted executable certificate proves its claimed real upper bound. -/
theorem checkUpperCertQ_sound_real
    {N : ℕ}
    (c : UpperCertQ N)
    (h : checkUpperCertQ c = true)
    (d : DataR N)
    (hd : Feasible d) :
    d.value c.objective ≤ (c.bound : ℝ) :=
  upperCertValidQ_sound_real c (checkUpperCertQ_sound c h) d hd

/-- First interpolation term with a negative multiplier. -/
def firstNegativeInterpTermQ
    {N : ℕ} :
    List (InterpTermQ N) → Option (InterpTermQ N)
  | [] => none
  | t :: ts =>
      if t.weight < 0 then some t else firstNegativeInterpTermQ ts

/-- Diagnostic record for a negative square weight.  The form itself is not
printed because its coefficient field is a function; its list position makes
the failing input term unambiguous. -/
structure NegativeSquareWeightQ where
  index : Nat
  weight : ℚ
  deriving DecidableEq, Repr

/-- Scan square terms while retaining their list index. -/
def firstNegativeSquareWeightFromQ
    {N : ℕ} :
    Nat → List (SquareTermQ N) → Option NegativeSquareWeightQ
  | _, [] => none
  | k, t :: ts =>
      if t.weight < 0 then
        some { index := k, weight := t.weight }
      else
        firstNegativeSquareWeightFromQ (k + 1) ts

/-- First square term with a negative weight. -/
def firstNegativeSquareWeightQ
    {N : ℕ} (terms : List (SquareTermQ N)) :
    Option NegativeSquareWeightQ :=
  firstNegativeSquareWeightFromQ 0 terms

/-- Location of one quadratic-polynomial coefficient. -/
inductive CoeffLocationQ (N : ℕ) where
  | const
  | grad (i : Fin (N + 1))
  | value (i : Fin (N + 1))
  | quad (i j : Fin (N + 1))
  deriving DecidableEq, Repr

/-- One exact coefficient mismatch. -/
structure CoeffMismatchQ (N : ℕ) where
  location : CoeffLocationQ N
  expected : ℚ
  actual : ℚ
  deriving DecidableEq, Repr

/-- Return one mismatch when two rational coefficients differ. -/
def mismatchQ
    {N : ℕ}
    (location : CoeffLocationQ N)
    (expected actual : ℚ) :
    List (CoeffMismatchQ N) :=
  if expected = actual then [] else
    [{ location := location, expected := expected, actual := actual }]

/-- Complete exact coefficient mismatch report. -/
def coefficientMismatchesQ
    {N : ℕ} (expected actual : QuadPolyQ N) :
    List (CoeffMismatchQ N) :=
  mismatchQ (N := N) .const expected.constCoeff actual.constCoeff ++
    (indices N).flatMap (fun i =>
      mismatchQ (.grad i) (expected.gradCoeff i) (actual.gradCoeff i)) ++
    (indices N).flatMap (fun i =>
      mismatchQ (.value i) (expected.valueCoeff i) (actual.valueCoeff i)) ++
    (indexPairs N).flatMap (fun ij =>
      mismatchQ (.quad ij.1 ij.2)
        (expected.quadCoeff ij.1 ij.2)
        (actual.quadCoeff ij.1 ij.2))

/-- Exact rejection reasons for generic upper certificates. -/
inductive UpperCertFailureQ (N : ℕ) where
  | negativeInterpWeight (term : InterpTermQ N)
  | negativeSquareWeight (failure : NegativeSquareWeightQ)
  | identityMismatch (differences : List (CoeffMismatchQ N))
  deriving DecidableEq, Repr

/-- Executable generic upper-certificate audit result. -/
inductive UpperCertAuditQ (N : ℕ) where
  | accepted
  | rejected (failure : UpperCertFailureQ N)
  deriving DecidableEq, Repr

/-- Audit weights first, then report every exact coefficient mismatch. -/
def auditUpperCertQ
    {N : ℕ} (c : UpperCertQ N) : UpperCertAuditQ N :=
  match firstNegativeInterpTermQ c.interpTerms with
  | some t => .rejected (.negativeInterpWeight t)
  | none =>
      match firstNegativeSquareWeightQ c.squareTerms with
      | some failure => .rejected (.negativeSquareWeight failure)
      | none =>
          if checkPolyEqQ
              (certificateRhsPolyQ c)
              (upperTargetPolyQ c.bound c.objective) then
            .accepted
          else
            .rejected (.identityMismatch
              (coefficientMismatchesQ
                (upperTargetPolyQ c.bound c.objective)
                (certificateRhsPolyQ c)))

end FiniteGD
end Toy
end LeanPEP
