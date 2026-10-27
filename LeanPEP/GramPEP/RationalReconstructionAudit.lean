import LeanPEP.GramPEP.ExternalBundle

/-! Exact endpoint auditing for an untrusted rational reconstruction proposal.
The source model is a shared type parameter. Only the submitted numerical
certificate coefficients are compared; PSD factors are synthesized separately
and are checked against each candidate's own, independently supplied matrix.
Closeness is NOT certificate acceptance. No reconstruction algorithm is trusted.
-/
namespace LeanPEP.GramPEP.RationalReconstructionAudit

structure PolicyQ where
  maxDenominator : ℕ
  maxAbsError : ℚ
  deriving DecidableEq, Repr

def checkPolicyQ (p : PolicyQ) : Bool :=
  decide (0 < p.maxDenominator ∧ 0 ≤ p.maxAbsError)

theorem checkPolicyQ_eq_true_iff (p : PolicyQ) :
    checkPolicyQ p = true ↔ 0 < p.maxDenominator ∧ 0 ≤ p.maxAbsError := by
  simp [checkPolicyQ]

/-- An endpoint error bound and a reduced-denominator bound, not an algorithm. -/
def WithinQ (p : PolicyQ) (raw reconstructed : ℚ) : Prop :=
  |reconstructed - raw| ≤ p.maxAbsError ∧ reconstructed.den ≤ p.maxDenominator

instance (p : PolicyQ) (a b : ℚ) : Decidable (WithinQ p a b) :=
  inferInstanceAs (Decidable (|b - a| ≤ p.maxAbsError ∧ b.den ≤ p.maxDenominator))

def checkScalarQ (p : PolicyQ) (a b : ℚ) : Bool := decide (WithinQ p a b)

theorem checkScalarQ_eq_true_iff (p : PolicyQ) (a b : ℚ) :
    checkScalarQ p a b = true ↔ WithinQ p a b := by
  simp [checkScalarQ]

/-- Length-sensitive comparison; never a truncating zip. -/
def checkCoefficientsQ (p : PolicyQ) : List ℚ → List ℚ → Bool
  | [], [] => true
  | a :: as, b :: bs => checkScalarQ p a b && checkCoefficientsQ p as bs
  | _, _ => false

/-- Positional correspondence, including both list lengths. -/
def CoefficientsWithinQ (p : PolicyQ) : List ℚ → List ℚ → Prop
  | [], [] => True
  | a :: as, b :: bs => WithinQ p a b ∧ CoefficientsWithinQ p as bs
  | _, _ => False

theorem checkCoefficientsQ_eq_true_iff (p : PolicyQ) (as bs : List ℚ) :
    checkCoefficientsQ p as bs = true ↔ CoefficientsWithinQ p as bs := by
  induction as generalizing bs with
  | nil => cases bs <;> simp [checkCoefficientsQ, CoefficientsWithinQ]
  | cons a as ih =>
      cases bs with
      | nil => simp [checkCoefficientsQ, CoefficientsWithinQ]
      | cons b bs =>
          simp [checkCoefficientsQ, CoefficientsWithinQ, checkScalarQ_eq_true_iff, ih]

theorem coefficients_length (p : PolicyQ) (as bs : List ℚ)
    (h : checkCoefficientsQ p as bs = true) : as.length = bs.length := by
  induction as generalizing bs with
  | nil => cases bs <;> simp_all [checkCoefficientsQ]
  | cons a as ih =>
      cases bs with
      | nil => simp [checkCoefficientsQ] at h
      | cons b bs =>
          change (checkScalarQ p a b && checkCoefficientsQ p as bs) = true at h
          have ht : checkCoefficientsQ p as bs = true := (Bool.and_eq_true_iff.mp h).2
          exact congrArg Nat.succ (ih bs ht)

/-- Row-major coefficient order includes both off-diagonal axes. -/
def gramCoefficientsQ {m : ℕ} (G : Gram m ℚ) : List ℚ :=
  (List.finRange m).flatMap fun i => (List.finRange m).map fun j => G i j

def exprCoefficientsQ {p m : ℕ} (e : LinearExprQ p m) : List ℚ :=
  [e.constCoeff] ++ (List.finRange p).map e.valueCoeff ++ gramCoefficientsQ e.gramCoeff

/-- Factors are excluded: they are exact representations, not solver numbers. -/
def numericalCoefficientsQ {p m : ℕ} {model : ModelQ p m} (c : UpperCertQ model) : List ℚ :=
  [c.bound] ++ exprCoefficientsQ c.objective ++ c.interpTerms.map (fun t => t.weight) ++
    c.assumptionTerms.map (fun t => t.weight) ++ gramCoefficientsQ c.dualMatrix

def assumptionReferencesQ {p m : ℕ} {model : ModelQ p m} (c : UpperCertQ model) : List ℕ :=
  c.assumptionTerms.map fun t => t.index.val

def interpolationReferencesQ {p m : ℕ} {model : ModelQ p m} (c : UpperCertQ model) : List (Fin p × Fin p) :=
  c.interpTerms.map fun t => (t.i, t.j)

/-- A candidate may change numbers, never reference indices, count, or order. -/
def checkChangesQ {p m : ℕ} {model : ModelQ p m} (policy : PolicyQ)
    (raw reconstructed : UpperCertQ model) : Bool :=
  checkPolicyQ policy &&
    decide (assumptionReferencesQ raw = assumptionReferencesQ reconstructed) &&
    decide (interpolationReferencesQ raw = interpolationReferencesQ reconstructed) &&
    checkCoefficientsQ policy (numericalCoefficientsQ raw) (numericalCoefficientsQ reconstructed)

theorem checkChangesQ_eq_true_iff {p m : ℕ} {model : ModelQ p m} (policy : PolicyQ)
    (raw reconstructed : UpperCertQ model) :
    checkChangesQ policy raw reconstructed = true ↔
      (0 < policy.maxDenominator ∧ 0 ≤ policy.maxAbsError) ∧
      assumptionReferencesQ raw = assumptionReferencesQ reconstructed ∧
      interpolationReferencesQ raw = interpolationReferencesQ reconstructed ∧
      CoefficientsWithinQ policy (numericalCoefficientsQ raw) (numericalCoefficientsQ reconstructed) := by
  simp [checkChangesQ, checkPolicyQ_eq_true_iff, checkCoefficientsQ_eq_true_iff, and_assoc]

theorem references_preserved {p m : ℕ} {model : ModelQ p m} (policy : PolicyQ)
    (raw reconstructed : UpperCertQ model) (h : checkChangesQ policy raw reconstructed = true) :
    assumptionReferencesQ raw = assumptionReferencesQ reconstructed ∧
      interpolationReferencesQ raw = interpolationReferencesQ reconstructed := by
  have hs := (checkChangesQ_eq_true_iff policy raw reconstructed).mp h
  exact ⟨hs.2.1, hs.2.2.1⟩

end LeanPEP.GramPEP.RationalReconstructionAudit
