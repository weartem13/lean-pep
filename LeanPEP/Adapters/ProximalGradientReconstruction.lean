import LeanPEP.Adapters.ProximalGradientSparse
import LeanPEP.GramPEP.RationalReconstructionAudit

/-! D8: a fixed exact source, two independent numerical candidates, and an
exact audit of the proposed changes. No proximity test is used as a substitute
for any PSD, source, coefficient identity, or certificate check. -/
namespace LeanPEP.Adapters.ProximalGradientReconstruction
open LeanPEP.GramPEP
open LeanPEP.GramPEP.RationalReconstructionAudit
open LeanPEP.Adapters.ProximalGradientSparse

/-- The raw certificate may be checked regardless of the reconstruction policy. -/
def checkRawQ {n k : ℕ} (s : SourceQ n k) (raw : UpperCertQ s.model) : Bool :=
  ProximalGradientSparse.checkBoundQ s raw

/-- This entry point does NOT assume the raw candidate is accepted. -/
def checkReconstructedQ {n k : ℕ} (s : SourceQ n k) (policy : PolicyQ)
    (raw reconstructed : UpperCertQ s.model) : Bool :=
  checkChangesQ policy raw reconstructed && ProximalGradientSparse.checkBoundQ s reconstructed

theorem checkReconstructedQ_eq_true_iff {n k : ℕ} (s : SourceQ n k) (policy : PolicyQ)
    (raw reconstructed : UpperCertQ s.model) :
    checkReconstructedQ s policy raw reconstructed = true ↔
      checkChangesQ policy raw reconstructed = true ∧
      ProximalGradientSparse.checkBoundQ s reconstructed = true := by
  simp only [checkReconstructedQ, Bool.and_eq_true]

theorem reconstructed_bound_check {n k : ℕ} (s : SourceQ n k) (policy : PolicyQ)
    (raw reconstructed : UpperCertQ s.model)
    (h : checkReconstructedQ s policy raw reconstructed = true) :
    ProximalGradientSparse.checkBoundQ s reconstructed = true :=
  ((checkReconstructedQ_eq_true_iff s policy raw reconstructed).mp h).2

theorem reconstruction_within_policy {n k : ℕ} (s : SourceQ n k) (policy : PolicyQ)
    (raw reconstructed : UpperCertQ s.model)
    (h : checkReconstructedQ s policy raw reconstructed = true) :
    CoefficientsWithinQ policy (numericalCoefficientsQ raw) (numericalCoefficientsQ reconstructed) := by
  have hh := ((checkReconstructedQ_eq_true_iff s policy raw reconstructed).mp h).1
  exact ((checkChangesQ_eq_true_iff policy raw reconstructed).mp hh).2.2.2

theorem checked_certificate {n k : ℕ} (s : SourceQ n k) (policy : PolicyQ)
    (raw reconstructed : UpperCertQ s.model)
    (h : checkReconstructedQ s policy raw reconstructed = true) :
    ∃ d : UpperCertQ (Profiles.ProximalGradient.modelQ n),
      checkUpperCertQ d = true ∧ d.interpTerms = [] ∧
      d.objective = Profiles.ProximalGradient.objectiveQ n ∧ d.bound = reconstructed.bound :=
  ProximalGradientSparse.checked_certificate s reconstructed
    (reconstructed_bound_check s policy raw reconstructed h)

end LeanPEP.Adapters.ProximalGradientReconstruction
