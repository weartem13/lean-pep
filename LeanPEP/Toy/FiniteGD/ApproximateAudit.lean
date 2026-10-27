import LeanPEP.Toy.FiniteGD.ExternalBundle

/-!
# Dual-track auditing for approximate numerical inputs

Approximate solver values enter Lean only after an untrusted preprocessing
step has produced two ordinary exact schema-v1 bundles:

* the `raw` bundle is the exact rational interpretation of the original finite
  base-10 strings, without repair or rounding; and
* the `reconstructed` bundle is a nearby exact candidate produced by an
  explicit reconstruction policy.

Both tracks are audited by the existing `ExactBundleQ` checker.  Acceptance of
the reconstructed track does not imply acceptance of the raw track.
-/

namespace LeanPEP
namespace Toy
namespace FiniteGD

/-- Content hashes tying a Lean comparison to its approximate source and the
untrusted generated artifacts.  These fields are provenance only; mathematical
validity is still decided by `checkExactBundleQ`. -/
structure ApproxAuditProvenanceQ where
  sourceSha256 : String
  rawExactSha256 : String
  reconstructedExactSha256 : String
  reconstructionReportSha256 : String
  comparisonManifestSha256 : String
  deriving DecidableEq, Repr

/-- Side-by-side exact audit results for the raw and reconstructed tracks. -/
structure ApproxAuditComparisonQ (N : ℕ) where
  provenance : ApproxAuditProvenanceQ
  rawAudit : ExactBundleAuditQ N
  reconstructedAudit : ExactBundleAuditQ N
  deriving DecidableEq, Repr

/-- Run the existing exact bundle auditor independently on both tracks. -/
def auditApproximatePairQ
    {N : ℕ}
    (provenance : ApproxAuditProvenanceQ)
    (raw reconstructed : ExactBundleQ N) : ApproxAuditComparisonQ N :=
  { provenance := provenance
    rawAudit := auditExactBundleQ raw
    reconstructedAudit := auditExactBundleQ reconstructed }

end FiniteGD
end Toy
end LeanPEP
