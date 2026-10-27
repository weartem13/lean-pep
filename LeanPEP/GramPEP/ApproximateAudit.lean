import LeanPEP.GramPEP.ExternalBundle

/-!
# Dual-track auditing for approximate Gram bundles

An untrusted preprocessing step turns one approximate decimal artifact into two
ordinary `external-gram-format-v1` bundles:

* `raw` is the exact rational interpretation of every finite base-10 string,
  without tolerance, repair, or binary floating-point conversion;
* `reconstructed` is a separate nearby exact candidate produced by an explicit
  denominator/error policy.

Both tracks are audited independently by the existing `ExactGramBundleQ`
checker.  Acceptance of the reconstructed track never implies acceptance of
the raw numerical artifact.
-/

namespace LeanPEP
namespace GramPEP

/-- Content hashes tying a comparison to its approximate source and generated
artifacts.  These strings record provenance only; all mathematical validity is
recomputed by the exact Gram-bundle checker. -/
structure ApproxGramAuditProvenanceQ where
  sourceSha256 : String
  rawExactSha256 : String
  reconstructedExactSha256 : String
  reconstructionReportSha256 : String
  comparisonManifestSha256 : String
  deriving DecidableEq, Repr

/-- Side-by-side exact audit reports for raw and reconstructed Gram bundles. -/
structure ApproxGramAuditComparisonQ (p m : ℕ) where
  provenance : ApproxGramAuditProvenanceQ
  rawAudit : ExactGramBundleAuditReportQ p m
  reconstructedAudit : ExactGramBundleAuditReportQ p m
  deriving DecidableEq, Repr

/-- Run the existing complete exact Gram auditor independently on both tracks. -/
def auditApproximateGramPairQ
    {p m : ℕ}
    (provenance : ApproxGramAuditProvenanceQ)
    (raw reconstructed : ExactGramBundleQ p m) :
    ApproxGramAuditComparisonQ p m :=
  { provenance := provenance
    rawAudit := auditExactGramBundleQ raw
    reconstructedAudit := auditExactGramBundleQ reconstructed }

end GramPEP
end LeanPEP
