# Structured audit for general Gram upper certificates

## Purpose

The verified v0.10D checker returns one Boolean.  The v0.10D2 layer preserves
that Boolean as the authoritative acceptance result and adds a deterministic
exact report for inspection, testing, and future external-bundle adapters.

No report field is inferred from floating-point tolerances.  All weights and
coefficient values are rational numbers, and the dual PSD section reuses the
exact factorization audit from v0.10B.

## Report structure

`UpperCertAuditReportQ p m` contains:

```text
accepted
negativeInterpWeights
negativeAssumptionWeights
dualAudit
identityMismatches
```

### Interpolation multipliers

Each `NegativeInterpWeightQ p` records:

```text
index, weight, i, j
```

where `index` is the deterministic certificate-list position and `(i,j)` is the
ordered interpolation pair.

### Assumption multipliers

Each `NegativeAssumptionWeightQ` records:

```text
index, assumptionIndex, weight
```

The first index locates the certificate term; the second locates the referenced
formulation assumption.

### Dual PSD section

`dualAudit` is the complete existing `PSDFactorAuditReportQ`.  It separately
reports:

- target-matrix asymmetries;
- negative rank-one factor weights; and
- exact target/factorized entry mismatches.

The dual matrix remains distinct from the primal Gram matrix and from scalar
interpolation slacks.

### Affine identity coefficients

`identityMismatches` compares

```text
expected = bound - objective
actual   = interpolation + assumptions + dual pairing
```

at every typed location:

```text
constant
function value f_i
ordered Gram entry G_ab
```

Every mismatch records exact expected and actual rationals.

## Soundness boundary

Lean proves:

```text
audit accepted = true <-> existing proposition-level certificate validity
```

and transports accepted audit reports through the existing universal real
upper-bound theorem.  Rejection only diagnoses the supplied certificate; it
does not imply that the claimed mathematical bound is false.

## Isolated regressions

The examples include:

- a clean accepted structural certificate;
- a clean accepted one-step `1/6` certificate;
- an appended cancelling interpolation pair with one negative multiplier;
- an appended cancelling assumption pair with one negative multiplier;
- appended cancelling dual factors with one negative factor weight;
- a missing dual factor with an exact `(1,1)` entry mismatch; and
- a wrong bound with one constant-coefficient mismatch.

The cancelling examples keep the exact affine identity unchanged, so the
reported failure is localized to the intended channel.
