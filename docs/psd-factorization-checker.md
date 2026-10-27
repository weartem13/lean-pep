# v0.10B: exact rational PSD factorization checker

## Scope

This milestone turns the proposition-level Gram PSD obligation from v0.10A
into an executable exact rational certificate check.  It does not use floating
point, numerical eigenvalues, or tolerance-based repair.

The checker accepts a target rational Gram matrix `G : Gram m ℚ` and a finite
list of weighted rank-one factors

```text
(weight_r, vector_r),
```

with intended identity

```text
G = Σ_r weight_r * vector_r * vector_rᵀ.
```

All vector dimensions are represented by `Fin m`.  A malformed source vector
length therefore cannot be constructed in this typed Lean layer; the v0.11A
strict exact Gram importer rejects source-level length mismatches before it
generates typed Lean terms.

## Exact obligations

`checkPSDFactorQ G cert` checks three independent obligations:

1. `G` is symmetric entry by entry;
2. every factor weight is nonnegative; and
3. every entry of `factorGramQ cert.factors` equals the corresponding entry of
   `G`.

The checker scans deterministic row-major lists of all `m²` ordered entries.
There is no conversion to a floating-point matrix.

## Soundness

For one factor, Lean proves the exact identity

```text
gramNormSq (weight * vector * vectorᵀ) u
  = weight * (Σ_i u_i * vector_i)^2.
```

Consequently, nonnegative weights make every represented quadratic form
nonnegative.  The theorem

```text
checkPSDFactorQ_sound
```

converts Boolean acceptance into

```text
IsGramPosSemidef G.
```

This theorem is the mathematical trust boundary of the executable checker.
The factor producer may be untrusted; Lean checks all weights and all entries.
The later module `LeanPEP.GramPEP.PSDFactorizationRealBridge` now supplies the
exact rational-to-real soundness theorem `checkPSDFactorQ_sound_real`; accepted
rational certificates therefore establish PSD of the entrywise real cast as
well.  The Nesterov-to-Gram bridge uses this infrastructure for explicit real
function samples.

## Structured diagnostics

`auditPSDFactorQ` returns:

- every exact target asymmetry `(i,j,left,right)`;
- every negative factor weight with its list index; and
- every exact target/factor mismatch `(i,j,expected,actual)`.

The report retains rational values rather than rounded residuals.  Soundness
lemmas state that reported asymmetries and entry mismatches name the exact
matrix entries and that every reported factor weight is strictly negative.

## Regression examples

The milestone includes:

- acceptance of the one-dimensional unit Gram matrix `[1]`;
- acceptance of
  `[[2,1],[1,2]]` through three rational rank-one factors;
- rejection of an otherwise exact factorization with weight `-1`;
- rejection and localization of a missing factor at entry `(0,0)`; and
- rejection and localization of an asymmetric `2 × 2` target.

## Boundaries

This checker establishes PSD of a supplied Gram matrix.  It does not by itself
check interpolation constraints, algorithm equations, normalization, an
objective, or a dual upper-certificate identity.  `CoreFeasible` continues to
combine proposition-level PSD with scalar interpolation feasibility; later
formulation layers will add the remaining PEP obligations.

## Verified v0.10B status and v0.10C use

The checker and its structured examples were kernel-checked locally on
2026-08-13 with Lean 4 / mathlib v4.31.0; the full project build completed with
3029 jobs.  v0.10C reuses the same checker for the identity Gram matrices of
the dimension-3 and dimension-5 standard-coordinate Nesterov witnesses.  Their
certificates are the canonical sums of standard-basis rank-one factors.
