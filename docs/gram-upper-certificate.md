# General exact Gram upper certificates

## Scope

This v0.10D milestone adds the upper/dual side of the general-dimensional
Gram-PEP core.  It does not import solver artifacts and it does not prove the
general smooth-convex interpolation theorem.

For a fixed model with `p` sampled points and `m` abstract Gram basis vectors,
positions and gradients are rational coefficient vectors.  Function values and
the primal Gram matrix remain variables.

## Exact affine-linear expressions

`LinearExprQ p m` represents

```text
constant + Σ_i valueCoeff[i] * f_i + Σ_a,b gramCoeff[a,b] * G[a,b].
```

Gram bilinear expressions are stored with canonical symmetric coefficients:

```text
(u vᵀ + v uᵀ) / 2.
```

On a symmetric primal Gram matrix this evaluates exactly to `uᵀ G v`.  This
canonicalization lets the checker compare every ordered coefficient exactly
without quotienting by symmetry after the fact.

## Formulation assumptions

`ModelQ p m` records:

- symbolic positions;
- symbolic gradients; and
- a list of additional affine-linear constraints required to be nonnegative.

The additional constraints are intended for normalization and other
formulation-specific assumptions.  They are not interpolation slacks and they
are not PSD matrices.

`RealizesModelQ model d` states that a real datum uses the model's exact
position and gradient expressions.  `AssumptionsFeasibleR model d` states that
every recorded additional constraint is nonnegative.

## Certificate structure

`UpperCertQ model` contains:

- a rational bound;
- an affine-linear objective;
- nonnegative interpolation multipliers;
- nonnegative indexed assumption multipliers;
- a rational dual matrix; and
- an exact weighted-rank-one PSD factorization certificate for the dual matrix.

The checked identity is

```text
bound - objective
  = Σ interpolation weights * interpolation slacks
  + Σ assumption weights * formulation assumptions
  + <dualMatrix, primalGram>.
```

All coefficients are compared over `ℚ`.

## Dual PSD soundness

If

```text
dualMatrix = Σ_r w_r u_r u_rᵀ,   w_r >= 0,
```

then its Frobenius pairing with a real PSD primal Gram matrix is

```text
<dualMatrix, G> = Σ_r w_r * (u_rᵀ G u_r) >= 0.
```

The Lean proof uses the existing exact rational factor checker and the
proposition-level primal Gram PSD semantics.  It does not use eigenvalues or
floating-point tolerance.

## Regression certificates

### Two-point structural regression

The first example proves

```text
(f_1 - f_0) + G_00 - G_11 <= 1
```

from:

- interpolation slack `(0,1)`;
- normalization `1 - G_00 >= 0`; and
- dual PSD term `G_11 >= 0` certified by `e_1 e_1ᵀ`.

This example exercises all three nonnegative certificate channels.

### Genuine one-step Gram-PEP certificate

The second example uses the abstract Gram basis `(x_0, g_0, g_1)` and points
`(x_star, x_0, x_1)` with `x_1 = x_0 - g_0`.  The normalization assumption is

```text
1 - ||x_0||_G^2 >= 0.
```

The certificate proves

```text
f_1 - f_star <= 1/6.
```

It uses three interpolation multipliers equal to `1/2`, normalization
multiplier `1/6`, and the exact dual factors

```text
1/4 * ||g_0 - (1/3) x_0||_G^2,
1/4 * ||g_1 - (1/3) x_0||_G^2,
1/4 * ||g_0 + g_1 - (2/3) x_0||_G^2.
```

This is a finite Gram-PEP upper theorem.  It is not yet the general theorem
that every feasible finite Gram datum has an actual smooth-convex interpolant.

## Trust boundary

The checker and soundness theorem are Lean code.  The v0.11A exact external
Gram importer generates model and certificate terms but remains untrusted:
Lean rechecks every weight, dual factorization entry, affine coefficient,
primal feasibility obligation, and exact primal attainment.  The strict schema
is documented in `external-gram-format-v1.md`.

## Structured exact audit layer

`LeanPEP/GramPEP/UpperCertificateAudit.lean` adds a complete deterministic
report over the same Boolean acceptance predicate.  It does not define a second
notion of validity and does not repair malformed certificates.

The report contains:

- every negative interpolation multiplier, with its certificate-list index and
  ordered point pair;
- every negative assumption multiplier, with its term index and referenced
  assumption index;
- the complete `PSDFactorAuditReportQ` for the separate dual matrix; and
- every affine identity mismatch at a typed constant, function-value, or Gram
  entry location, together with exact expected and actual rationals.

The audit does not short-circuit.  One malformed certificate may expose several
independent failures.  Its `accepted` field is the existing
`checkUpperCertQ` result, and Lean proves both the exact validity equivalence and
the same universal real upper-bound soundness theorem for accepted reports.

The diagnostic examples use cancelling interpolation, assumption, and dual
factor pairs to isolate individual failure channels without changing the
certificate identity.  See `docs/gram-upper-audit.md`.
