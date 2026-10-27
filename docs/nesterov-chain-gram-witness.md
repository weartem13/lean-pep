# v0.10C: exact Nesterov-chain Gram witnesses

This stage connects the two previously independent branches:

```text
explicit Nesterov quadratic and exact GD trajectory
                    ↓
exact rational standard-coordinate samples
                    ↓
Gram-PEP interpolation and PSD audits
```

## Choice of Gram basis

For each small trajectory, the abstract Gram basis is the ambient standard
coordinate basis.  Thus the PEP Gram matrix is the identity matrix `I` in
ambient dimension 3 or 5.  Positions and gradients are their exact coordinate
vectors.

This identity Gram matrix is not the tridiagonal `chainMatrix` used in the
quadratic function.  The latter is the Hessian structure matrix of the
explicit function; the former records inner products of the selected PEP base
vectors.

## Exact PSD certificate

The canonical certificate is

```text
I = Σ_i e_i e_iᵀ,
```

with every factor weight equal to one.  The v0.10B checker rechecks target
symmetry, every nonnegative weight, and every matrix entry exactly.

## Dimension 3, one step

The point set is `star, iter 0, iter 1`.  The exact samples are

```text
x★ = (3/4, 1/2, 1/4)
x0 = (0, 0, 0)
x1 = (1/4, 0, 0)

g★ = (0, 0, 0)
g0 = (-1/4, 0, 0)
g1 = (-1/8, -1/16, 0)

f★ = -3/32
f0 = 0
f1 = -3/64
```

All nine ordered interpolation slacks are nonnegative.  The exact objective
gap is `3/64`, the initial distance squared is `7/8`, and the normalized value
is `3/56`.

## Dimension 5, two steps

The point set is `star, iter 0, iter 1, iter 2`.  The exact samples are

```text
x★ = (5/6, 2/3, 1/2, 1/3, 1/6)
x0 = (0, 0, 0, 0, 0)
x1 = (1/4, 0, 0, 0, 0)
x2 = (3/8, 1/16, 0, 0, 0)

g★ = (0, 0, 0, 0, 0)
g0 = (-1/4, 0, 0, 0, 0)
g1 = (-1/8, -1/16, 0, 0, 0)
g2 = (-5/64, -1/16, -1/64, 0, 0)

f★ = -5/48
f0 = 0
f1 = -3/64
f2 = -65/1024
```

All sixteen ordered interpolation slacks are nonnegative.  Both unit-step GD
updates hold exactly.  The exact final gap is `125/3072`, the initial distance
squared is `55/36`, and the normalized value is `75/2816`.

## Rational-to-real meaning

The rational data are cast entrywise to reals.  Lean proves that the cast
preserves Gram inner products, squared norms, and every interpolation slack.
For these identity-Gram witnesses, real PSD follows independently from the
standard-coordinate sum-of-squares theorem.

The stage also proves that the cast positions, gradients, and function values
agree with the previously formalized real Nesterov trajectories.  Therefore
these are not merely nearby rational candidates: they are exact coordinate
representations of the already verified explicit executions.

## Boundary

This stage proves two explicit finite conversions.  It does not yet provide:

- a general theorem converting every smooth convex execution into Gram data;
- a general interpolation completeness theorem;
- formulation-level import of a solver Gram basis;
- a general dual PSD certificate; or
- an oracle-complexity lower bound.
