# Nesterov chain basic formalization

## Indexing convention

The Lean parameter `n` in this branch gives ambient dimension `n + 1`:

```text
Vector n = Fin (n + 1) → ℝ.
```

There are exactly `n` adjacent edges, indexed by `Fin n`. The edge with index
`i` joins coordinates `i.castSucc` and `i.succ`.

Consequently:

- dimension 1 uses parameter `n = 0`;
- the classic `k = 1`, dimension-3 example uses parameter `n = 2`;
- the classic `k = 2`, dimension-5 example uses parameter `n = 4`; and
- a classic dimension `2k + 1` uses Lean parameter `2k`.

This parameter is unrelated to `FiniteGD.Data N`, where `N` counts gradient-
descent steps in the one-dimensional finite PEP.

## Structure matrix

The matrix is defined by the exact factorization

```text
A = e₀e₀ᵀ
    + Σᵢ (eᵢ - eᵢ₊₁)(eᵢ - eᵢ₊₁)ᵀ
    + e_last e_lastᵀ.
```

This factorization gives the tridiagonal chain structure without introducing a
floating-point spectral computation. It immediately separates three notions
that must not be conflated:

1. `A` is the Hessian structure matrix of this explicit quadratic;
2. a future PEP Gram matrix represents inner products among PEP vectors; and
3. interpolation slacks are scalar inequalities, not matrices.

The exact quadratic identity is

```text
xᵀAx = x₀² + Σᵢ (xᵢ - xᵢ₊₁)² + x_last².
```

The rank-one factorization proves positive semidefiniteness. A separate
sum-of-squares estimate proves

```text
xᵀAx ≤ 4 Σᵢ xᵢ².
```

No eigenvalue approximation is used.

## Function semantics

For a real parameter `L`, define

```text
f(x) = (L / 8) xᵀAx - (L / 4) x₀,
g(x) = (L / 4) (Ax - e₀),
H    = (L / 4) A.
```

The primary semantic theorem is the exact identity

```text
f(x + d) = f(x) + ⟨g(x), d⟩ + (L / 8) dᵀAd.
```

When `L ≥ 0`, the remainder is nonnegative, giving the first-order convexity
inequality. Since `dᵀAd ≤ 4‖d‖²`, the same identity gives

```text
f(y) ≤ f(x) + ⟨g(x), y - x⟩ + (L / 2) ‖y - x‖².
```

This is the standard smooth upper model used in optimization analysis. The
current B1 API deliberately proves these exact identities directly. A later
stage may package them into mathlib's differential and Lipschitz predicates.

## Minimizer

In zero-based indexing,

```text
x★ i = 1 - (i.val + 1) / (n + 2).
```

Every adjacent difference and the final coordinate equal `1 / (n + 2)`. A
telescoping calculation proves

```text
energyInner x★ z = z₀,
```

which is then converted into the vector equation

```text
A x★ = e₀.
```

Therefore `g(x★) = 0`. Completing the square yields

```text
f(x) = f(x★) + (L / 8) (x - x★)ᵀA(x - x★),
```

and, for `L ≥ 0`, global minimality. The exact value is

```text
f(x★) = -(L / 8) * (1 - 1 / (n + 2)).
```

## Validation

The B1 modules were kernel-checked locally on 2026-08-11 with Lean 4 / mathlib
`v4.31.0`. `lake build LeanPEP` completed successfully with 3016 jobs, and
`lake env lean tests/lean/smoke/V08SmokeTest.lean` checked the public theorem surface together
with the exact dimension-3 minimizer, energy, quadratic-form, and optimal-value
regressions. The build emitted only non-blocking tactic-style linter warnings.

## Current boundary

B1 proves properties of this explicit real function. It does not yet prove:

- that its trajectories have been converted to a finite PEP witness;
- that it is an exact finite-horizon PEP worst case;
- support propagation for a class of first-order methods; or
- an oracle complexity lower bound.
