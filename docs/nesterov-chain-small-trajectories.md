# Exact small trajectories on the Nesterov chain

## Scope

This B2 milestone keeps the explicit hard-function branch separate from the
finite-PEP semantics.  It specializes the already verified Nesterov-chain
function to `L = 1`.  The standard gradient-descent step therefore has step
size `1 / L = 1`:

```text
x⁺ = x - gradient n 1 x.
```

The Lean definition is `unitGDStep`.  `IsUnitGDPath` records every recurrence
of a finite path.  These are exact real-vector statements, not floating-point
simulations.

## Dimension 3, one step

The classic `k = 1` chain uses branch parameter `n = 2`, hence ambient type
`Fin 3 → ℝ`.  From the zero vector:

```text
x₀ = (0, 0, 0),
g₀ = (-1/4, 0, 0),
x₁ = (1/4, 0, 0).
```

The exact values are:

```text
f(x₀) = 0,
f(x₁) = -3/64,
f(x★) = -3/32,
f(x₁) - f(x★) = 3/64,
‖x₀ - x★‖² = 7/8.
```

For the normalized `L = 1` performance ratio

```text
(f(x₁) - f(x★)) / ‖x₀ - x★‖²,
```

Lean checks the exact value

```text
3/56.
```

A separate comparison module combines this equality with the already proved
one-step finite-PEP theorem whose greatest value is `1/6`, and checks

```text
3/56 < 1/6.
```

This means the displayed Nesterov-chain trajectory does not attain that exact
finite-PEP constant.  It does not by itself provide a generic actual-function-to-Gram conversion or
a theorem for an algorithm class.  The two displayed trajectories now have
separate explicit Gram witnesses, while v0.12A addresses the generic bridge.

## Dimension 5, two steps

The classic `k = 2` chain uses branch parameter `n = 4`, hence ambient type
`Fin 5 → ℝ`.  The exact trajectory is:

```text
x₀ = (0, 0, 0, 0, 0),
g₀ = (-1/4, 0, 0, 0, 0),
x₁ = (1/4, 0, 0, 0, 0),
g₁ = (-1/8, -1/16, 0, 0, 0),
x₂ = (3/8, 1/16, 0, 0, 0).
```

The exact final quantities are:

```text
f(x₂) = -65/1024,
f(x★) = -5/48,
f(x₂) - f(x★) = 125/3072,
‖x₀ - x★‖² = 55/36,
normalized performance = 75/2816.
```

The scalar comparison with the exact normalized two-step finite-PEP constant
is:

```text
75/2816 < 1/10.
```

Again, this is a comparison of independently formalized exact constants.
Since v0.10C, this explicit five-dimensional trajectory has also been encoded
as an exact rational coordinate Gram witness in
`LeanPEP.Bridges.NesterovChainGram`: its standard-basis PSD certificate, all
ordered interpolation slacks, both GD steps, normalized performance, and
equality with the direct real samples are kernel-checked.

## Trust and theorem boundary

The B2 files contain no numerical solver or floating-point computation.  The
coordinates and performance ratios are exact rational expressions in `ℝ`.
The pinned local build and `tests/lean/smoke/V08B2SmokeTest.lean` have completed successfully,
so Lean kernel checking supports claims about these two explicit function
executions and the stated scalar comparisons.

They still do not establish:

- a finite-PEP conversion for arbitrary explicit trajectories;
- support propagation for linear-span or zero-respecting algorithms;
- a lower bound for an algorithm class; or
- a theorem-level oracle complexity result.
