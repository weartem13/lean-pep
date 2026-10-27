# Exact three-step finite PEP

This milestone instantiates the existing normalized one-dimensional finite-GD
semantics at `N = 3`.

## Exact primal witness

The rational witness is

```text
g₀ = g₁ = g₂ = g₃ = 1/7,
f₀ = 13/98,
f₁ = 11/98,
f₂ = 9/98,
f₃ = 1/14.
```

The generic checker scans all `(3 + 2)^2 = 25` ordered interpolation pairs.
Acceptance is bridged to real finite-PEP feasibility by the existing Q-to-R
soundness theorem.

## Exact upper certificate

The target is

```text
1/14 - f₃.
```

The nonnegative interpolation multipliers are

```text
(star,p₀) : 1/6
(star,p₁) : 7/30
(star,p₂) : 7/20
(star,p₃) : 1/4
(p₀,p₁)  : 1/6
(p₁,p₂)  : 2/5
(p₂,p₃)  : 3/4
```

The consecutive-iterate weights are the cumulative sums of the star weights.
Consequently, all function-value coefficients cancel except the required
coefficient `-1` on `f₃`.

After subtracting these interpolation terms, the remaining affine quadratic
polynomial is the exact sum of four nonnegative rationally weighted squares.
Writing `a = g₀-1/7`, `b = g₁-1/7`, `c = g₂-1/7`, and `d = g₃-1/7`, the factors
are

```text
a + (7/5)b + (21/10)c + (3/2)d,
a - (7/25)b - (21/50)c - (3/10)d,
b - (7/12)c - (5/12)d,
c - d,
```

with weights

```text
7/72, 5/72, 51/250, 23/96.
```

The generic `UpperCertQ` checker verifies nonnegativity of every multiplier and
checks the complete polynomial identity coefficient by coefficient over exact
rationals.

## Logical conclusion

When both checkers accept, Lean proves the exact value of this finite PEP:

```text
IsGreatest ThreeStep.pepValues (1/14).
```

This remains an exact finite-PEP theorem.  It is not yet a complete theorem over
all actual smooth convex functions because the general interpolation bridge has
not been formalized.
