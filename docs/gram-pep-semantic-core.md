# v0.10A: exact Gram-PEP semantic core

## Scope

This milestone introduces the exact mathematical vocabulary needed for a
finite-dimensional Gram formulation of a smooth-convex PEP.  It does not yet
implement an executable PSD checker, a dual PSD certificate, a solver adapter,
or the smooth-convex interpolation theorem.

## Vector expressions and the Gram matrix

For a chosen family of `m` abstract vectors, a vector expression is a
coefficient function

```text
VecExpr m 𝕜 = Fin m → 𝕜.
```

The Gram matrix is

```text
Gram m 𝕜 = Matrix (Fin m) (Fin m) 𝕜,
```

with intended meaning

```text
G[a,b] = ⟨v_a, v_b⟩.
```

The exact semantics evaluate

```text
gramInner G u v = uᵀ G v
gramNormSq G u  = uᵀ G u.
```

This matrix is the PEP geometry object.  It is distinct from every scalar
interpolation slack and from the Nesterov-chain Hessian structure matrix.

## General sampled data

`GramPEP.Data Point m 𝕜` stores:

- one Gram matrix;
- a coefficient expression for every sampled position;
- a coefficient expression for every sampled gradient; and
- one scalar function value for every point.

For every ordered pair `(i,j)`, the normalized `1`-smooth convex interpolation
slack is

```text
f_i - f_j
- ⟨g_j, x_i - x_j⟩_G
- (1/2) ‖g_i - g_j‖²_G.
```

`InterpolationFeasible` requires each such scalar to be nonnegative.
`IsGramPosSemidef` separately requires Gram symmetry and nonnegativity of every
represented quadratic form.  `CoreFeasible` is the conjunction of those two
obligations.

Algorithm equations, normalization, and objectives remain formulation
specific.  The name `CoreFeasible` is deliberately narrower than a complete
PEP model.

## One-dimensional embedding regression

The existing scalar `FiniteGD.Data N 𝕜` is embedded with one abstract basis
vector and the unit Gram matrix `[1]`.  Scalar positions and gradients become
one-coordinate coefficient expressions.

Lean theorem `interpolationSlack_ofFiniteGD` states that every ordered slack is
preserved exactly.  Therefore:

```text
InterpolationFeasible (ofFiniteGD d) ↔ FiniteGD.Feasible d
CoreFeasible          (ofFiniteGD d) ↔ FiniteGD.Feasible d.
```

The verified `N = 1`, `N = 2`, and `N = 3` rational witnesses are rechecked
through this bridge, while the known invalid two-step candidate remains
infeasible.  This proves compatibility of the new semantic layer with the
existing exact checker; it does not yet replace that checker.

## Executable PSD layer

v0.10B adds a separate exact rational factorization checker for certificates
of the form

```text
G = Σ_r w_r u_r u_rᵀ,    w_r ≥ 0.
```

It checks symmetry, all weights, and every factorization entry, then proves
`IsGramPosSemidef G` from acceptance.  Structured reports contain exact
asymmetries, negative weights, and entry mismatches.  The semantic definition
in this file remains independent of the certificate syntax.  See
`docs/psd-factorization-checker.md`.

## v0.10C explicit coordinate realizations

The semantic core is now used by two candidate exact realizations of the
formalized Nesterov-chain trajectories.  The abstract base vectors are the
ambient standard coordinate axes, so their Gram matrix is the identity matrix.
Exact rational positions, gradients, and values are rechecked against all
ordered interpolation constraints, then cast to the real layer with exact
slack preservation.  The cast data are proved equal to the existing explicit
real samples.

This is an explicit finite bridge for two examples, not the general
smooth-convex soundness or completeness theorem.

## v0.11A exact external boundary

The v0.11A candidate packages the semantic core, primal PSD factors,
formulation assumptions, general upper certificates, dual PSD factors, source
ordering, and provenance in a separate strict exact JSON schema.  The generated
Lean module runs one non-short-circuiting `ExactGramBundleQ` audit and proves a
real closed-loop soundness theorem for accepted bundles.

The importer does not change `CoreFeasible`: algorithm equations,
normalization, and other formulation assumptions remain explicit `ModelQ`
semantics.  See `docs/external-gram-format-v1.md`.
