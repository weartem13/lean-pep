"""Independent exact regressions for the v0.13C1 composite/proximal slice.

These checks deliberately do not replace Lean elaboration. All arithmetic in
this file is fractions.Fraction; source constants are parsed, not silently
replaced by convenient floating-point approximations. No solver is invoked.
"""
from __future__ import annotations

import ast
from dataclasses import dataclass, replace
from fractions import Fraction as Q
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / 'LeanPEP/Profiles/ProximalGradientOneStep.lean'
TEXT = SOURCE.read_text(encoding='utf-8')


def rational(text: str) -> Q:
    node = ast.parse(text.strip(), mode='eval').body
    def parse(n: ast.AST) -> Q:
        if isinstance(n, ast.Constant) and type(n.value) is int:
            return Q(n.value)
        if isinstance(n, ast.UnaryOp) and isinstance(n.op, (ast.USub, ast.UAdd)):
            x = parse(n.operand)
            return -x if isinstance(n.op, ast.USub) else x
        if isinstance(n, ast.BinOp):
            x, y = parse(n.left), parse(n.right)
            if isinstance(n.op, ast.Div):
                return x / y
            if isinstance(n.op, ast.Add):
                return x + y
            if isinstance(n.op, ast.Sub):
                return x - y
            if isinstance(n.op, ast.Mult):
                return x * y
        raise ValueError(f'Not an exact rational expression: {text!r}')
    return parse(node)


def source_vector(name: str) -> tuple[Q, ...]:
    match = re.search(r'def ' + re.escape(name) + r'[^\n]*:= !\[([^\]]+)\]', TEXT)
    if match is None:
        raise ValueError(f'Missing source vector {name}')
    return tuple(rational(v) for v in match.group(1).split(','))


def add(u, v):
    return tuple(x + y for x, y in zip(u, v, strict=True))


def scale(c, u):
    return tuple(c * x for x in u)


def sub(u, v):
    return add(u, scale(Q(-1), v))


def dot(u, v):
    return sum((x * y for x, y in zip(u, v, strict=True)), Q(0))


def outer(u, v):
    return tuple(tuple(x * y for y in v) for x in u)


@dataclass(frozen=True)
class Expr:
    const: Q
    values: tuple[Q, ...]
    gram: tuple[tuple[Q, ...], ...]

    @staticmethod
    def zero(p=5, m=5):
        return Expr(Q(0), (Q(0),) * p, ((Q(0),) * m,) * m)

    def __add__(self, other):
        return Expr(self.const + other.const, add(self.values, other.values),
                    tuple(add(x, y) for x, y in zip(self.gram, other.gram, strict=True)))

    def scaled(self, c):
        return Expr(c * self.const, scale(c, self.values),
                    tuple(scale(c, row) for row in self.gram))

    def __sub__(self, other):
        return self + other.scaled(Q(-1))

    def evaluate(self, values, gram):
        return self.const + dot(self.values, values) + sum(
            (dot(a, b) for a, b in zip(self.gram, gram, strict=True)), Q(0))


def value(i):
    z = Expr.zero()
    return replace(z, values=tuple(Q(j == i) for j in range(5)))


def constant(c):
    return replace(Expr.zero(), const=Q(c))


def bilinear(u, v):
    return replace(Expr.zero(), gram=tuple(tuple((u[i]*v[j] + v[i]*u[j])/2
        for j in range(5)) for i in range(5)))


@dataclass(frozen=True)
class Sample:
    slot: int
    position: tuple[Q, ...]
    oracle: tuple[Q, ...]


def pair_expr(kind, a, b):
    expr = value(a.slot) - value(b.slot) - bilinear(b.oracle, sub(a.position, b.position))
    if kind == 'smooth':
        dg = sub(a.oracle, b.oracle)
        return expr - bilinear(dg, dg).scaled(Q(1, 2))
    if kind != 'convex':
        raise ValueError('Unknown function class')
    return expr


def component_constraints(kind, samples):
    return [pair_expr(kind, a, b) for a in samples for b in samples]


U = source_vector('initialVecQ')
GS = source_vector('starGradientQ')
G0 = source_vector('initialGradientQ')
G1 = source_vector('finalGradientQ')
S1 = source_vector('finalSubgradientQ')
ZERO = (Q(0),) * 5
X1 = sub(sub(U, G0), S1)
VECTOR_NAMES = {'0': ZERO, 'initialVecQ': U, 'finalVecQ': X1,
    'starGradientQ': GS, '-starGradientQ': scale(Q(-1), GS),
    'initialGradientQ': G0, 'finalGradientQ': G1, 'finalSubgradientQ': S1}
if not re.search(r'def finalVecQ[^\n]*:= initialVecQ - initialGradientQ - finalSubgradientQ', TEXT):
    raise ValueError('Audit the changed implicit update before changing its test interpreter')

def source_samples(name):
    section = TEXT.split('def '+name, 1)[1].split('\ndef ', 1)[0]
    records = re.findall(r'valueIndex := (\d+), position := ([^,]+), oracle := ([^}]+)', section)
    return [Sample(int(i), VECTOR_NAMES[x.strip()], VECTOR_NAMES[g.strip()]) for i, x, g in records]

SMOOTH = source_samples('smoothSamplesQ')
NONSMOOTH = source_samples('nonsmoothSamplesQ')
RADIUS = constant(1) - bilinear(U, U)
CONSTRAINTS = component_constraints('smooth', SMOOTH) + component_constraints('convex', NONSMOOTH) + [RADIUS]
OBJECTIVE = value(2) + value(4) - value(0) - value(3)
BOUND = rational(re.search(r'def upperCertQ.*?bound := ([^\n]+)', TEXT, re.S).group(1))
FACTOR_SECTION = TEXT.split('def dualFactorsQ', 1)[1].split('def upperCertQ', 1)[0]
FACTORS = [(rational(w), tuple(rational(v) for v in vec.split(',')))
    for w, vec in re.findall(r'weight := ([^,]+), vector := !\[([^\]]+)\]', FACTOR_SECTION)]
TERM_SECTION = TEXT.split('def upperCertQ', 1)[1].split('theorem upperCertQ_check', 1)[0]
TERMS = [(rational(w), int(i)) for w, i in re.findall(r'weight := ([^,]+), index := ⟨(\d+),', TERM_SECTION)]
PRIMAL_SECTION = TEXT.split('def primalFactorQ', 1)[1].split('theorem primalQ_psd_check', 1)[0]
PRIMAL_VECTOR = tuple(rational(v) for v in re.search(r'vector := !\[([^\]]+)\]', PRIMAL_SECTION).group(1).split(','))
PRIMAL_VALUES = tuple(rational(v) for v in re.search(r'value := !\[([^\]]+)\]', PRIMAL_SECTION).group(1).split(','))
PRIMAL_GRAM = outer(PRIMAL_VECTOR, PRIMAL_VECTOR)


def factor_expr(factors):
    out = Expr.zero()
    for w, v in factors:
        out += bilinear(v, v).scaled(w)
    return out


def rhs(constraints=CONSTRAINTS, terms=TERMS, factors=FACTORS):
    out = factor_expr(factors)
    for w, index in terms:
        out += constraints[index].scaled(w)
    return out


def accepted(constraints=CONSTRAINTS, terms=TERMS, factors=FACTORS, bound=BOUND,
             objective=OBJECTIVE, implicit_terms=()):
    # This explicit-mode guard corresponds to the REQUIRED hempty hypothesis,
    # not to a claim that the legacy checker has changed its behavior.
    return (not implicit_terms and all(w >= 0 for w, _ in terms)
            and all(w >= 0 for w, _ in factors)
            and rhs(constraints, terms, factors) == constant(bound) - objective)


def rank(matrix):
    a = [list(r) for r in matrix]
    k = 0
    for j in range(len(a[0])):
        pivot = next((i for i in range(k, len(a)) if a[i][j]), None)
        if pivot is None:
            continue
        a[k], a[pivot] = a[pivot], a[k]
        t = a[k][j]
        a[k] = [x/t for x in a[k]]
        for i in range(len(a)):
            if i != k:
                t = a[i][j]
                a[i] = [x-t*y for x, y in zip(a[i], a[k], strict=True)]
        k += 1
    return k


def actual_datum(f, h, g, xstar, x0, x1, s1):
    base = [sub(x0, xstar), g(xstar), g(x0), g(x1), s1]
    gram = tuple(tuple(dot(a, b) for b in base) for a in base)
    vals = (f(xstar), f(x0), f(x1), h(xstar), h(x1))
    return base, gram, vals


class CompositeProximalTests(unittest.TestCase):
    def test_component_order_and_count(self):
        self.assertEqual(len(CONSTRAINTS), 14)
        smooth_section = TEXT.split('def smoothComponentQ', 1)[1].split('def nonsmoothComponentQ', 1)[0]
        nonsmooth_section = TEXT.split('def nonsmoothComponentQ', 1)[1].split('def radiusExprQ', 1)[0]
        self.assertIn('functionClass := .oneSmoothConvex', smooth_section)
        self.assertIn('functionClass := .convex', nonsmooth_section)
        objective_section = TEXT.split('def objectiveQ', 1)[1].split('def profileQ', 1)[0]
        self.assertEqual(re.findall(r'valueVar (\d+)', objective_section), ['2', '4', '0', '3'])
        self.assertEqual([s.slot for s in SMOOTH], [0, 1, 2])
        self.assertEqual([s.slot for s in NONSMOOTH], [3, 4])

    def test_no_cross_component_value_coefficients(self):
        self.assertTrue(all(e.values[3:] == (0, 0) for e in CONSTRAINTS[:9]))
        self.assertTrue(all(e.values[:3] == (0, 0, 0) for e in CONSTRAINTS[9:13]))

    def test_update_and_composite_stationarity(self):
        self.assertEqual(X1, (1, 0, -1, 0, -1))
        self.assertEqual(add(SMOOTH[0].oracle, NONSMOOTH[0].oracle), ZERO)
        self.assertNotEqual(SMOOTH[0].oracle, ZERO)

    def test_certificate_source_weights(self):
        self.assertEqual(BOUND, Q(1, 4))
        self.assertEqual(TERMS, [(Q(1, 2), 1), (Q(1, 2), 5), (Q(1, 2), 2), (Q(1), 10), (Q(1, 4), 13)])
        self.assertEqual([w for w, _ in FACTORS], [Q(1, 4), Q(1, 2), Q(1, 8)])
        self.assertEqual(len(FACTORS), 3)

    def test_exact_full_coefficient_identity(self):
        self.assertTrue(accepted())
        self.assertEqual(rhs(), constant(BOUND) - OBJECTIVE)

    def test_dual_rank_and_positive_factors(self):
        self.assertEqual(rank(factor_expr(FACTORS).gram), 3)
        self.assertTrue(all(w > 0 for w, _ in FACTORS))
        for k in range(-5, 6):
            v = tuple(Q((j+1)*k-j*j, 7) for j in range(5))
            self.assertGreaterEqual(factor_expr(FACTORS).evaluate((Q(0),)*5, outer(v, v)), 0)

    def test_primal_rank_and_all_constraints(self):
        self.assertEqual(rank(PRIMAL_GRAM), 1)
        self.assertTrue(all(e.evaluate(PRIMAL_VALUES, PRIMAL_GRAM) >= 0 for e in CONSTRAINTS))

    def test_primal_attainment(self):
        self.assertEqual(OBJECTIVE.evaluate(PRIMAL_VALUES, PRIMAL_GRAM), BOUND)

    def test_complementarity(self):
        for w, i in TERMS:
            self.assertEqual(w*CONSTRAINTS[i].evaluate(PRIMAL_VALUES, PRIMAL_GRAM), 0)
        for w, v in FACTORS:
            self.assertEqual(w*dot(v, PRIMAL_VECTOR)**2, 0)

    def test_actual_cancelling_components_match_primal(self):
        f = lambda x: x[0]
        h = lambda x: max(x[0], Q(0))/2-x[0]
        g = lambda x: (Q(1),)
        base, gram, vals = actual_datum(f, h, g, (Q(0),), (Q(1),), (Q(1, 2),), (Q(-1, 2),))
        self.assertEqual(tuple(x[0] for x in base), PRIMAL_VECTOR)
        self.assertEqual(gram, PRIMAL_GRAM)
        self.assertEqual(vals, PRIMAL_VALUES)
        self.assertNotEqual(g((Q(0),)), (Q(0),))

    def test_actual_prox_minimization(self):
        h = lambda x: max(Q(x), Q(0))/2-Q(x)
        x = Q(1, 2)
        self.assertIsInstance(h(0), Q)
        for j in range(-50, 51):
            y = Q(j, 7)
            self.assertLessEqual(h(x)+x*x/2, h(y)+y*y/2)
            self.assertLessEqual(h(x)+Q(-1, 2)*(y-x), h(y))
            self.assertLessEqual(h(0)-y, h(y))

    def test_quadratic_remainder_identity(self):
        for dim in (1, 2, 5):
            v = tuple(Q(j-2, 3) for j in range(dim))
            x = tuple(Q(j+1, 7) for j in range(dim))
            y = tuple(Q(j*j-1, 5) for j in range(dim))
            lhs = dot(sub(y, v), sub(y, v))/2-dot(sub(x, v), sub(x, v))/2+dot(sub(v, x), sub(y, x))
            self.assertEqual(lhs, dot(sub(y, x), sub(y, x))/2)

    def test_positive_segment_argument(self):
        for a in (Q(-1), Q(-7, 9), Q(-1, 10**12)):
            for b in (Q(0), Q(1, 5), Q(100)):
                t = -a/(b-a)
                self.assertTrue(0 < t <= 1)
                self.assertLess(t*a+t*t*b, 0)

    def test_actual_quadratic_plus_l1_family(self):
        # Smooth affine-quadratic part and shifted l1 part have cancelling
        # (possibly nonzero) star subgradients. Every datum uses a real prox.
        for dim in (1, 2, 5):
            for case in range(12):
                center = tuple(Q(j-2, 3) for j in range(dim))
                q = tuple(Q((case+j) % 5, 4) for j in range(dim))
                a = tuple(Q(j+case-3, 7) for j in range(dim))
                lam = tuple(Q((case+2*j) % 4, 10) for j in range(dim))
                u = tuple(Q(((-1)**(j+case))*(j+1), dim*(dim+1)) for j in range(dim))
                f = lambda x: sum((qj*z*z/2+aj*z for qj, aj, z in zip(q, a, sub(x, center), strict=True)), Q(0))
                h = lambda x: sum((lj*abs(z)-aj*z for lj, aj, z in zip(lam, a, sub(x, center), strict=True)), Q(0))
                g = lambda x: tuple(qj*z+aj for qj, aj, z in zip(q, a, sub(x, center), strict=True))
                x0 = add(center, u)
                z = tuple((1-qj)*uj for qj, uj in zip(q, u, strict=True))
                soft = lambda z, l: max(z-l, Q(0)) if z >= 0 else min(z+l, Q(0))
                x1 = add(center, tuple(soft(zj, lj) for zj, lj in zip(z, lam, strict=True)))
                s1 = sub(sub(x0, g(x0)), x1)
                _, gram, vals = actual_datum(f, h, g, center, x0, x1, s1)
                slacks = [e.evaluate(vals, gram) for e in CONSTRAINTS]
                self.assertTrue(all(t >= 0 for t in slacks), (dim, case, slacks))
                gap = OBJECTIVE.evaluate(vals, gram)
                self.assertLessEqual(gap, BOUND)
                self.assertEqual(rhs().evaluate(vals, gram), BOUND-gap)

    def test_legacy_all_slot_interpolation_is_inapplicable(self):
        # Dummy vectors are zero, so legacy slacks are value_i-value_j.
        self.assertTrue(any(a-b < 0 for a in PRIMAL_VALUES for b in PRIMAL_VALUES))
        self.assertTrue(all(e.evaluate(PRIMAL_VALUES, PRIMAL_GRAM) >= 0 for e in CONSTRAINTS))

    def test_wrong_objective_rejected(self):
        self.assertFalse(accepted(objective=value(2)-value(0)))

    def test_smaller_and_larger_bounds_rejected_by_same_identity(self):
        self.assertFalse(accepted(bound=Q(1, 5)))
        self.assertFalse(accepted(bound=Q(1, 3)))

    def test_reverse_ordered_pair_rejected(self):
        cs = list(CONSTRAINTS)
        cs[10] = pair_expr('convex', NONSMOOTH[1], NONSMOOTH[0])
        self.assertFalse(accepted(constraints=cs))

    def test_missing_nonsmooth_constraint_rejected(self):
        cs = list(CONSTRAINTS)
        cs[10] = Expr.zero()
        self.assertFalse(accepted(constraints=cs))

    def test_fictitious_nonsmooth_smoothness_rejected(self):
        cs = CONSTRAINTS[:9] + component_constraints('smooth', NONSMOOTH) + [RADIUS]
        self.assertFalse(accepted(constraints=cs))
        self.assertLess(cs[10].evaluate(PRIMAL_VALUES, PRIMAL_GRAM), 0)

    def test_separate_star_stationarity_rejects_actual_witness(self):
        bad = [replace(NONSMOOTH[0], oracle=ZERO), NONSMOOTH[1]]
        self.assertTrue(any(e.evaluate(PRIMAL_VALUES, PRIMAL_GRAM) < 0
                            for e in component_constraints('convex', bad)))

    def test_omitted_factor_rejected(self):
        for k in range(3):
            self.assertFalse(accepted(factors=FACTORS[:k]+FACTORS[k+1:]))

    def test_negative_weights_rejected(self):
        ts = [(-TERMS[0][0], TERMS[0][1])] + TERMS[1:]
        self.assertFalse(accepted(terms=ts))
        fs = [(-FACTORS[0][0], FACTORS[0][1])] + FACTORS[1:]
        self.assertFalse(accepted(factors=fs))

    def test_implicit_interpolation_requires_explicit_guard(self):
        self.assertFalse(accepted(implicit_terms=((1, 0, 4),)))
        guard_source = (ROOT/'LeanPEP/GramPEP/ExplicitConstraints.lean').read_text(encoding='utf-8')
        self.assertIn('(hempty : c.interpTerms = [])', guard_source)

    def test_tiny_negative_slack_is_not_tolerated(self):
        vals = list(PRIMAL_VALUES)
        vals[4] += Q(1, 10**30)
        self.assertEqual(CONSTRAINTS[10].evaluate(vals, PRIMAL_GRAM), -Q(1, 10**30))

    def test_wrong_residual_update_rejected(self):
        bad_final = sub(U, G0)
        smooth = SMOOTH[:2]+[replace(SMOOTH[2], position=bad_final)]
        nonsmooth = NONSMOOTH[:1]+[replace(NONSMOOTH[1], position=bad_final)]
        cs = component_constraints('smooth', smooth)+component_constraints('convex', nonsmooth)+[RADIUS]
        self.assertFalse(accepted(constraints=cs))

    def test_wrong_function_slot_rejected(self):
        bad = [NONSMOOTH[0], replace(NONSMOOTH[1], slot=2)]
        cs = CONSTRAINTS[:9]+component_constraints('convex', bad)+[RADIUS]
        self.assertFalse(accepted(constraints=cs))


if __name__ == '__main__':
    unittest.main()
