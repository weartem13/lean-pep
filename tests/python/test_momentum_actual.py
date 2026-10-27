"""Exact ambient-function regressions for the v0.13B2 soundness bridge.

These tests independently execute actual oracles, form ambient vectors, and
compare compiled coefficients and Gram slacks.  Fraction arithmetic only;
they do NOT execute or certify the Lean proofs.  Existing B1 constants are
read from the unchanged Lean fixture through its restricted exact parser.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from typing import Callable
import re
import unittest

from tests.python import test_momentum_profile as b1

Vec = list[Q]
Oracle = Callable[[Vec], Vec]
Function = Callable[[Vec], Q]


def add(a: Vec, b: Vec) -> Vec:
    return [x + y for x, y in zip(a, b, strict=True)]


def sub(a: Vec, b: Vec) -> Vec:
    return [x - y for x, y in zip(a, b, strict=True)]


def smul(c: Q, v: Vec) -> Vec:
    return [c * x for x in v]


def inner(a: Vec, b: Vec) -> Q:
    return sum((x * y for x, y in zip(a, b, strict=True)), Q(0))


def realize(coeff: Vec, base: list[Vec]) -> Vec:
    if not base or len(coeff) != len(base):
        raise ValueError("Nonempty ambient vector family and matching coefficients required")
    result = [Q(0)] * len(base[0])
    for c, v in zip(coeff, base, strict=True):
        result = add(result, smul(c, v))
    return result


def actual_run(steps: Vec, betas: Vec, grad: Oracle, initial: Vec,
               *, wrong_oracle_point: bool = False) -> tuple[list[Vec], list[Vec]]:
    if len(steps) != len(betas):
        raise ValueError("Schedule lengths differ")
    states, queries = [initial[:]], [initial[:]]
    for alpha, beta in zip(steps, betas, strict=True):
        old = states[-1]
        g = grad(old if wrong_oracle_point else queries[-1])
        new = sub(queries[-1], smul(alpha, g))
        states.append(new)
        queries.append(add(new, smul(beta, sub(new, old))))
    return states, queries


def quadratic(anchor: Vec, curvature: Vec, offset: Q = Q(0)) -> tuple[Function, Oracle]:
    if len(anchor) != len(curvature) or any(not 0 <= a <= 1 for a in curvature):
        raise ValueError("Use normalized convex diagonal quadratics only")

    def grad(x: Vec) -> Vec:
        return [a * z for a, z in zip(curvature, sub(x, anchor), strict=True)]

    def fun(x: Vec) -> Q:
        z = sub(x, anchor)
        return inner(z, grad(x)) / 2 + offset

    return fun, grad


def huber(threshold: Q, anchor: Q = Q(0), offset: Q = Q(0)) -> tuple[Function, Oracle]:
    """The project's one-sided Huber convention, not the symmetric convention."""
    if threshold < 0:
        raise ValueError("The stationary anchor requires a nonnegative threshold")

    def fun(x: Vec) -> Q:
        if len(x) != 1:
            raise ValueError("Huber regression is one-dimensional")
        z = x[0] - anchor
        return (z*z/2 if z <= threshold else threshold*z - threshold*threshold/2) + offset

    def grad(x: Vec) -> Vec:
        if len(x) != 1:
            raise ValueError("Huber regression is one-dimensional")
        return [min(x[0] - anchor, threshold)]

    return fun, grad


@dataclass
class Datum:
    base: list[Vec]
    positions: list[Vec]
    gradients: list[Vec]
    gram: list[Vec]
    samples: list[Vec]
    values: Vec


def datum(steps: Vec, betas: Vec, f: Function, g: Oracle, anchor: Vec, initial: Vec) -> Datum:
    states, queries = actual_run(steps, betas, g, initial)
    points = queries[:-1] + [states[-1]]
    base = [sub(initial, anchor)] + [g(x) for x in points]
    m = len(base)
    positions = b1.output_positions(steps, betas)
    gradients = [[Q(0)] * m] + [[Q(int(j == i)) for j in range(m)] for i in range(1, m)]
    samples = [anchor] + points
    return Datum(base, positions, gradients,
                 [[inner(u, v) for v in base] for u in base], samples, [f(x) for x in samples])


def gram_inner(G: list[Vec], u: Vec, v: Vec) -> Q:
    return sum((u[i]*G[i][j]*v[j] for i in range(len(u)) for j in range(len(v))), Q(0))


def actual_slack(f: Function, g: Oracle, x: Vec, y: Vec) -> Q:
    dg = sub(g(x), g(y))
    return f(x) - f(y) - inner(g(y), sub(x, y)) - inner(dg, dg)/2


def gram_slack(d: Datum, i: int, j: int) -> Q:
    dg = sub(d.gradients[i], d.gradients[j])
    return d.values[i] - d.values[j] - gram_inner(d.gram, d.gradients[j],
        sub(d.positions[i], d.positions[j])) - gram_inner(d.gram, dg, dg)/2


def pilot_constants() -> tuple[list[tuple[Q, int, int]], list[tuple[Q, Vec]]]:
    src = b1.SOURCE.read_text(encoding="utf-8")
    terms = [(b1.rational(w), int(i), int(j)) for w, i, j in re.findall(
        r"\{\s*weight\s*:=\s*([^,]+),\s*i\s*:=\s*(\d+),\s*j\s*:=\s*(\d+)\s*\}",
        b1.declaration(src, "pilotInterpTermsQ"))]
    factors = [(b1.rational(w), b1.vector(v)) for w, v in re.findall(
        r"\{\s*weight\s*:=\s*([^,]+),\s*vector\s*:=\s*!\[([^\]]+)\]\s*\}",
        b1.declaration(src, "pilotDualFactorsQ"))]
    if len(terms) != 9 or len(factors) != 11:
        raise ValueError("Unexpected B1 fixture structure")
    return terms, factors


class MomentumActualTests(unittest.TestCase):
    def test_actual_oracle_recurrence_realizes_both_affine_sequences(self) -> None:
        for dim in (1, 2, 5):
            anchor = [Q(j-2, 3) for j in range(dim)]
            initial = [a + Q(j+1, 7) for j, a in enumerate(anchor)]
            _, g = quadratic(anchor, [Q(j+1, dim+2) for j in range(dim)])
            for n in range(13):
                steps = [Q((k*7)%9-3, k%4+1) for k in range(n)]
                betas = [Q((k*5)%11-5, k%3+1) for k in range(n)]
                states, queries = actual_run(steps, betas, g, initial)
                rows_x, rows_y = b1.coefficient_rows(steps, betas)
                points = queries[:-1] + [states[-1]]
                base = [sub(initial, anchor)] + [g(p) for p in points]
                for k in range(n+1):
                    self.assertEqual(realize([Q(1)]+[-c for c in rows_x[k]], base), sub(states[k], anchor))
                    self.assertEqual(realize([Q(1)]+[-c for c in rows_y[k]], base), sub(queries[k], anchor))

    def test_zero_horizon_is_initial_state_and_its_gradient(self) -> None:
        anchor, initial = [Q(2)], [Q(5, 2)]
        f, g = quadratic(anchor, [Q(1, 3)], Q(7))
        d = datum([], [], f, g, anchor, initial)
        self.assertEqual(d.samples, [anchor, initial])
        self.assertEqual(d.base, [sub(initial, anchor), g(initial)])
        self.assertEqual(d.values[-1]-d.values[0], f(initial)-f(anchor))

    def test_positions_and_gradients_realize_all_samples(self) -> None:
        for n in range(10):
            anchor, initial = [Q(3), Q(-2)], [Q(7, 2), Q(-5, 3)]
            f, g = quadratic(anchor, [Q(1, 3), Q(4, 5)])
            d = datum([Q(1)]*n, [Q(k, k+3) for k in range(n)], f, g, anchor, initial)
            for i, point in enumerate(d.samples):
                self.assertEqual(realize(d.positions[i], d.base), sub(point, anchor))
                self.assertEqual(realize(d.gradients[i], d.base), g(point))

    def test_gram_bilinear_is_actual_inner_product(self) -> None:
        f, g = quadratic([Q(0), Q(0), Q(0)], [Q(0), Q(1, 4), Q(1)])
        d = datum([Q(1)]*4, [Q(k, k+3) for k in range(4)], f, g,
                  [Q(0)]*3, [Q(1, 3)]*3)
        for k in range(25):
            u = [Q((j*3+k)%11-5, 7) for j in range(6)]
            v = [Q((j*7+k)%13-6, 9) for j in range(6)]
            self.assertEqual(gram_inner(d.gram, u, v), inner(realize(u, d.base), realize(v, d.base)))
            self.assertGreaterEqual(gram_inner(d.gram, u, u), 0)

    def test_all_ordered_slacks_equal_actual_function_slacks(self) -> None:
        for n in range(9):
            anchor, initial = [Q(2, 3), Q(-4, 5)], [Q(5, 6), Q(-1, 5)]
            f, g = quadratic(anchor, [Q(1, 3), Q(4, 5)], Q(11, 7))
            d = datum([Q(2, 3)]*n, [Q(k-3, k+4) for k in range(n)], f, g, anchor, initial)
            for i, x in enumerate(d.samples):
                for j, y in enumerate(d.samples):
                    self.assertEqual(gram_slack(d, i, j), actual_slack(f, g, x, y))
                    self.assertGreaterEqual(gram_slack(d, i, j), 0)

    def test_radius_is_inequality_not_equality(self) -> None:
        anchor, initial = [Q(1), Q(2)], [Q(5, 4), Q(7, 3)]
        f, g = quadratic(anchor, [Q(1, 2), Q(1, 3)])
        d = datum([Q(1)]*4, [Q(k, k+3) for k in range(4)], f, g, anchor, initial)
        self.assertEqual(Q(1)-d.gram[0][0], Q(1)-inner(sub(initial, anchor), sub(initial, anchor)))
        self.assertGreater(Q(1)-d.gram[0][0], 0)

    def test_zero_radius_and_zero_gram_are_supported(self) -> None:
        anchor = [Q(3), Q(-5)]
        f, g = quadratic(anchor, [Q(1, 7), Q(1, 2)], Q(17))
        d = datum([Q(1)]*4, [Q(k, k+3) for k in range(4)], f, g, anchor, anchor)
        self.assertTrue(all(x == anchor for x in d.samples))
        self.assertTrue(all(entry == 0 for row in d.gram for entry in row))
        self.assertEqual(d.values[-1]-d.values[0], 0)

    def test_translation_and_function_offset_invariance(self) -> None:
        a, x = [Q(0), Q(0)], [Q(2, 5), Q(-1, 3)]
        shift = [Q(13, 4), Q(-9, 2)]
        f0, g0 = quadratic(a, [Q(1, 3), Q(3, 4)])
        f1, g1 = quadratic(shift, [Q(1, 3), Q(3, 4)], Q(-31, 7))
        args = ([Q(1)]*4, [Q(k, k+3) for k in range(4)])
        d0, d1 = datum(*args, f0, g0, a, x), datum(*args, f1, g1, shift, add(x, shift))
        self.assertEqual(d0.gram, d1.gram)
        self.assertEqual(d0.values[-1]-d0.values[0], d1.values[-1]-d1.values[0])
        for i in range(6):
            for j in range(6):
                self.assertEqual(gram_slack(d0, i, j), gram_slack(d1, i, j))

    def test_arbitrary_gap_objectives_have_declared_semantics(self) -> None:
        f, g = quadratic([Q(2)], [Q(2, 3)], Q(8, 5))
        d = datum([Q(1)]*4, [Q(k, k+3) for k in range(4)], f, g, [Q(2)], [Q(5, 2)])
        for target in range(6):
            for reference in range(6):
                self.assertEqual(d.values[target]-d.values[reference],
                                 f(d.samples[target])-f(d.samples[reference]))

    def test_last_momentum_does_not_change_actual_output(self) -> None:
        _, g = quadratic([Q(0)], [Q(2, 3)])
        for n in range(1, 13):
            betas = [Q(k, k+3) for k in range(n)]
            x, y = actual_run([Q(1)]*n, betas, g, [Q(1)])
            betas[-1] = Q(-79, 11)
            xx, yy = actual_run([Q(1)]*n, betas, g, [Q(1)])
            self.assertEqual(x[-1], xx[-1])
            self.assertEqual(y[:-1], yy[:-1])

    def test_state_oracle_mutation_breaks_realization(self) -> None:
        _, g = quadratic([Q(0)], [Q(3, 7)])
        steps, betas = [Q(1)]*4, [Q(k, k+3) for k in range(4)]
        x, y = actual_run(steps, betas, g, [Q(1)], wrong_oracle_point=True)
        points = y[:-1]+[x[-1]]
        base = [[Q(1)]]+[g(p) for p in points]
        expected = realize(b1.output_positions(steps, betas)[-1], base)
        self.assertNotEqual(expected, x[-1])

    def test_swapped_basis_mutation_breaks_realization(self) -> None:
        f, g = quadratic([Q(0)], [Q(3, 7)])
        d = datum([Q(1)]*4, [Q(k, k+3) for k in range(4)], f, g, [Q(0)], [Q(1)])
        base = [v[:] for v in d.base]
        base[1], base[2] = base[2], base[1]
        self.assertNotEqual(realize(d.positions[2], base), d.samples[2])

    def test_terminal_query_mutation_breaks_realization(self) -> None:
        f, g = quadratic([Q(0)], [Q(3, 7)])
        steps, betas = [Q(1)]*4, [Q(k, k+3) for k in range(4)]
        d = datum(steps, betas, f, g, [Q(0)], [Q(1)])
        _, queries = actual_run(steps, betas, g, [Q(1)])
        self.assertNotEqual(realize(d.positions[-1], d.base), queries[-1])

    def test_nonstationary_reference_cannot_realize_zero_gradient(self) -> None:
        f, g = quadratic([Q(0)], [Q(2, 3)])
        d = datum([Q(1)]*4, [Q(k, k+3) for k in range(4)], f, g, [Q(1)], [Q(3, 2)])
        self.assertNotEqual(realize(d.gradients[0], d.base), g(d.samples[0]))

    def test_reference_centering_is_required(self) -> None:
        f, g = quadratic([Q(3)], [Q(3, 7)])
        d = datum([Q(1)]*4, [Q(k, k+3) for k in range(4)], f, g, [Q(3)], [Q(7, 2)])
        bad_base = [[Q(7, 2)]] + d.base[1:]
        self.assertNotEqual(realize(d.positions[-1], bad_base), sub(d.samples[-1], [Q(3)]))


class NesterovActualCertificateTests(unittest.TestCase):
    def check_actual_certificate(self, f: Function, g: Oracle, anchor: Vec, initial: Vec) -> Q:
        d = datum([Q(1)]*4, [Q(k, k+3) for k in range(4)], f, g, anchor, initial)
        terms, factors = pilot_constants()
        interpolation = sum((w*gram_slack(d, i, j) for w, i, j in terms), Q(0))
        radius = (Q(1)-d.gram[0][0])/21
        dual = sum((w*inner(realize(v, d.base), realize(v, d.base)) for w, v in factors), Q(0))
        self.assertEqual(Q(1, 21)-(d.values[-1]-d.values[0]), interpolation+radius+dual)
        for i in range(6):
            for j in range(6):
                self.assertGreaterEqual(gram_slack(d, i, j), 0)
        self.assertGreaterEqual(interpolation, 0)
        self.assertGreaterEqual(radius, 0)
        self.assertGreaterEqual(dual, 0)
        gap = d.values[-1]-d.values[0]
        self.assertLessEqual(gap, Q(1, 21))
        return gap

    def test_quadratic_actual_function_certificate(self) -> None:
        for curvature in (Q(0), Q(1, 17), Q(1, 3), Q(3, 4), Q(1)):
            for radius in (Q(0), Q(1, 5), Q(1, 2), Q(1)):
                f, g = quadratic([Q(2)], [curvature], Q(7, 9))
                self.check_actual_certificate(f, g, [Q(2)], [Q(2)+radius])

    def test_multidimensional_actual_function_certificate(self) -> None:
        for dim in (2, 3, 5):
            anchor = [Q(j-2, 3) for j in range(dim)]
            initial = [a+Q(1, dim) for a in anchor]
            f, g = quadratic(anchor, [Q(j+1, dim+2) for j in range(dim)], Q(-2))
            self.check_actual_certificate(f, g, anchor, initial)

    def test_huber_actual_execution_matches_finite_primal(self) -> None:
        # An exact regression only: B2 deliberately contains no Lean lower theorem.
        f, g = huber(Q(2, 21))
        gap = self.check_actual_certificate(f, g, [Q(0)], [Q(1)])
        self.assertEqual(gap, Q(1, 21))
        d = datum([Q(1)]*4, [Q(k, k+3) for k in range(4)], f, g, [Q(0)], [Q(1)])
        self.assertEqual(d.values, [Q(0), Q(40, 441), Q(4, 49), Q(31, 441), Q(25, 441), Q(1, 21)])
        self.assertEqual(d.samples[-1], [Q(23, 42)])

    def test_huber_across_piecewise_branches(self) -> None:
        for threshold in (Q(0), Q(1, 50), Q(1, 3), Q(2, 3), Q(1), Q(2)):
            for initial in (Q(-1), Q(-1, 2), Q(0), Q(1, 2), Q(1)):
                f, g = huber(threshold, Q(3), Q(7))
                self.check_actual_certificate(f, g, [Q(3)], [Q(3)+initial])

    def test_dimension_mismatch_fails_instead_of_silent_truncation(self) -> None:
        with self.assertRaises(ValueError):
            inner([Q(1)], [Q(1), Q(2)])
        with self.assertRaises(ValueError):
            realize([Q(1)], [[Q(1)], [Q(2)]])


if __name__ == "__main__":
    unittest.main()
