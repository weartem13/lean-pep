"""C5 independent exact regressions, not a Lean elaborator.

Global minimizers and prox points below are obtained from closed formulas for
separable quadratic-plus-absolute-value functions. Finite comparison grids
are diagnostic only: they are not proofs of arbitrary global minimality.
The existing C4 normalization and C3A certificate mirrors are reused unchanged.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from pathlib import Path
import unittest

from tests.python import test_composite_proximal as c1
from tests.python import test_proximal_gradient_profile as pg
from tests.python import test_proximal_gradient_certificate as cert
from tests.python import test_proximal_gradient_scaling as c4

ROOT = Path(__file__).resolve().parents[2]
OPT = (ROOT / 'LeanPEP/ActualFunction/CompositeOptimality.lean').read_text()
RATE = (ROOT / 'LeanPEP/ActualFunction/ProximalGradientMinimizer.lean').read_text() + "\n" + (ROOT / 'LeanPEP/ActualFunction/ProximalGradientMinimizerCore.lean').read_text()
Vec = tuple[Q, ...]


@dataclass(frozen=True)
class Example:
    curvature: Vec
    linear: Vec
    tilt: Vec
    lam: Vec
    shift: Vec
    f_offset: Q = Q(7, 3)
    h_offset: Q = Q(-11, 5)

    def f(self, x: Vec) -> Q:
        return self.f_offset + sum((d*z*z/2 + a*z for d, a, z in
                                    zip(self.curvature, self.linear, x, strict=True)), Q(0))

    def g(self, x: Vec) -> Vec:
        return tuple(d*z+a for d, a, z in zip(self.curvature, self.linear, x, strict=True))

    def h(self, x: Vec) -> Q:
        return self.h_offset + sum((b*abs(z-c)+t*z for b, c, t, z in
                                    zip(self.lam, self.shift, self.tilt, x, strict=True)), Q(0))

    def prox(self, v: Vec, K: Q) -> Vec:
        if K <= 0:
            raise ValueError('Positive inverse step size required')
        return tuple(c+pg.soft(z-c-t/K, b/K) for c, z, t, b in
                     zip(self.shift, v, self.tilt, self.lam, strict=True))

    def minimum(self) -> Vec:
        answer = []
        for d, a, t, b, c in zip(self.curvature, self.linear, self.tilt,
                                  self.lam, self.shift, strict=True):
            if d == 0:
                if abs(a+t) > b:
                    raise ValueError('Unbounded composite coordinate')
                answer.append(c)
            else:
                answer.append(c+pg.soft(-c-(a+t)/d, b/d))
        return tuple(answer)

    def supports(self, x: Vec, s: Vec) -> bool:
        for z, q, c, t, b in zip(x, s, self.shift, self.tilt, self.lam, strict=True):
            q -= t
            if z == c:
                if not -b <= q <= b:
                    return False
            elif q != (b if z > c else -b):
                return False
        return True


def example(dim: int, L: Q) -> Example:
    if dim < 1 or L < 0:
        raise ValueError('Invalid dimension or smoothness')
    ds = tuple(L*Q(j+1, dim+1) for j in range(dim))
    tilt = tuple(Q(2*j+1, 5) for j in range(dim))
    linear = tuple(-t if L == 0 else Q(1-3*j, 2) for j, t in enumerate(tilt))
    return Example(ds, linear, tilt, tuple(Q(j+1, 4) for j in range(dim)),
                   tuple(Q(j-2, 3) for j in range(dim)))


def probes(dim: int):
    for k in range(-5, 6):
        yield tuple(Q(k*(j+1)-j, 3) for j in range(dim))


def run(ex: Example, L: Q, x0: Vec, T: int) -> list[Vec]:
    if L <= 0 or T < 0:
        raise ValueError('Invalid physical run')
    xs = [x0]
    for _ in range(T):
        xs.append(ex.prox(c1.sub(xs[-1], c1.scale(1/L, ex.g(xs[-1]))), L))
    return xs


class CompositeMinimizerTests(unittest.TestCase):
    def test_source_reuses_unit_optimality_and_normalization(self):
        self.assertIn('subgradient_of_isUnitProxPoint hconv hprox', OPT)
        self.assertIn('normalized_prox_iff hL', OPT)
        self.assertIn('normalizedFunction_convex', OPT)
        self.assertNotIn('axiom ', OPT)

    def test_source_auxiliary_curvature_is_not_physical_step(self):
        self.assertIn('let K : ℝ≥0 := L + 1', OPT)
        self.assertNotIn('L + 1', RATE)
        self.assertIn('IsSmoothProxRun T L h g x', RATE)

    def test_source_certificate_guards_and_old_rate(self):
        for guard in ('GramPEP.checkUpperCertQ c = true', 'c.interpTerms = []',
                      'c.objective = Profiles.ProximalGradient.objectiveQ n'):
            self.assertIn(guard, RATE)
        self.assertIn('upper_analytic_steps T hT hf hh hL hR', RATE)
        self.assertIn('ProximalGradientWitnessScaling.analytic_tight_all n hL hR', RATE)

    def test_source_new_value_set_uses_minimum_not_certificate(self):
        block = RATE.split('def oneDimensionalMinimizerValues', 1)[1].split('/--', 1)[0]
        self.assertIn('(∀ y, f xStar + h xStar ≤ f y + h y)', block)
        self.assertNotIn('SubgradientAt', block)
        self.assertNotIn('GramPEP', block)
        self.assertIn('oneDimensionalMinimizerValues_eq_analyticValues', RATE)

    def test_prox_residual_is_exact_subgradient(self):
        for dim in (1, 2, 5):
            ex = example(dim, Q(3))
            for K in (Q(1, 5), Q(1), Q(7, 2)):
                for v in probes(dim):
                    x = ex.prox(v, K)
                    self.assertTrue(ex.supports(x, c1.scale(K, c1.sub(v, x))))

    def test_prox_objective_support_remainder(self):
        for dim in (1, 2, 5):
            ex = example(dim, Q(3))
            for K in (Q(1, 5), Q(1), Q(7, 2)):
                v = tuple(Q(j-3, 7) for j in range(dim))
                x = ex.prox(v, K)
                s = c1.scale(K, c1.sub(v, x))
                for y in probes(dim):
                    diff = ex.h(y)+K*c4.norm2(c1.sub(y, v))/2-ex.h(x)-K*c4.norm2(c1.sub(x, v))/2
                    support = ex.h(y)-ex.h(x)-c1.dot(s, c1.sub(y, x))
                    self.assertGreaterEqual(support, 0)
                    self.assertEqual(diff, support+K*c4.norm2(c1.sub(y, x))/2)

    def test_normalized_subgradient_clearing(self):
        for dim in (1, 2, 5):
            ex = example(dim, Q(3))
            zero = (Q(0),)*dim
            for K in (Q(1, 5), Q(7, 2)):
                v = tuple(Q(j-3, 7) for j in range(dim))
                x = ex.prox(v, K)
                for y in probes(dim):
                    normalized = (ex.h(y)-ex.h(zero))/K-(ex.h(x)-ex.h(zero))/K-c1.dot(c1.sub(v, x), c1.sub(y, x))
                    physical = ex.h(y)-ex.h(x)-c1.dot(c1.scale(K, c1.sub(v, x)), c1.sub(y, x))
                    self.assertEqual(K*normalized, physical)
                    self.assertGreaterEqual(physical, 0)

    def test_auxiliary_quadratic_identity_for_arbitrary_reference(self):
        for dim in (1, 2, 5):
            x = tuple(Q(j-1, 3) for j in range(dim))
            a = tuple(Q(2*j+1, 7) for j in range(dim))
            for K in (Q(1, 3), Q(1), Q(5)):
                v = c1.sub(x, c1.scale(1/K, a))
                self.assertEqual(c1.scale(K, c1.sub(v, x)), c1.scale(Q(-1), a))
                for y in probes(dim):
                    self.assertEqual(K*(c4.norm2(c1.sub(y, v))-c4.norm2(c1.sub(x, v)))/2,
                                     c1.dot(a, c1.sub(y, x))+K*c4.norm2(c1.sub(y, x))/2)

    def test_closed_minimum_global_comparison_grid(self):
        for dim in (1, 2, 5):
            for L in (Q(0), Q(1, 4), Q(3), Q(7)):
                ex = example(dim, L)
                x = ex.minimum()
                for y in probes(dim):
                    self.assertLessEqual(ex.f(x)+ex.h(x), ex.f(y)+ex.h(y))

    def test_upper_model_at_minimum(self):
        for dim in (1, 2, 5):
            for L in (Q(0), Q(1, 4), Q(3), Q(7)):
                ex = example(dim, L)
                x = ex.minimum()
                for y in probes(dim):
                    self.assertLessEqual(ex.f(y), ex.f(x)+c1.dot(ex.g(x), c1.sub(y, x))+L*c4.norm2(c1.sub(y, x))/2)

    def test_L_plus_one_majorizer(self):
        for dim in (1, 2, 5):
            for L in (Q(0), Q(1, 4), Q(3)):
                ex = example(dim, L)
                x = ex.minimum()
                for y in probes(dim):
                    self.assertLessEqual(ex.h(x), ex.h(y)+c1.dot(ex.g(x), c1.sub(y, x))+(L+1)*c4.norm2(c1.sub(y, x))/2)

    def test_minimum_supplies_exact_support(self):
        for dim in (1, 2, 5):
            for L in (Q(0), Q(1, 4), Q(3), Q(7)):
                ex = example(dim, L)
                x = ex.minimum()
                self.assertTrue(ex.supports(x, c1.scale(Q(-1), ex.g(x))))

    def test_minimum_is_fixed_point_for_all_positive_penalties(self):
        for dim in (1, 2, 5):
            for L in (Q(0), Q(1, 4), Q(3)):
                ex = example(dim, L)
                x = ex.minimum()
                for K in (Q(1, 5), Q(1), Q(7), L+1):
                    self.assertEqual(ex.prox(c1.sub(x, c1.scale(1/K, ex.g(x))), K), x)

    def test_zero_smoothness_uses_nonzero_canceling_vectors(self):
        ex = example(5, Q(0))
        x = ex.minimum()
        self.assertNotEqual(ex.g(x), (Q(0),)*5)
        self.assertTrue(ex.supports(x, c1.scale(Q(-1), ex.g(x))))
        self.assertEqual(ex.prox(c1.sub(x, ex.g(x)), Q(1)), x)

    def test_independent_offsets_do_not_change_minimizer(self):
        ex = example(2, Q(3))
        shifted = Example(ex.curvature, ex.linear, ex.tilt, ex.lam, ex.shift, Q(101), Q(-77))
        x = ex.minimum()
        self.assertEqual(shifted.minimum(), x)
        for y in probes(2):
            self.assertEqual(ex.f(y)+ex.h(y)-ex.f(x)-ex.h(x),
                             shifted.f(y)+shifted.h(y)-shifted.f(x)-shifted.h(x))

    def test_starting_at_minimum_fixes_supplied_run(self):
        for dim in (1, 2, 5):
            for L in (Q(1, 4), Q(3), Q(7)):
                ex = example(dim, L)
                x = ex.minimum()
                self.assertEqual(run(ex, L, x, 32), [x]*33)

    def test_existing_rate_at_closed_form_minimum(self):
        for dim in (1, 2, 5):
            for L in (Q(1, 4), Q(3)):
                ex = example(dim, L)
                star = ex.minimum()
                for R in (Q(0), Q(2, 3), Q(2)):
                    x0 = c1.add(star, tuple(R*Q(1, dim*(j+1)) for j in range(dim)))
                    xs = run(ex, L, x0, 12)
                    for T in range(1, 13):
                        self.assertLessEqual(ex.f(xs[T])+ex.h(xs[T])-ex.f(star)-ex.h(star), L*R**2/(4*T))

    def test_existing_certificate_on_minimizer_based_actual_data(self):
        for dim in (1, 2):
            L, R = Q(3), Q(2)
            ex = example(dim, L)
            star = ex.minimum()
            x0 = c1.add(star, tuple(R*Q(1, dim*(j+1)) for j in range(dim)))
            for T in range(1, 7):
                xs = run(ex, L, x0, T)
                *_, values, gram = c4.normalized_data(T, L, R, ex.f, ex.h, ex.g, star, xs)
                constraints, objective = pg.compile_profile(T-1)
                self.assertTrue(all(cert.ev(e, values, gram) >= 0 for e in constraints))
                rhs, target = cert.candidate(T)
                self.assertEqual(cert.ev(rhs, values, gram), cert.ev(target, values, gram))
                self.assertLessEqual(cert.ev(objective, values, gram), Q(1, 4*T))

    def test_existing_witness_is_global_minimum_and_attains(self):
        for T in range(1, 33):
            for L in (Q(1, 3), Q(3)):
                for R in (Q(0), Q(2, 3), Q(2)):
                    a, f, h, g, prox, xs = c4.witness(T, L, R)
                    for j in range(-3, 4):
                        self.assertLessEqual(f(Q(0))+h(Q(0)), f(Q(j))+h(Q(j)))
                    self.assertEqual(xs[-1], R/2)
                    self.assertEqual(f(xs[-1])+h(xs[-1])-f(Q(0))-h(Q(0)), L*R**2/(4*T))

    def test_no_separate_component_minimum(self):
        _, f, h, g, _, _ = c4.witness(4, Q(3), Q(2))
        self.assertNotEqual(g(Q(0)), 0)
        self.assertLess(f(Q(-1)), f(Q(0)))
        self.assertLess(h(Q(1)), h(Q(0)))
        self.assertGreaterEqual(f(Q(1))+h(Q(1)), f(Q(0))+h(Q(0)))

    def test_wrong_sign_support_rejected(self):
        ex = example(2, Q(0))
        x = ex.minimum()
        self.assertTrue(ex.supports(x, c1.scale(Q(-1), ex.g(x))))
        self.assertFalse(ex.supports(x, ex.g(x)))

    def test_convexity_cannot_be_omitted_from_necessity(self):
        # f=x^2, h=-x^2 has constant composite objective. At x=1 the
        # proposed supporting vector -f'(1)=-2 is NOT a global support of h.
        x, y = Q(1), Q(0)
        f, h = lambda z: z*z, lambda z: -z*z
        self.assertEqual(f(x)+h(x), f(y)+h(y))
        self.assertGreater(h(x)-2*(y-x), h(y))

    def test_smooth_upper_model_cannot_be_omitted(self):
        # f=abs(x), h=-x at x=0. Taking the wrong "gradient" 0 cannot
        # satisfy any finite quadratic upper model near zero.
        for L in (Q(0), Q(1), Q(7)):
            y = 1/(L+1)
            self.assertGreater(abs(y), L*y*y/2)
            self.assertGreater(Q(0), -y)

    def test_positive_penalty_needed_for_prox_uniqueness(self):
        # h=0 and L=0: all points minimize the subproblem, and uniqueness fails.
        x, y, v = Q(0), Q(1), Q(3)
        self.assertNotEqual(x, y)
        self.assertEqual(Q(0)*(x-v)**2/2, Q(0)*(y-v)**2/2)
        with self.assertRaises(ValueError):
            example(1, Q(0)).prox((v,), Q(0))


if __name__ == '__main__':
    unittest.main()
