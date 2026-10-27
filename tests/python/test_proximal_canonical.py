"""C6 exact semantic regressions. Not a Lean elaborator or an existence proof.

Closed-form exact prox maps for separable real convex functions independently
exercise the proposed selection/trajectory semantics and the old certificates.
Finite grids only diagnose inequalities; compactness is a Lean proof obligation.
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
from tests.python import test_composite_minimizer as c5

ROOT = Path(__file__).resolve().parents[2]
EXIST = (ROOT / 'LeanPEP/ActualFunction/ProximalExistence.lean').read_text()
ITER = (ROOT / 'LeanPEP/ActualFunction/ProximalIteration.lean').read_text()
RATE = (ROOT / 'LeanPEP/ActualFunction/ProximalGradientCanonical.lean').read_text()
Vec = tuple[Q, ...]

@dataclass(frozen=True)
class Penalty:
    curvature: Vec
    lam: Vec
    tilt: Vec
    shift: Vec
    offset: Q = Q(-7, 3)

    def __post_init__(self):
        if len({len(self.curvature), len(self.lam), len(self.tilt), len(self.shift)}) != 1:
            raise ValueError('Coefficient dimensions must agree')
        if any(a < 0 for a in self.curvature + self.lam):
            raise ValueError('Convex coefficients must be nonnegative')

    def h(self, x: Vec) -> Q:
        if len(x) != len(self.curvature):
            raise ValueError('Input dimension mismatch')
        return self.offset + sum((a*(z-d)**2/2+b*abs(z-d)+t*(z-d)
            for a, b, t, d, z in zip(self.curvature, self.lam, self.tilt, self.shift, x, strict=True)), Q(0))

    def prox(self, v: Vec, L: Q) -> Vec:
        if L <= 0 or len(v) != len(self.curvature):
            raise ValueError('Positive inverse step and correct dimension required')
        return tuple(d+pg.soft(L*(z-d)-t, b)/(L+a)
            for a, b, t, d, z in zip(self.curvature, self.lam, self.tilt, self.shift, v, strict=True))

    def supports(self, x: Vec, s: Vec) -> bool:
        for a, b, t, d, z, q in zip(self.curvature, self.lam, self.tilt, self.shift, x, s, strict=True):
            w = z-d
            residual = q-a*w-t
            if w == 0:
                if not -b <= residual <= b:
                    return False
            elif residual != (b if w > 0 else -b):
                return False
        return True

    def objective(self, v: Vec, L: Q, z: Vec) -> Q:
        return self.h(z)+L*c4.norm2(c1.sub(z, v))/2


def penalty(dim: int) -> Penalty:
    return Penalty(tuple(Q(j % 3, 4) for j in range(dim)),
                   tuple(Q(j+1, 5) for j in range(dim)),
                   tuple(Q(2*j-3, 3) for j in range(dim)),
                   tuple(Q(1-j, 7) for j in range(dim)))


def iterate(prox, g, L: Q, x0: Vec, N: int) -> list[Vec]:
    if L <= 0 or N < 0:
        raise ValueError('Invalid inverse step or horizon')
    xs = [x0]
    for _ in range(N):
        xs.append(prox(c1.sub(xs[-1], c1.scale(1/L, g(xs[-1]))), L))
    return xs


class ProximalCanonicalTests(unittest.TestCase):
    def test_source_existence_has_real_compactness_and_no_assumed_support(self):
        self.assertIn('hh.continuousOn isOpen_univ', EXIST)
        self.assertIn('exists_isMaxOn', EXIST)
        self.assertIn('exists_isMinOn', EXIST)
        self.assertIn('[FiniteDimensional ℝ E]', EXIST)
        self.assertIn('isProxPoint_unique hL hh hx hy', EXIST)
        head = EXIST.split('theorem exists_isProxPoint', 1)[1].split(':= by', 1)[0]
        self.assertNotIn('SubgradientAt', head)
        self.assertNotIn('Continuous', head)

    def test_source_selection_is_proof_carrying_without_fallback(self):
        block = ITER.split('def proxMap', 1)[1].split('theorem proxMap_spec', 1)[0]
        self.assertIn('Classical.choose (hp v)', block)
        self.assertNotIn('else', block)
        self.assertIn('proxMap_eq_of_selector', ITER)

    def test_source_reuses_run_and_all_certificate_guards(self):
        for term in ('GramPEP.checkUpperCertQ c = true', 'c.interpTerms = []',
                     'c.objective = Profiles.ProximalGradient.objectiveQ n'):
            self.assertIn(term, RATE)
        self.assertIn('ProximalGradientScaling.upper_analytic_steps_of_minimizer', RATE)
        self.assertIn('isProxPoint_unique', ITER)
        self.assertIn('revert hk', ITER)

    def test_source_value_set_has_selected_iterate_not_free_run(self):
        block = RATE.split('def oneDimensionalValues', 1)[1].split('/--', 1)[0]
        self.assertIn('(hp : HasProx L h)', block)
        self.assertIn('iterate hp g x0', block)
        for term in ('IsSmoothProxRun', 'GramPEP', '(x : ℕ → ℝ)', 'SubgradientAt'):
            self.assertNotIn(term, block)
        self.assertIn('oneDimensionalValues_eq_minimizerValues', RATE)

    def test_exact_prox_residuals_support(self):
        for dim in (0, 1, 2, 5):
            h = penalty(dim)
            for L in (Q(1, 7), Q(1), Q(3)):
                for v in c5.probes(dim):
                    x = h.prox(v, L)
                    self.assertTrue(h.supports(x, c1.scale(L, c1.sub(v, x))))

    def test_exact_global_support_and_strict_quadratic_remainder(self):
        for dim in (1, 2, 5):
            h = penalty(dim)
            for L in (Q(1, 4), Q(1), Q(5, 2)):
                v = tuple(Q(j-3, 7) for j in range(dim))
                x = h.prox(v, L)
                s = c1.scale(L, c1.sub(v, x))
                for y in c5.probes(dim):
                    slack = h.h(y)-h.h(x)-c1.dot(s, c1.sub(y, x))
                    self.assertGreaterEqual(slack, 0)
                    gap = h.objective(v, L, y)-h.objective(v, L, x)
                    self.assertEqual(gap, slack+L*c4.norm2(c1.sub(y, x))/2)
                    if y != x:
                        self.assertGreater(gap, 0)

    def test_scalar_radial_lower_bound_from_unit_ball_maximum(self):
        for a in (Q(0), Q(1, 3), Q(2)):
            h = Penalty((a,), (Q(2, 5),), (Q(-3, 2),), (Q(4, 7),))
            for v in (Q(-2), Q(0), Q(5, 3)):
                M = max(h.h((v-1,)), h.h((v+1,)))
                C = M-h.h((v,))
                self.assertGreaterEqual(C, 0)
                for k in range(-60, 61):
                    x = Q(k, 7)
                    self.assertLessEqual(h.h((v,))-C*abs(x-v), h.h((x,)))
                    if x != v:
                        r = abs(x-v)
                        y = v-(x-v)/r
                        self.assertEqual(x/(r+1)+r*y/(r+1), v)
                        self.assertLessEqual(h.h((y,)), M)

    def test_compact_radius_dominates_all_sampled_outside_points(self):
        h = penalty(1)
        for v in (Q(-2), Q(0), Q(7, 3)):
            C = max(h.h((v-1,)), h.h((v+1,)))-h.h((v,))
            for L in (Q(1, 9), Q(1), Q(9)):
                radius = 2*C/L+1
                x = h.prox((v,), L)[0]
                self.assertLessEqual(abs(x-v), radius)
                for sign in (-1, 1):
                    for extra in (Q(1, 10), Q(1), Q(20)):
                        y = (v+sign*(radius+extra),)
                        self.assertLessEqual(h.h((v,)), h.objective((v,), L, y))

    def test_unbounded_below_component_still_has_prox(self):
        h = Penalty((Q(0),), (Q(0),), (Q(-3),), (Q(0),))
        for L in (Q(1, 3), Q(1), Q(4)):
            for v in (Q(-2), Q(0), Q(7)):
                self.assertEqual(h.prox((v,), L), (v+3/L,))
        self.assertLess(h.h((Q(1000),)), h.h((Q(0),)))

    def test_zero_dimensional_space(self):
        h = penalty(0)
        self.assertEqual(h.prox((), Q(2)), ())
        self.assertEqual(iterate(h.prox, lambda _: (), Q(2), (), 64), [()]*65)

    def test_coherent_prefixes_and_nonpositive_horizon_validation(self):
        h = penalty(3)
        g = lambda x: tuple(z/2 for z in x)
        x0 = (Q(1), Q(-2), Q(3))
        long = iterate(h.prox, g, Q(2), x0, 32)
        for N in range(33):
            self.assertEqual(iterate(h.prox, g, Q(2), x0, N), long[:N+1])
        self.assertEqual(iterate(h.prox, g, Q(2), x0, 0), [x0])
        with self.assertRaises(ValueError):
            iterate(h.prox, g, Q(2), x0, -1)

    def test_independent_constant_offsets_do_not_change_selected_run(self):
        for dim in (1, 2, 5):
            ex = c5.example(dim, Q(3))
            shifted = c5.Example(ex.curvature, ex.linear, ex.tilt, ex.lam, ex.shift, Q(31), Q(-51))
            x0 = next(c5.probes(dim))
            self.assertEqual(iterate(ex.prox, ex.g, Q(3), x0, 12),
                             iterate(shifted.prox, shifted.g, Q(3), x0, 12))

    def test_constructed_run_equals_existing_c5_actual_run(self):
        for dim in (1, 2, 5):
            for L in (Q(1, 5), Q(1), Q(7, 2)):
                ex = c5.example(dim, L)
                for T in (0, 1, 2, 8, 16):
                    x0 = next(c5.probes(dim))
                    self.assertEqual(iterate(ex.prox, ex.g, L, x0, T), c5.run(ex, L, x0, T))

    def test_minimizer_fixed_point_with_nonzero_component_gradient(self):
        for dim in (1, 2, 5):
            ex = c5.example(dim, Q(3))
            xStar = ex.minimum()
            self.assertNotEqual(ex.g(xStar), (Q(0),)*dim)
            self.assertEqual(iterate(ex.prox, ex.g, Q(3), xStar, 32), [xStar]*33)

    def test_old_certificate_on_canonical_data(self):
        for T in (1, 2, 4, 8):
            for dim in (1, 2, 5):
                L, R = Q(3), Q(2)
                f, h, g, prox, center, supplied = c4.physical_example(T, dim, L, R)
                xs = iterate(prox, g, L, supplied[0], T)
                self.assertEqual(xs, supplied)
                *_, values, gram = c4.normalized_data(T, L, R, f, h, g, center, xs)
                rhs, target = cert.candidate(T)
                self.assertEqual(rhs, target)
                self.assertEqual(cert.ev(rhs, values, gram), cert.ev(target, values, gram))
                self.assertGreaterEqual(cert.ev(rhs, values, gram), 0)
                self.assertLessEqual(f(xs[-1])+h(xs[-1])-f(center)-h(center), L*R**2/(4*T))

    def test_selected_witness_prefix_and_attainment(self):
        for T in range(1, 65):
            for L in (Q(1, 5), Q(1), Q(3)):
                for R in (Q(0), Q(1, 2), Q(2)):
                    a, f, h, g, prox, xs = c4.witness(T, L, R)
                    self.assertEqual(xs, [R*(1-Q(k, 2*T)) for k in range(T+1)])
                    self.assertEqual(f(xs[-1])+h(xs[-1])-f(Q(0))-h(Q(0)), L*R**2/(4*T))

    def test_witness_affine_formula_is_not_asserted_beyond_prefix(self):
        for T in range(1, 17):
            R, L = Q(2), Q(3)
            a, f, h, g, prox, _ = c4.witness(T, L, R)
            x = R
            for k in range(2*T+1):
                x = prox(x-g(x)/L)
            self.assertEqual(x, 0)
            self.assertNotEqual(x, R*(1-Q(2*T+1, 2*T)))

    def test_wrong_forward_scale_changes_actual_run(self):
        h = penalty(1)
        g = lambda x: (Q(2)*x[0]+1,)
        L, x0 = Q(3), (Q(4),)
        correct = iterate(h.prox, g, L, x0, 1)[1]
        wrong = h.prox(c1.sub(x0, g(x0)), L)
        self.assertNotEqual(correct, wrong)
        self.assertFalse(h.supports(wrong, c1.sub(c1.scale(L, c1.sub(x0, wrong)), g(x0))))

    def test_zero_penalty_is_not_an_existence_or_uniqueness_theorem(self):
        with self.assertRaises(ValueError):
            penalty(1).prox((Q(0),), Q(0))
        # h(x)=-x has no minimum when the quadratic penalty is zero.
        for x in range(-10, 11):
            self.assertLess(-Q(x+1), -Q(x))
        # A constant function has multiple minimizers at zero penalty.
        constant = Penalty((Q(0),), (Q(0),), (Q(0),), (Q(0),), offset=Q(7))
        self.assertEqual(constant.objective((Q(0),), Q(0), (Q(-1),)),
                         constant.objective((Q(0),), Q(0), (Q(1),)))
        self.assertNotEqual((Q(-1),), (Q(1),))

    def test_omitting_convexity_can_destroy_prox_existence(self):
        # h(x)=-x^2, L=1, v=0 gives Q(x)=-x^2/2, unbounded below.
        for x in range(1, 20):
            self.assertLess(-Q((x+1)**2, 2), -Q(x*x, 2))
        with self.assertRaises(ValueError):
            Penalty((Q(-1),), (Q(0),), (Q(0),), (Q(0),))

if __name__ == '__main__':
    unittest.main()
