"""C4 exact semantic regressions; not a Lean elaborator or a solver.

The original coefficient/certificate mirrors are reused. Physical forward
and prox steps are evaluated independently, normalized afterwards, and checked
against the old compiler and certificate. Source guards only check selected
wiring/definitions and do not certify the new Lean proofs.
"""
from __future__ import annotations

from fractions import Fraction as Q
from pathlib import Path
import unittest

from tests.python import test_composite_proximal as c1
from tests.python import test_proximal_gradient_profile as pg
from tests.python import test_proximal_gradient_certificate as cert

ROOT = Path(__file__).resolve().parents[2]
ACTUAL = ROOT / 'LeanPEP/ActualFunction'
PROX = (ACTUAL / 'ProximalScaling.lean').read_text()
RUN = (ACTUAL / 'ProximalGradientScaling.lean').read_text() + "\n" + (ACTUAL / 'ProximalGradientScalingCore.lean').read_text()
WITNESS = (ACTUAL / 'ProximalGradientWitnessScaling.lean').read_text()


def norm2(v):
    return c1.dot(v, v)


def to_physical(center, R, z):
    return c1.add(center, c1.scale(R, z))


def to_normalized(center, R, x):
    if R == 0:
        raise ValueError('Inverse coordinates require nonzero radius')
    return c1.scale(1/R, c1.sub(x, center))


def check_scales(L, R):
    if L <= 0 or R <= 0:
        raise ValueError('Positive L and R required for inverse normalization')


def physical_example(T, dim, L, R, *, zero_radius=False, off_f=Q(7, 3), off_h=Q(-11, 5)):
    if T < 0 or dim < 1 or L <= 0 or R < 0:
        raise ValueError('Invalid physical run parameters')
    center = tuple(Q(j-1, 3) for j in range(dim))
    tilt = tuple(Q(j+1, 7) for j in range(dim))
    curv = tuple(Q(j+1, dim+1) for j in range(dim))
    lam = Q(1, 7)
    z0 = tuple(Q(1, dim*(j+2)) for j in range(dim))
    initial = center if zero_radius else to_physical(center, R, z0)

    def f(x):
        d = c1.sub(x, center)
        return off_f + sum((L*q*t*t/2 + L*R*a*t for q, a, t in zip(curv, tilt, d)), Q(0))
    def g(x):
        d = c1.sub(x, center)
        return tuple(L*q*t + L*R*a for q, a, t in zip(curv, tilt, d))
    def h(x):
        d = c1.sub(x, center)
        return off_h + sum((L*R*lam*abs(t)-L*R*a*t for a, t in zip(tilt, d)), Q(0))
    def prox(v, penalty=L):
        return tuple(c + pg.soft(vi+L*R*a/penalty-c, L*R*lam/penalty)
                     for c, vi, a in zip(center, v, tilt))
    xs = [initial]
    for _ in range(T):
        xs.append(prox(c1.sub(xs[-1], c1.scale(1/L, g(xs[-1])))))
    return f, h, g, prox, center, xs


def normalized_data(T, L, R, f, h, g, center, xs):
    check_scales(L, R)
    if T < 1 or len(xs) != T+1:
        raise ValueError('Positive horizon data required')
    A = L*R**2
    F = lambda z: (f(to_physical(center, R, z))-f(center))/A
    H = lambda z: (h(to_physical(center, R, z))-h(center))/A
    G = lambda z: c1.scale(1/(L*R), g(to_physical(center, R, z)))
    zs = [to_normalized(center, R, x) for x in xs]
    zero = tuple(Q(0) for _ in center)
    residuals = [c1.sub(c1.sub(zs[k], G(zs[k])), zs[k+1]) for k in range(T)]
    base = [zs[0], G(zero)] + [G(z) for z in zs] + residuals
    values = tuple([F(zero)] + [F(z) for z in zs] + [H(zero)] + [H(z) for z in zs[1:]])
    gram = tuple(tuple(c1.dot(a, b) for b in base) for a in base)
    return F, H, G, zs, residuals, base, values, gram


def witness(T, L, R):
    if T < 1 or L <= 0 or R < 0:
        raise ValueError('Witness requires T>0, L>0, R>=0')
    a = R/(2*T)
    f = lambda x: L*x
    h = lambda x: L*(a*max(x, Q(0))-x)
    g = lambda x: L
    prox = lambda v: cert.prox_h(v, a, Q(1))
    xs = [R]
    for _ in range(T):
        xs.append(prox(xs[-1]-g(xs[-1])/L))
    return a, f, h, g, prox, xs


class ProximalGradientScalingTests(unittest.TestCase):
    def test_source_uses_original_normalization_and_certificate(self):
        self.assertIn('SmoothScaling.normalizedFirstOrder', RUN)
        self.assertIn('ProximalGradient.certificate_upper_of_prox c hc hempty hobj', RUN)
        self.assertIn('(upperCertQ n) (upperCertQ_check_all n) rfl rfl', RUN)
        self.assertIn('normalizedFunction h center L R', PROX)

    def test_source_physical_penalty_and_forward_coefficient(self):
        self.assertIn('((L : ℝ)/2) * inner ℝ (x-v) (x-v)', PROX)
        self.assertIn('x k - (L : ℝ)⁻¹ • g (x k)', RUN)
        self.assertIn('(1/((L : ℝ)*R)) • s', PROX)

    def test_source_objective_guard_and_empty_interpolation(self):
        self.assertIn('(hempty : c.interpTerms = [])', RUN)
        self.assertIn('(hobj : c.objective = LeanPEP.Profiles.ProximalGradient.objectiveQ n)', RUN)
        self.assertNotIn('native_decide', RUN)

    def test_source_zero_radius_does_not_invert_radius(self):
        block = RUN.split('rcases eq_or_lt_of_le hR with rfl | hR', 1)[1].split('  · have hnormalized', 1)[0]
        self.assertIn('stationary_run', block)
        self.assertNotIn('normalizedPoint', block)
        self.assertNotIn('normalizedFunction', block)

    def test_source_reuses_old_slope_and_points(self):
        self.assertIn('R * ProximalGradientWitness.slope n', WITNESS)
        self.assertIn('R * ProximalGradientWitness.witnessPoint n k', WITNESS)
        self.assertIn('(L : ℝ) * (slope n R * max z 0 - z)', WITNESS)
        self.assertIn('def smoothGradient (L : ℝ≥0) (_ : ℝ) : ℝ := (L : ℝ)', WITNESS)

    def test_inverse_affine_signed_nonzero(self):
        for dim in (1, 2, 5):
            center = tuple(Q(j-2, 3) for j in range(dim))
            z = tuple(Q(2*j+1, 5) for j in range(dim))
            for R in (Q(-5), Q(-1, 7), Q(1, 11), Q(4)):
                self.assertEqual(to_normalized(center, R, to_physical(center, R, z)), z)

    def test_prox_objective_identity(self):
        for dim in (1, 2, 5):
            for L, R in ((Q(1, 3), Q(2, 7)), (Q(3), Q(2)), (Q(7, 2), Q(5, 3))):
                f, h, g, prox, c, xs = physical_example(2, dim, L, R)
                A = L*R**2
                v = tuple(Q(j-2, 5) for j in range(dim))
                for k in range(-3, 4):
                    z = tuple(Q(k+j, 7) for j in range(dim))
                    Tv, Tz = to_physical(c, R, v), to_physical(c, R, z)
                    lhs = (h(Tz)-h(c))/A + norm2(c1.sub(z, v))/2
                    rhs = (h(Tz) + L*norm2(c1.sub(Tz, Tv))/2-h(c))/A
                    self.assertEqual(lhs, rhs)

    def test_forward_point_correspondence(self):
        for T in range(1, 14):
            for dim in (1, 2, 5):
                L, R = Q(5, 2), Q(3, 7)
                f, h, g, prox, c, xs = physical_example(T, dim, L, R)
                F, H, G, zs, *_ = normalized_data(T, L, R, f, h, g, c, xs)
                for x, z in zip(xs, zs):
                    self.assertEqual(to_physical(c, R, c1.sub(z, G(z))), c1.sub(x, c1.scale(1/L, g(x))))

    def test_normalized_run_equals_independent_unit_run(self):
        for T in range(1, 14):
            for dim in (1, 2, 5):
                _, _, _, _, unit_xs, *_ = pg.actual_example(T-1, dim, translate=False)
                for L, R in ((Q(1, 4), Q(1, 3)), (Q(3), Q(2)), (Q(7, 2), Q(5, 3))):
                    f, h, g, prox, c, xs = physical_example(T, dim, L, R)
                    zs = [to_normalized(c, R, x) for x in xs]
                    self.assertEqual(zs, unit_xs)

    def test_physical_prox_global_min_sample_grid(self):
        # Independent exact comparison points; this does not prove global minimality.
        for L, R in ((Q(1, 3), Q(2, 7)), (Q(3), Q(2))):
            f, h, g, prox, c, xs = physical_example(6, 1, L, R)
            for x, nxt in zip(xs, xs[1:]):
                v = c1.sub(x, c1.scale(1/L, g(x)))
                opt = h(nxt)+L*norm2(c1.sub(nxt, v))/2
                for j in range(-20, 21):
                    y = (Q(j, 5),)
                    self.assertLessEqual(opt, h(y)+L*norm2(c1.sub(y, v))/2)

    def test_normalized_residual_coefficients(self):
        for T in range(1, 14):
            f, h, g, prox, c, xs = physical_example(T, 5, Q(3), Q(2))
            *_, residuals, base, vals, gram = normalized_data(T, Q(3), Q(2), f, h, g, c, xs)
            for k, s in enumerate(residuals):
                physical = c1.sub(c1.scale(Q(3), c1.sub(xs[k], xs[k+1])), g(xs[k]))
                self.assertEqual(s, c1.scale(Q(1, 6), physical))

    def test_normalized_objective_and_offsets(self):
        for T in range(1, 14):
            for off_f, off_h in ((Q(0), Q(0)), (Q(1000, 3), Q(-701, 2))):
                L, R = Q(3), Q(2)
                f, h, g, prox, c, xs = physical_example(T, 2, L, R, off_f=off_f, off_h=off_h)
                F, H, G, zs, *_ = normalized_data(T, L, R, f, h, g, c, xs)
                zero = (Q(0), Q(0))
                self.assertEqual(F(zs[-1])+H(zs[-1])-F(zero)-H(zero),
                                 (f(xs[-1])+h(xs[-1])-f(c)-h(c))/(L*R**2))

    def test_actual_compiler_and_all_constraints(self):
        for T in range(1, 9):
            for dim in (1, 2, 5):
                L, R = Q(5, 2), Q(3, 7)
                f, h, g, prox, c, xs = physical_example(T, dim, L, R)
                F, H, G, zs, rs, base, vals, gram = normalized_data(T, L, R, f, h, g, c, xs)
                for coeff, z in zip(pg.positions(T-1), zs):
                    self.assertEqual(pg.realize(coeff, base), z)
                constraints, objective = pg.compile_profile(T-1)
                self.assertTrue(all(cert.ev(e, vals, gram) >= 0 for e in constraints))
                self.assertEqual(cert.ev(objective, vals, gram), F(zs[-1])+H(zs[-1]))

    def test_original_certificate_on_scaled_actual_data(self):
        for T in range(1, 9):
            for dim in (1, 2, 5):
                L, R = Q(3), Q(2)
                f, h, g, prox, c, xs = physical_example(T, dim, L, R)
                *_, vals, gram = normalized_data(T, L, R, f, h, g, c, xs)
                rhs, target = cert.candidate(T)
                self.assertEqual(cert.ev(rhs, vals, gram), cert.ev(target, vals, gram))
                self.assertGreaterEqual(cert.ev(rhs, vals, gram), 0)
                self.assertLessEqual(f(xs[-1])+h(xs[-1])-f(c)-h(c), L*R**2/(4*T))

    def test_strict_radius_slack_not_assumed_zero(self):
        f, h, g, prox, c, xs = physical_example(3, 2, Q(3), Q(2))
        *_, vals, gram = normalized_data(3, Q(3), Q(2), f, h, g, c, xs)
        self.assertGreater(1-gram[0][0], 0)
        idx, weight = cert.terms(3)[-1]
        self.assertGreater(weight*cert.ev(cert.selected_constraint(3, idx), vals, gram), 0)

    def test_zero_radius_cancelling_witness(self):
        for T in range(1, 65):
            for L in (Q(1, 7), Q(1), Q(13)):
                a, f, h, g, prox, xs = witness(T, L, Q(0))
                self.assertEqual(xs, [Q(0)]*(T+1))
                self.assertNotEqual(g(Q(0)), 0)
                self.assertEqual(h(Q(2)), -2*L)
                self.assertEqual(f(Q(2))+h(Q(2)), 0)

    def test_positive_witness_run_and_final(self):
        for T in range(1, 65):
            for L, R in ((Q(1, 3), Q(2, 7)), (Q(3), Q(2)), (Q(11), Q(9, 4))):
                a, f, h, g, prox, xs = witness(T, L, R)
                self.assertEqual(xs, [R-Q(k)*a for k in range(T+1)])
                self.assertEqual(xs[-1], R/2)
                self.assertEqual(f(xs[-1])+h(xs[-1])-f(0)-h(0), L*R**2/(4*T))

    def test_scaled_witness_full_primal_with_affine_tilt(self):
        # The normalized affine split has tilt 1/R, NOT necessarily the old tilt 1.
        for T in range(1, 9):
            for L, R in ((Q(3), Q(2)), (Q(1, 5), Q(3, 7))):
                a, f, h, g, prox, xs = witness(T, L, R)
                A = L*R**2
                base = (Q(1), Q(1)/R) + (Q(1)/R,)*(T+1) + (Q(1, 2*T)-1/R,)*T
                vals = (Q(0),)+tuple(f(x)/A for x in xs)+(Q(0),)+tuple(h(x)/A for x in xs[1:])
                *_, old_base, old_vals, old_gram = cert.data(T, tilt=1/R)
                self.assertEqual(base, old_base)
                self.assertEqual(vals, old_vals)
                constraints, _ = pg.compile_profile(T-1)
                self.assertTrue(all(cert.ev(e, vals, old_gram) >= 0 for e in constraints))
                for idx, w in cert.terms(T):
                    self.assertEqual(w*cert.ev(cert.selected_constraint(T, idx), vals, old_gram), 0)
                for w, v in cert.factors(T):
                    self.assertEqual(w*c1.dot(v, base)**2, 0)

    def test_witness_not_global_linear_run(self):
        for T in range(1, 17):
            a, f, h, g, prox, xs = witness(T, Q(3), Q(2))
            self.assertNotEqual(prox(Q(0)-Q(1)), -a)

    def test_prox_uniqueness_quadratic_remainder(self):
        for dim in (1, 2, 5):
            for L in (Q(1, 7), Q(3)):
                s = tuple(Q(j+1, 5) for j in range(dim))
                v = tuple(Q(j-2, 3) for j in range(dim))
                x = c1.sub(v, c1.scale(1/L, s))  # prox for affine h=<s,.>
                for j in range(1, 7):
                    y = c1.add(x, tuple(Q(j, 7) for _ in range(dim)))
                    rem = c1.dot(s, y)+L*norm2(c1.sub(y, v))/2-c1.dot(s, x)-L*norm2(c1.sub(x, v))/2
                    self.assertEqual(rem, L*norm2(c1.sub(y, x))/2)
                    self.assertGreater(rem, 0)

    def test_mutation_missing_inverse_L(self):
        f, h, g, prox, c, xs = physical_example(2, 2, Q(3), Q(2))
        wrong = prox(c1.sub(xs[0], g(xs[0])))
        self.assertNotEqual(wrong, xs[1])

    def test_mutation_wrong_prox_penalty(self):
        f, h, g, prox, c, xs = physical_example(2, 2, Q(3), Q(2))
        v = c1.sub(xs[0], c1.scale(Q(1, 3), g(xs[0])))
        self.assertNotEqual(prox(v, penalty=Q(1)), xs[1])

    def test_mutation_wrong_gradient_or_value_scale(self):
        L, R = Q(3), Q(2)
        f, h, g, prox, c, xs = physical_example(2, 2, L, R)
        F, H, G, zs, *_ = normalized_data(2, L, R, f, h, g, c, xs)
        self.assertNotEqual(c1.scale(1/(L*R**2), g(xs[0])), G(zs[0]))
        self.assertNotEqual((h(xs[0])-h(c))/(L*R), H(zs[0]))

    def test_mutation_separate_stationarity_and_wrong_bound(self):
        for T in (1, 4, 8, 32):
            L, R = Q(3), Q(2)
            a, f, h, g, prox, xs = witness(T, L, R)
            self.assertNotEqual(g(0), 0)
            gap = f(xs[-1])+h(xs[-1])-f(0)-h(0)
            self.assertNotEqual(gap, L*R/(4*T))
            self.assertNotEqual(gap, R**2/(4*T))
            self.assertGreater(gap, L*R**2/(4*T+2))

    def test_unit_scales_match_original_witness(self):
        for T in range(1, 33):
            a, f, h, g, prox, xs = witness(T, Q(1), Q(1))
            of, og, oh, oxs, *_ = cert.data(T)
            self.assertEqual(tuple(xs), oxs)
            for z in (Q(-2), Q(0), Q(1, 2), Q(3)):
                self.assertEqual((f(z), g(z), h(z)), (of(z), og(z), oh(z)))

    def test_invalid_scale_guard_and_no_zero_step_rate(self):
        for L, R in ((Q(0), Q(1)), (Q(-1), Q(1)), (Q(1), Q(0)), (Q(1), Q(-1))):
            with self.assertRaises(ValueError): check_scales(L, R)
        with self.assertRaises(ValueError): witness(0, Q(1), Q(1))
        with self.assertRaises(ValueError): to_normalized((Q(0),), Q(0), (Q(1),))
        f, h, g, prox, c, xs = physical_example(0, 1, Q(3), Q(2))
        self.assertEqual(len(xs), 1)  # Vacuous run allowed; no upper-rate claim.


if __name__ == '__main__':
    unittest.main()
