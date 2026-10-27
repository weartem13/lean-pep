"""Independent exact regressions for B4 scaling (not a Lean proof runner).

We execute physical and normalized oracles separately, reuse B1 coefficient
and certificate data, and include zero radius without an inverse-radius call.
Source guards check the intended bridge wiring, not elaboration or soundness.
"""
from __future__ import annotations

from fractions import Fraction as Q
from pathlib import Path
import re
import unittest

from tests.python import test_momentum_actual as b2
from tests.python import test_momentum_profile as b1

ROOT = Path(__file__).resolve().parents[2]
ACTUAL = ROOT / "LeanPEP/ActualFunction"


def transform(center: b2.Vec, radius: Q, z: b2.Vec) -> b2.Vec:
    return b2.add(center, b2.smul(radius, z))


def normalized_pair(f: b2.Function, g: b2.Oracle, center: b2.Vec,
                    smoothness: Q, radius: Q) -> tuple[b2.Function, b2.Oracle]:
    if smoothness <= 0 or radius <= 0:
        raise ValueError("Positive L and R are required for inverse normalization")
    amplitude = smoothness * radius**2
    return (lambda z: (f(transform(center, radius, z)) - f(center)) / amplitude,
            lambda z: b2.smul(1 / (smoothness * radius), g(transform(center, radius, z))))


def physical_pair(f: b2.Function, g: b2.Oracle, center: b2.Vec,
                  smoothness: Q, radius: Q, offset: Q = Q(0)) -> tuple[b2.Function, b2.Oracle]:
    if smoothness <= 0 or radius <= 0:
        raise ValueError("Use the direct Huber definition at zero radius")
    to_z = lambda x: b2.smul(1 / radius, b2.sub(x, center))
    return (lambda x: smoothness * radius**2 * f(to_z(x)) + offset,
            lambda x: b2.smul(smoothness * radius, g(to_z(x))))


def source_threshold() -> Q:
    source = (ACTUAL / "NesterovPilotWitness.lean").read_text(encoding="utf-8")
    m = re.search(r"^def threshold : ℝ := ([^\n]+)$", source, re.M)
    if m is None:
        raise ValueError("Missing B3 witness threshold")
    return b1.rational(m.group(1))


def scaled_witness(L: Q, R: Q, center: Q = Q(0), offset: Q = Q(0)):
    if L < 0 or R < 0:
        raise ValueError("Nonnegative witness scales required")
    f, g = b2.huber(R * source_threshold(), center)
    return lambda x: L * f(x) + offset, lambda x: b2.smul(L, g(x))


def pilot_run(L: Q, g: b2.Oracle, x0: b2.Vec):
    if L <= 0:
        raise ValueError("The physical upper theorem requires positive smoothness")
    return b2.actual_run([Q(1) / L] * 4, [Q(k, k + 3) for k in range(4)], g, x0)


class MomentumScalingTests(unittest.TestCase):
    def test_affine_covariance_signed_scales_and_schedules(self):
        for dim in (1, 2, 5):
            center = [Q(j - 2, 3) for j in range(dim)]
            z0 = [Q(j + 1, dim + 2) for j in range(dim)]
            g = lambda z: [Q(j + 1, dim + 3)*v + Q(2-j, 7) for j, v in enumerate(z)]
            for R in (Q(-3), Q(-1, 7), Q(1, 5), Q(4)):
                gp = lambda x: b2.smul(R, g(b2.smul(1 / R, b2.sub(x, center))))
                for n in range(13):
                    steps = [Q((k % 5) - 2, 3) for k in range(n)]
                    betas = [Q((k % 7) - 3, 5) for k in range(n)]
                    x, y = b2.actual_run(steps, betas, g, z0)
                    X, Y = b2.actual_run(steps, betas, gp, transform(center, R, z0))
                    self.assertEqual(X, [transform(center, R, z) for z in x])
                    self.assertEqual(Y, [transform(center, R, z) for z in y])

    def test_singular_affine_transport_does_not_require_inverse(self):
        center, z0 = [Q(2), Q(-3)], [Q(7), Q(8)]
        g = lambda z: b2.add(z, [Q(1), Q(2)])
        gp = lambda x: b2.sub(x, center)  # gp(center)=0; may be nonzero elsewhere.
        steps, betas = [Q(-2), Q(0), Q(3)] * 4, [Q(7, 3)] * 12
        x, y = b2.actual_run(steps, betas, g, z0)
        X, Y = b2.actual_run(steps, betas, gp, center)
        self.assertEqual(X, [transform(center, Q(0), z) for z in x])
        self.assertEqual(Y, [transform(center, Q(0), z) for z in y])

    def test_positive_normalization_preserves_both_sequences(self):
        for dim in (1, 2, 5):
            center = [Q(j - 3, 2) for j in range(dim)]
            base_f, base_g = b2.quadratic([Q(0)]*dim, [Q(j+1, dim+2) for j in range(dim)])
            z0 = [Q(1, dim+1)] * dim
            for L, R in ((Q(1, 3), Q(2, 7)), (Q(3), Q(2)), (Q(7, 2), Q(5, 3))):
                f, g = physical_pair(base_f, base_g, center, L, R, Q(11, 3))
                F, G = normalized_pair(f, g, center, L, R)
                for n in range(13):
                    steps = [Q(k % 5 - 2, 4) for k in range(n)]
                    betas = [Q(k % 7 - 3, 6) for k in range(n)]
                    x, y = b2.actual_run(steps, betas, G, z0)
                    X, Y = b2.actual_run([a/L for a in steps], betas, g, transform(center, R, z0))
                    self.assertEqual(X, [transform(center, R, z) for z in x])
                    self.assertEqual(Y, [transform(center, R, z) for z in y])
                    self.assertEqual(F(x[-1])-F([Q(0)]*dim),
                                     (f(X[-1])-f(center))/(L*R**2))

    def test_initial_norm_and_radius_slack(self):
        for R in (Q(1, 7), Q(1), Q(8, 3)):
            center, x0 = [Q(2), Q(-1)], [Q(2)+R/3, Q(-1)+R/4]
            z0 = b2.smul(1/R, b2.sub(x0, center))
            norm2 = b2.inner(b2.sub(x0, center), b2.sub(x0, center))
            self.assertEqual(b2.inner(z0, z0), norm2/R**2)
            self.assertEqual(transform(center, R, z0), x0)
            self.assertGreater(1-b2.inner(z0, z0), 0)

    def test_stationary_run_all_schedules_and_zero_steps(self):
        center = [Q(3), Q(-2)]
        _, g = b2.quadratic(center, [Q(1, 2), Q(3, 4)])
        for n in range(25):
            for L in (Q(1, 7), Q(3), Q(19, 2)):
                x, y = b2.actual_run([Q(k-3, 7)/L for k in range(n)],
                                      [Q(9-k, 3) for k in range(n)], g, center)
                self.assertEqual(x, [center]*(n+1))
                self.assertEqual(y, [center]*(n+1))

    def test_unit_smoothness_is_original_run(self):
        _, g = b2.quadratic([Q(0)], [Q(3, 7)])
        self.assertEqual(pilot_run(Q(1), g, [Q(1)]),
                         b2.actual_run([Q(1)]*4, [Q(k, k+3) for k in range(4)], g, [Q(1)]))

    def test_normalization_rejects_nonpositive_parameters(self):
        f, g = b2.quadratic([Q(0)], [Q(1, 2)])
        for L, R in ((Q(0), Q(1)), (Q(1), Q(0)), (Q(-1), Q(1)), (Q(1), Q(-1))):
            with self.assertRaises(ValueError):
                normalized_pair(f, g, [Q(0)], L, R)

    def test_missing_inverse_L_changes_trajectory(self):
        L, R = Q(3), Q(2)
        f0, g0 = b2.quadratic([Q(0)], [Q(3, 7)])
        _, g = physical_pair(f0, g0, [Q(4)], L, R)
        good = pilot_run(L, g, [Q(6)])
        wrong = b2.actual_run([Q(1)]*4, [Q(k, k+3) for k in range(4)], g, [Q(6)])
        self.assertNotEqual(good[0][-1], wrong[0][-1])

    def test_dividing_momentum_by_L_is_wrong(self):
        L = Q(3)
        _, g = scaled_witness(L, Q(2))
        good = pilot_run(L, g, [Q(2)])
        wrong = b2.actual_run([1/L]*4, [Q(k, k+3)/L for k in range(4)], g, [Q(2)])
        self.assertNotEqual(good[0][-1], wrong[0][-1])

    def test_oracle_at_state_is_not_query_update(self):
        L, R = Q(3), Q(2)
        f0, g0 = b2.quadratic([Q(0)], [Q(3, 7)])
        _, g = physical_pair(f0, g0, [Q(0)], L, R)
        good = pilot_run(L, g, [R])
        wrong = b2.actual_run([1/L]*4, [Q(k, k+3) for k in range(4)], g, [R],
                             wrong_oracle_point=True)
        self.assertNotEqual(good[0][-1], wrong[0][-1])

    def test_field_scaling_is_LR_not_LR_squared(self):
        L, R = Q(5), Q(2)
        f0, g0 = b2.quadratic([Q(0)], [Q(1, 2)])
        f, g = physical_pair(f0, g0, [Q(3)], L, R)
        _, G = normalized_pair(f, g, [Q(3)], L, R)
        z = [Q(2, 3)]
        self.assertEqual(G(z), g0(z))
        self.assertNotEqual(b2.smul(1/(L*R**2), g(transform([Q(3)], R, z))), g0(z))

    def test_last_momentum_still_does_not_affect_final_state(self):
        L = Q(7, 3)
        _, g = scaled_witness(L, Q(5, 2))
        beta = [Q(k, k+3) for k in range(4)]
        x, y = b2.actual_run([1/L]*4, beta, g, [Q(5, 2)])
        beta[-1] = Q(-31, 4)
        xx, yy = b2.actual_run([1/L]*4, beta, g, [Q(5, 2)])
        self.assertEqual(x, xx)
        self.assertEqual(y[:-1], yy[:-1])
        self.assertNotEqual(y[-1], yy[-1])

    def test_source_keeps_checker_and_objective_contract(self):
        src = (ACTUAL / "MomentumScaling.lean").read_text(encoding="utf-8")
        header = b1.declaration(src, "certificate_upper").split(":= by", 1)[0]
        self.assertIn("GramPEP.checkUpperCertQ c = true", header)
        self.assertIn("c.objective = outputObjectiveQ N s unitRadiusNormalizationQ", header)
        self.assertIn("IsSmoothConvexFirstOrder L f g", header)
        self.assertIn("0 ≤ R", header)
        self.assertIn("import LeanPEP.GramPEP.UpperCertificateChecker", src)
        # Metadata protection only: this does not claim the Lean file elaborates.
        self.assertNotIn("def pilotUpperCertQ", src)


class NesterovScaledWitnessTests(unittest.TestCase):
    def test_all_scaled_witness_states_and_queries(self):
        a = source_threshold()
        f0, g0 = b2.huber(a)
        x, y = pilot_run(Q(1), g0, [Q(1)])
        for L in (Q(1, 7), Q(1), Q(3), Q(17, 5)):
            for R in (Q(0), Q(1, 9), Q(1), Q(2), Q(13, 3)):
                _, g = scaled_witness(L, R)
                X, Y = pilot_run(L, g, [R])
                self.assertEqual(X, [b2.smul(R, z) for z in x])
                self.assertEqual(Y, [b2.smul(R, z) for z in y])

    def test_global_huber_scaling_including_both_branches(self):
        a = source_threshold()
        f0, g0 = b2.huber(a)
        for L in (Q(0), Q(1, 3), Q(3)):
            for R in (Q(0), Q(2, 7), Q(5)):
                f, g = scaled_witness(L, R)
                for z in (Q(-3), Q(0), a/2, a, a*2, Q(7)):
                    self.assertEqual(f([R*z]), L*R**2*f0([z]))
                    self.assertEqual(g([R*z]), b2.smul(L*R, g0([z])))

    def test_exact_attainment_across_scales(self):
        for L in (Q(1, 7), Q(1), Q(3), Q(17, 5)):
            for R in (Q(0), Q(1, 9), Q(1), Q(2), Q(13, 3)):
                f, g = scaled_witness(L, R)
                x, y = pilot_run(L, g, [R])
                self.assertEqual(x[-1], [R*Q(23, 42)])
                self.assertEqual(y[-1], [R*Q(10, 21)])
                self.assertEqual(f(x[-1])-f([Q(0)]), L*R**2/21)
                self.assertEqual(f(y[-1])-f([Q(0)]), 2*L*R**2/49)

    def test_positive_radius_endpoint_separation(self):
        for R in (Q(1, 19), Q(2), Q(9, 2)):
            f, g = scaled_witness(Q(3), R)
            x, y = pilot_run(Q(3), g, [R])
            self.assertNotEqual(x[-1], y[-1])
            self.assertNotEqual(f(x[-1]), f(y[-1]))

    def test_zero_radius_trajectory_not_identically_zero_function(self):
        f, g = scaled_witness(Q(3), Q(0))
        x, y = pilot_run(Q(3), g, [Q(0)])
        self.assertEqual(x, [[Q(0)]]*5)
        self.assertEqual(y, [[Q(0)]]*5)
        self.assertEqual(f(x[-1])-f([Q(0)]), 0)
        self.assertEqual(f([Q(-1)]), Q(3, 2))
        self.assertEqual(g([Q(0)]), [Q(0)])

    def test_translation_and_value_offset(self):
        for center, offset in ((Q(-7, 3), Q(11)), (Q(5), Q(-9, 2))):
            L, R = Q(7, 5), Q(3, 2)
            f, g = scaled_witness(L, R, center, offset)
            x, y = pilot_run(L, g, [center+R])
            self.assertEqual(x[-1], [center+R*Q(23, 42)])
            self.assertEqual(y[-1], [center+R*Q(10, 21)])
            self.assertEqual(f(x[-1])-f([center]), L*R**2/21)

    def test_actual_interpolation_scales_by_LR_squared(self):
        L, R = Q(7, 3), Q(5, 2)
        center = Q(-4)
        f, g = scaled_witness(L, R, center, Q(17))
        F, G = normalized_pair(f, g, [center], L, R)
        xs, ys = pilot_run(L, g, [center+R])
        zs, qs = pilot_run(Q(1), G, [Q(1)])
        P, Z = [[center]]+ys[:-1]+[xs[-1]], [[Q(0)]]+qs[:-1]+[zs[-1]]
        for i in range(6):
            for j in range(6):
                dg = b2.sub(g(P[i]), g(P[j]))
                physical = (f(P[i])-f(P[j])-b2.inner(g(P[j]), b2.sub(P[i], P[j]))
                            -b2.inner(dg, dg)/(2*L))
                self.assertEqual(physical, L*R**2*b2.actual_slack(F, G, Z[i], Z[j]))
                self.assertGreaterEqual(physical, 0)

    def test_normalized_data_match_original_primal(self):
        L, R = Q(11, 7), Q(5, 3)
        f, g = scaled_witness(L, R, Q(2), Q(-7))
        F, G = normalized_pair(f, g, [Q(2)], L, R)
        d = b2.datum([Q(1)]*4, [Q(k, k+3) for k in range(4)], F, G, [Q(0)], [Q(1)])
        self.assertEqual(d.values, [Q(0), Q(40, 441), Q(4, 49), Q(31, 441), Q(25, 441), Q(1, 21)])
        self.assertEqual(d.base, [[Q(1)]]+[[Q(2, 21)]]*5)

    def test_source_preserves_actual_tightness_not_gram_set(self):
        src = (ACTUAL / "NesterovPilotWitnessScaling.lean").read_text(encoding="utf-8")
        decl = b1.declaration(src, "oneDimensionalAnalyticValues")
        self.assertIn("IsSmoothConvexAnalytic L f g", decl)
        self.assertIn("NesterovPilotScaling.iterate L g x0 4", decl)
        self.assertNotIn("CoreFeasible", decl)
        self.assertNotIn("checkUpperCertQ", decl)


class ScaledCertificateTests(unittest.TestCase):
    def check_scaled(self, f, g, center, initial, L, R):
        F, G = normalized_pair(f, g, center, L, R)
        z0 = b2.smul(1/R, b2.sub(initial, center))
        d = b2.datum([Q(1)]*4, [Q(k, k+3) for k in range(4)], F, G, [Q(0)]*len(center), z0)
        terms, factors = b2.pilot_constants()
        interpolation = sum((w*b2.gram_slack(d, i, j) for w, i, j in terms), Q(0))
        radius = (1-d.gram[0][0])/21
        dual = sum((w*b2.inner(b2.realize(v, d.base), b2.realize(v, d.base))
                    for w, v in factors), Q(0))
        x, _ = pilot_run(L, g, initial)
        gap = f(x[-1])-f(center)
        A = L*R**2
        self.assertEqual(A/21-gap, A*(interpolation+radius+dual))
        self.assertGreaterEqual(interpolation, 0)
        self.assertGreaterEqual(radius, 0)
        self.assertGreaterEqual(dual, 0)
        self.assertLessEqual(gap, A/21)
        return radius, gap

    def test_original_certificate_on_scaled_quadratics_with_slack(self):
        for dim in (1, 2, 5):
            f0, g0 = b2.quadratic([Q(0)]*dim, [Q(j+1, dim+2) for j in range(dim)])
            center, z0 = [Q(j-2, 7) for j in range(dim)], [Q(1, dim+1)]*dim
            for L, R in ((Q(1, 7), Q(2, 3)), (Q(3), Q(2)), (Q(7, 2), Q(1, 5))):
                f, g = physical_pair(f0, g0, center, L, R, Q(19))
                radius, _ = self.check_scaled(f, g, center, transform(center, R, z0), L, R)
                self.assertGreater(radius, 0)

    def test_original_certificate_on_scaled_huber_witness(self):
        for L, R in ((Q(2, 5), Q(3, 2)), (Q(3), Q(2)), (Q(11, 2), Q(7))):
            f, g = scaled_witness(L, R, Q(5), Q(-1))
            radius, gap = self.check_scaled(f, g, [Q(5)], [Q(5)+R], L, R)
            self.assertEqual(radius, 0)
            self.assertEqual(gap, L*R**2/21)

    def test_original_certificate_on_scaled_piecewise_crossings(self):
        for a in (Q(0), Q(1, 50), Q(1, 3), Q(2)):
            f0, g0 = b2.huber(a)
            L, R, center = Q(7, 3), Q(2, 5), [Q(-2)]
            f, g = physical_pair(f0, g0, center, L, R, Q(13))
            for z in (Q(-1), Q(-1, 2), Q(0), Q(1, 2), Q(1)):
                self.check_scaled(f, g, center, transform(center, R, [z]), L, R)


if __name__ == "__main__":
    unittest.main()
