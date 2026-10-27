"""C7 exact diagnostics, not execution of Lean choice or infinite-dimensional proof.

Rational finite-coordinate examples test the algebra behind the compact-free
argument. Source-interface checks prevent accidental weakening of its premises.
Completeness, continuity and quantification over a Hilbert space remain Lean
proof obligations; these tests do not infer them from finite samples.
"""
from __future__ import annotations
from fractions import Fraction as Q
from pathlib import Path
import re
import unittest

from tests.python import test_composite_proximal as c1
from tests.python import test_proximal_gradient_scaling as c4
from tests.python import test_proximal_gradient_certificate as cert
from tests.python import test_proximal_canonical as c6

ROOT = Path(__file__).resolve().parents[2]
MID = (ROOT/'LeanPEP/ActualFunction/StrongMidpointMinimizer.lean').read_text()
EXIST = (ROOT/'LeanPEP/ActualFunction/ProximalHilbertExistence.lean').read_text()
RATE = (ROOT/'LeanPEP/ActualFunction/ProximalGradientHilbert.lean').read_text()
Vec = tuple[Q, ...]


def vecadd(x: Vec, y: Vec) -> Vec:
    return tuple(a+b for a,b in zip(x,y,strict=True))


def midpoint(x: Vec, y: Vec) -> Vec:
    return c1.scale(Q(1,2), vecadd(x,y))


def units(dim: int) -> Vec:
    if dim == 1:
        return (Q(1),)
    if dim == 2:
        return (Q(3,5), Q(4,5))
    if dim == 5:
        return (Q(1,3), Q(2,3), Q(2,3), Q(0), Q(0))
    raise ValueError('Unsupported rational unit-vector dimension')


def uncomment(s: str) -> str:
    # New C7 files contain no nested block comments.
    return re.sub(r'--[^\n]*', '', re.sub(r'/-.*?-/', '', s, flags=re.S))


class ProximalHilbertTests(unittest.TestCase):
    def test_source_compact_free_core_and_complete_limit(self):
        s = uncomment(MID+EXIST)
        for bad in ('FiniteDimensional', 'IsCompact', 'isCompact_closedBall', 'exists_isMinOn'):
            self.assertNotIn(bad, s)
        for good in ('ciInf_le', 'exists_lt_of_ciInf_lt', 'cauchySeq_tendsto_of_complete',
                     'tendsto_nhds_unique'):
            self.assertIn(good, MID)

    def test_source_explicit_regularity_and_positivity(self):
        head = EXIST.split('theorem exists_isProxPoint_hilbert',1)[1].split(':= by',1)[0]
        for required in ('[CompleteSpace E]', '0 < (L : ℝ)', 'ConvexOn ℝ Set.univ h', 'Continuous h'):
            self.assertIn(required,head)
        for forbidden in ('HasProx', 'SubgradientAt', 'FiniteDimensional', 'IsSmoothProxRun'):
            self.assertNotIn(forbidden,head)
        self.assertIn('Metric.continuousAt_iff', EXIST)

    def test_source_reuses_old_operator_and_certificate_guards(self):
        block = RATE.split('def hilbertIterate',1)[1].split('@[simp]',1)[0]
        self.assertIn('iterate (hasProx_of_continuous hL hh hcont) g x0',block)
        self.assertNotIn('Classical.choose',block)
        for guard in ('GramPEP.checkUpperCertQ c = true','c.interpTerms = []',
                      'c.objective = Profiles.ProximalGradient.objectiveQ n'):
            self.assertIn(guard,RATE)
        self.assertIn('upper_analytic_steps T hT (hasProx_of_continuous',RATE)

    def test_source_value_set_does_not_assume_free_run_or_prox_existence(self):
        block=RATE.split('def oneDimensionalHilbertValues',1)[1].split('/--',1)[0]
        for req in ('Continuous h','ConvexOn ℝ Set.univ h','hilbertIterate'):
            self.assertIn(req,block)
        for bad in ('HasProx','IsSmoothProxRun','GramPEP','(x : ℕ → ℝ)'):
            self.assertNotIn(bad,block)
        self.assertIn('hh.continuousOn isOpen_univ',RATE)
        self.assertIn('oneDimensionalHilbertValues_eq_canonicalValues',RATE)

    def test_rational_opposite_direction_geometry(self):
        for dim in (1,2,5):
            v=tuple(Q(j-2,7) for j in range(dim))
            unit=units(dim)
            self.assertEqual(c4.norm2(unit),1)
            for r in (Q(1,7),Q(1),Q(5)):
                for d in (Q(1,13),Q(2),Q(11,3)):
                    x=vecadd(v,c1.scale(d,unit))
                    y=c1.sub(v,c1.scale(r/d,c1.sub(x,v)))
                    self.assertEqual(c4.norm2(c1.sub(y,v)),r*r)
                    self.assertEqual(vecadd(c1.scale(r/(d+r),x),c1.scale(d/(d+r),y)),v)

    def test_local_upper_to_radial_lower_with_variable_ball(self):
        for curvature in (Q(0),Q(2,5),Q(3)):
            h=c6.Penalty((curvature,),(Q(2,7),),(Q(-4,3),),(Q(2,3),))
            for v in (Q(-2),Q(0),Q(3,2)):
                for r in (Q(1,5),Q(1),Q(4)):
                    M=max(h.h((v-r,)),h.h((v+r,)))-h.h((v,))
                    self.assertGreaterEqual(M,0)
                    for k in range(-30,31):
                        x=Q(k,4)
                        self.assertLessEqual(h.h((v,))-(M/r)*abs(x-v),h.h((x,)))

    def test_radial_bound_center_case_no_inverse_norm(self):
        for v in (Q(-7),Q(0),Q(8,3)):
            for C in (Q(0),Q(2),Q(5,7)):
                self.assertEqual(v-C*abs(v-v),v)
        h=c6.penalty(0)
        self.assertEqual(h.objective((),Q(3),()),h.h(()))

    def test_complete_square_identity_for_positive_penalty(self):
        for L in (Q(1,11),Q(1),Q(3),Q(17,2)):
            for C in (Q(0),Q(1,7),Q(4)):
                for d in (Q(0),Q(1,13),Q(2),Q(19)):
                    lhs=-C*C/(2*L)+L*(d-C/L)**2/2
                    self.assertEqual(lhs,-C*d+L*d*d/2)
                    self.assertGreaterEqual(-C*d+L*d*d/2,-C*C/(2*L))

    def test_norm_midpoint_gap_full_cross_terms(self):
        for dim in (0,1,2,5):
            for t in range(9):
                x=tuple(Q(j+t-3,5) for j in range(dim))
                y=tuple(Q(2*j-t,7) for j in range(dim))
                v=tuple(Q(3-j,4) for j in range(dim))
                lhs=c4.norm2(c1.sub(midpoint(x,y),v))
                rhs=(c4.norm2(c1.sub(x,v))+c4.norm2(c1.sub(y,v)))/2-c4.norm2(c1.sub(x,y))/4
                self.assertEqual(lhs,rhs)

    def test_prox_objective_midpoint_gap(self):
        for dim in (0,1,2,5):
            h=c6.penalty(dim)
            v=tuple(Q(1-j,9) for j in range(dim))
            for L in (Q(1,9),Q(1),Q(5)):
                for t in range(10):
                    x=tuple(Q(j-t,3) for j in range(dim))
                    y=tuple(Q(j+2*t,7) for j in range(dim))
                    gap=(h.objective(v,L,x)+h.objective(v,L,y))/2-h.objective(v,L,midpoint(x,y))
                    convexgap=(h.h(x)+h.h(y))/2-h.h(midpoint(x,y))
                    self.assertEqual(gap,convexgap+L*c4.norm2(c1.sub(x,y))/8)
                    self.assertGreaterEqual(convexgap,0)

    def test_affine_penalty_makes_L_over_8_sharp(self):
        h=c6.Penalty((Q(0),),(Q(0),),(Q(-3),),(Q(0),))
        for L in (Q(1,4),Q(1),Q(7)):
            x,y,v=(Q(-2),),(Q(5),),(Q(4,3),)
            gap=(h.objective(v,L,x)+h.objective(v,L,y))/2-h.objective(v,L,midpoint(x,y))
            self.assertEqual(gap,L*c4.norm2(c1.sub(x,y))/8)
            self.assertLess(gap,L*c4.norm2(c1.sub(x,y))/4)

    def test_approximate_minimizer_pair_estimate(self):
        for dim in (1,2,5):
            h=c6.penalty(dim)
            v=tuple(Q(2-j,11) for j in range(dim))
            for L in (Q(1,3),Q(1),Q(9)):
                z=h.prox(v,L)
                m=h.objective(v,L,z)
                for t in range(7):
                    x=tuple(Q(j-t,3) for j in range(dim))
                    y=tuple(Q(2*j+t,5) for j in range(dim))
                    ep=h.objective(v,L,x)-m
                    eq=h.objective(v,L,y)-m
                    self.assertGreaterEqual(ep,0)
                    self.assertGreaterEqual(eq,0)
                    self.assertLessEqual((L/8)*c4.norm2(c1.sub(x,y)),(ep+eq)/2)

    def test_controlled_minimizing_sequence_cauchy_bound(self):
        for L in (Q(1,5),Q(1),Q(2)):
            for dim in (1,2,5):
                e=units(dim)
                z=tuple(Q(j+1,13) for j in range(dim))
                u=lambda k: vecadd(z,c1.scale(Q((-1)**k,k+1),e))
                for N in range(33):
                    for p,q in ((N,N),(N,N+1),(N+3,N+17)):
                        self.assertLessEqual(L*c4.norm2(c1.sub(u(p),z))/2,Q(1,p+1))
                        self.assertLessEqual(L*c4.norm2(c1.sub(u(q),z))/2,Q(1,q+1))
                        self.assertLessEqual(c4.norm2(c1.sub(u(p),u(q))),Q(8,N+1)/L)

    def test_cauchy_squared_control_decreases_to_arbitrary_rational_thresholds(self):
        for c in (Q(1,64),Q(1,8),Q(5)):
            for eps in (Q(1),Q(1,10),Q(1,100)):
                N=int(1/(c*eps*eps))+1
                self.assertLess(Q(1,N+1)/c,eps*eps)
                self.assertGreaterEqual(N,0)

    def test_bounded_basis_sequence_is_not_treated_as_cauchy(self):
        # Finite-coordinate diagnostics of the Hilbert orthonormal-sequence obstruction.
        basis=[tuple(Q(int(i==j)) for j in range(32)) for i in range(32)]
        self.assertTrue(all(c4.norm2(x)==1 for x in basis))
        self.assertTrue(all(c4.norm2(c1.sub(basis[i],basis[i+1]))==2 for i in range(31)))

    def test_zero_midpoint_gap_does_not_force_minimizers_cauchy(self):
        # Every point minimizes the zero objective. A positive gap cannot hold.
        x,y=(Q(0),),(Q(1),)
        self.assertEqual(Q(0),Q(0))
        self.assertLess(-Q(1,8)*c4.norm2(c1.sub(x,y)),0)
        head=MID.split('theorem cauchySeq_of_midpoint_gap',1)[1].split(':= by',1)[0]
        self.assertIn('(hc : 0 < c)',head)

    def test_unbounded_below_affine_component_still_has_minimum_after_penalty(self):
        for tilt in (Q(-7),Q(2),Q(11,3)):
            h=c6.Penalty((Q(0),),(Q(0),),(tilt,),(Q(0),))
            for L in (Q(1,5),Q(1),Q(3)):
                v=(Q(2,7),)
                z=h.prox(v,L)
                self.assertEqual(z,(v[0]-tilt/L,))
                for y in ((Q(-50),),(Q(0),),(Q(73),)):
                    self.assertGreaterEqual(h.objective(v,L,y),h.objective(v,L,z))

    def test_old_certificate_remains_exact_on_continuous_examples(self):
        for T in (1,2,4,8):
            for dim in (1,2,5):
                L,R=Q(3),Q(2)
                f,h,g,prox,center,supplied=c4.physical_example(T,dim,L,R)
                xs=c6.iterate(prox,g,L,supplied[0],T)
                self.assertEqual(xs,supplied)
                *_,values,gram=c4.normalized_data(T,L,R,f,h,g,center,xs)
                rhs,target=cert.candidate(T)
                self.assertEqual(rhs,target)
                self.assertEqual(cert.ev(rhs,values,gram),cert.ev(target,values,gram))
                self.assertGreaterEqual(cert.ev(rhs,values,gram),0)

    def test_canonical_prefixes_remain_coherent(self):
        for dim in (0,1,2,5):
            h=c6.penalty(dim)
            g=lambda x: c1.scale(Q(1,3),x)
            x0=tuple(Q(j-3,4) for j in range(dim))
            long=c6.iterate(h.prox,g,Q(2),x0,24)
            for N in range(25):
                self.assertEqual(c6.iterate(h.prox,g,Q(2),x0,N),long[:N+1])

    def test_continuous_witness_attainment_and_zero_radius(self):
        for T in range(1,33):
            for L in (Q(1,7),Q(1),Q(3)):
                for R in (Q(0),Q(1,3),Q(2)):
                    a=R/(2*T)
                    h=c6.Penalty((Q(0),),(L*a/2,),(L*(a/2-1),),(Q(0),),Q(0))
                    xs=c6.iterate(h.prox,lambda _: (L,),L,(R,),T)
                    self.assertEqual(xs,[(R-k*a,) for k in range(T+1)])
                    self.assertEqual(xs[-1],(R/2,))
                    gap=L*xs[-1][0]+h.h(xs[-1])-h.h((Q(0),))
                    self.assertEqual(gap,L*R*R/(4*T))

    def test_zero_penalty_and_nonconvex_counterexamples_not_supported(self):
        with self.assertRaises(ValueError):
            c6.penalty(1).prox((Q(1),),Q(0))
        with self.assertRaises(ValueError):
            c6.Penalty((Q(-4),),(Q(0),),(Q(0),),(Q(0),))
        # h=-x^2, L=1: the regularized objective remains unbounded below.
        self.assertLess(-Q(100)**2+Q(100)**2/2, -Q(1)**2+Q(1)**2/2)

    def test_source_witness_identity_has_only_the_proved_prefix(self):
        head=RATE.split('theorem hilbertIterate_witness',1)[1].split(':= by',1)[0]
        self.assertIn('(hk : k ≤ n+1)',head)
        self.assertIn('rw [hilbertIterate_eq_finiteDimensional]',RATE)


if __name__ == '__main__':
    unittest.main()
