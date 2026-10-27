"""C9 exact finite diagnostics, not a proof of limits or a Lean elaborator.

The old closed-form prox/trajectory mirrors are reused. Rational trajectories
with known closed forms exercise Fejer balls, subsequence promotion, fixed-point
identification and objective-rate scaling. Finite samples do not establish
compactness, infinite limits, or execution of Classical.choose.
"""
from __future__ import annotations
from fractions import Fraction as Q
from pathlib import Path
import re
import unittest

from tests.python import test_composite_proximal as c1
from tests.python import test_composite_minimizer as c5
from tests.python import test_proximal_canonical as c6
from tests.python import test_proximal_gradient_scaling as c4
from tests.python import test_proximal_gradient_certificate as cert
from tests.python import test_proximal_stability as c8

ROOT = Path(__file__).resolve().parents[2]
FEJER = (ROOT/'LeanPEP/ActualFunction/FejerConvergence.lean').read_text()
CONV = (ROOT/'LeanPEP/ActualFunction/ProximalGradientConvergence.lean').read_text()
OBJ = (ROOT/'LeanPEP/ActualFunction/ProximalGradientObjectiveConvergence.lean').read_text()


def statement(source: str, name: str) -> str:
    return source.split('theorem '+name, 1)[1].split(':=', 1)[0]


def strip_comments(source: str) -> str:
    return re.sub(r'--[^\n]*', '', re.sub(r'/-.*?-/', '', source, flags=re.S))


def flat_example(L: Q) -> c5.Example:
    # F(x,y)=L*x^2/4 + constant; g_star and the h support cancel nontrivially.
    return c5.Example((L/2,Q(0)), (Q(3),Q(-2)), (Q(-3),Q(2)),
                      (Q(0),Q(0)), (Q(0),Q(0)))


class ProximalConvergenceTests(unittest.TestCase):
    def test_metric_lemma_has_no_optimization_or_dimension_assumptions(self):
        for name in ('tendsto_of_antitone_dist_of_subsequence',
                     'fixed_of_subsequence_of_residual', 'tendsto_fixed_of_subsequence',
                     'exists_tendsto_fixed_of_compact'):
            head=statement(FEJER,name)
            for word in ('HasProx','FiniteDimensional','CompleteSpace','InnerProductSpace','GramPEP'):
                self.assertNotIn(word,head)
        self.assertIn('hK.tendsto_subseq hu',FEJER)
        self.assertIn('(hanti hn).trans_lt',FEJER)
        self.assertIn('hres.comp hφ',FEJER)

    def test_reuses_old_iteration_and_stability(self):
        src=strip_comments(FEJER+CONV+OBJ)
        self.assertNotRegex(src,r'\b(?:def|abbrev)\s+(?:iterate|proxMap|hilbertIterate|finiteDimensionalIterate)\b')
        self.assertNotIn('Classical.choose',src)
        for dep in ('iterate_step_norm_tendsto_zero','iterate_distance_antitone',
                    'forwardBackwardStep_lipschitz','forwardBackwardStep_fixed_iff_minimizer',
                    'run_eq_iterate'):
            self.assertIn(dep,CONV)
        for token in ('sorry','admit','axiom','opaque','native_decide','unsafe','implemented_by'):
            self.assertNotRegex(src,rf'\b{token}\b')

    def test_compactness_and_unique_limit_boundaries(self):
        self.assertIn('(hK : IsCompact K)', statement(CONV,'iterate_tendsto_of_compact'))
        self.assertIn('(hK : IsCompact K)', statement(CONV,'hilbertIterate_tendsto_of_compact'))
        head=statement(CONV,'finiteDimensionalIterate_tendsto ')
        self.assertIn('[FiniteDimensional ℝ E]',head)
        self.assertNotIn('hunique',head)
        self.assertNotIn('Continuous h',head)
        self.assertNotIn('HasProx',head)
        self.assertIn('∃ z,',head)
        self.assertIn('hunique',statement(CONV,'finiteDimensionalIterate_tendsto_of_unique'))

    def test_objective_proof_uses_old_rate_not_point_convergence(self):
        self.assertIn('ProximalGradientScaling.upper_firstOrder_of_minimizer',OBJ)
        self.assertNotIn('import LeanPEP.ActualFunction.ProximalGradientConvergence',OBJ)
        for name in ('run_objective_tendsto','hilbertIterate_objective_tendsto'):
            head=statement(OBJ,name)
            self.assertNotIn('FiniteDimensional',head)
            self.assertNotIn('IsCompact',head)
            self.assertNotIn('HasProx',head)
        self.assertIn('(hcont : Continuous h)',statement(OBJ,'hilbertIterate_objective_tendsto'))
        self.assertIn('(hrun : ∀ N,',statement(OBJ,'run_objective_tendsto'))
        self.assertIn('refine ⟨N+1, ?_⟩',OBJ)

    def test_no_new_rate_or_inexact_point_convergence_claim(self):
        src=strip_comments(CONV+OBJ)
        self.assertNotIn('inexact',src)
        self.assertNotIn('checkUpperCertQ',src)
        self.assertNotIn('upperCertQ',src)
        self.assertNotIn('Weak',src)
        self.assertNotIn('isCompact_closedBall',OBJ)
        self.assertIn('isCompact_closedBall',CONV)

    def test_flat_minimizer_set_closed_form_trajectory(self):
        for L in (Q(1,5),Q(1),Q(7)):
            ex=flat_example(L)
            for x0 in ((Q(2),Q(5)),(Q(-3),Q(-2)),(Q(0),Q(4))):
                xs=c6.iterate(ex.prox,ex.g,L,x0,40)
                for k,x in enumerate(xs):
                    self.assertEqual(x,(x0[0]/(2**k),x0[1]))

    def test_reference_minimizer_need_not_be_limit(self):
        ex=flat_example(Q(1)); ref=(Q(0),Q(0)); lim=(Q(0),Q(5))
        xs=c6.iterate(ex.prox,ex.g,Q(1),(Q(2),Q(5)),32)
        self.assertEqual(ex.f(ref)+ex.h(ref),ex.f(lim)+ex.h(lim))
        self.assertEqual(c8.step(ex.prox,ex.g,Q(1),lim),lim)
        self.assertNotEqual(ref,lim)
        self.assertGreaterEqual(c8.norm2(c1.sub(xs[-1],ref)),25)
        self.assertEqual(c8.norm2(c1.sub(xs[-1],lim)),Q(4,4**32))

    def test_distances_to_every_flat_minimizer_are_antitone(self):
        ex=flat_example(Q(3)); xs=c6.iterate(ex.prox,ex.g,Q(3),(Q(2),Q(5)),32)
        for s in range(-7,8):
            star=(Q(0),Q(s))
            d=[c8.norm2(c1.sub(x,star)) for x in xs]
            self.assertTrue(all(b<=a for a,b in zip(d,d[1:])))

    def test_fejer_ball_contains_every_tested_prefix(self):
        for dim in (1,2,5):
            ex=c5.example(dim,Q(3)); star=ex.minimum()
            for x0 in list(c5.probes(dim))[::2]:
                xs=c6.iterate(ex.prox,ex.g,Q(3),x0,32)
                r2=c8.norm2(c1.sub(x0,star))
                self.assertTrue(all(c8.norm2(c1.sub(x,star))<=r2 for x in xs))

    def test_subsequence_threshold_controls_whole_tail(self):
        # Exact squared-distance analogue of the epsilon proof; sparse phi(k)=k^2.
        ex=flat_example(Q(1)); lim=(Q(0),Q(5))
        xs=c6.iterate(ex.prox,ex.g,Q(1),(Q(2),Q(5)),100)
        for K in range(1,10):
            N=K*K; epsilon2=Q(5,4**N)
            self.assertLess(c8.norm2(c1.sub(xs[N],lim)),epsilon2)
            self.assertTrue(all(c8.norm2(c1.sub(x,lim))<epsilon2 for x in xs[N:]))

    def test_noncommuting_quadratic_closed_form(self):
        for L in (Q(1,5),Q(1),Q(3)):
            g,p=c8.coupled(L)
            for x0 in ((Q(1),Q(1)),(Q(-2),Q(3)),(Q(5),Q(0))):
                xs=c6.iterate(p,g,L,x0,32)
                for k in range(1,len(xs)):
                    y0=x0[1]
                    self.assertEqual(xs[k],(Q(-3,7)*Q(4,7)**(k-1)*y0,Q(4,7)**k*y0))

    def test_noncommuting_objective_obeys_old_sharp_upper(self):
        for L in (Q(1,7),Q(1),Q(5)):
            g,p=c8.coupled(L)
            x0=(Q(-2),Q(3)); xs=c6.iterate(p,g,L,x0,32)
            for k,x in enumerate(xs[1:],1):
                F=L*x[0]**2/2+3*L*(x[0]+x[1])**2/2
                self.assertGreaterEqual(F,0)
                self.assertLessEqual(F,L*c8.norm2(x0)/(4*k))

    def test_objective_majorants_all_dimensions(self):
        for dim in (1,2,5):
            for L in (Q(1,4),Q(1),Q(3)):
                ex=c5.example(dim,L); star=ex.minimum()
                x0=next(c5.probes(dim)); xs=c6.iterate(ex.prox,ex.g,L,x0,32)
                Fstar=ex.f(star)+ex.h(star); C=L*c8.norm2(c1.sub(x0,star))/4
                for k,x in enumerate(xs[1:],1):
                    gap=ex.f(x)+ex.h(x)-Fstar
                    self.assertGreaterEqual(gap,0)
                    self.assertLessEqual(gap,C/k)

    def test_objective_offsets_do_not_change_trajectory_or_gap(self):
        ex=c5.example(2,Q(3))
        shifted=c5.Example(ex.curvature,ex.linear,ex.tilt,ex.lam,ex.shift,Q(999),Q(-333))
        star=ex.minimum(); x0=(Q(2),Q(-4))
        xs=c6.iterate(ex.prox,ex.g,Q(3),x0,32)
        ys=c6.iterate(shifted.prox,shifted.g,Q(3),x0,32)
        self.assertEqual(xs,ys)
        for x in xs:
            self.assertEqual(ex.f(x)+ex.h(x)-ex.f(star)-ex.h(star),
                             shifted.f(x)+shifted.h(x)-shifted.f(star)-shifted.h(star))

    def test_zero_dimension_is_included(self):
        ex=c5.Example((),(),(),(),())
        xs=c6.iterate(ex.prox,ex.g,Q(3),(),32)
        self.assertEqual(xs,[()]*33)
        self.assertTrue(all(ex.f(x)+ex.h(x)==ex.f(())+ex.h(()) for x in xs))

    def test_zero_radius_nonzero_component_cancellation(self):
        ex=flat_example(Q(3)); star=(Q(0),Q(7))
        self.assertNotEqual(ex.g(star),(Q(0),Q(0)))
        xs=c6.iterate(ex.prox,ex.g,Q(3),star,32)
        self.assertEqual(xs,[star]*33)

    def test_old_witness_has_correct_post_prefix_behavior(self):
        for T in range(1,17):
            for R in (Q(0),Q(1),Q(3,2)):
                a,f,h,g,p,old=c4.witness(T,Q(3),R)
                xs=[R]
                for _ in range(2*T+3): xs.append(p(xs[-1]-g(xs[-1])/3))
                self.assertEqual(xs[:T+1],old)
                self.assertEqual(xs[2*T:],[Q(0)]*4)
                self.assertEqual(f(xs[T])+h(xs[T])-f(Q(0))-h(Q(0)),3*R**2/(4*T))
                if R>0:
                    self.assertNotEqual(xs[2*T+1],R-(2*T+1)*a)

    def test_old_certificate_still_on_identical_actual_data(self):
        for T in (1,2,4,8):
            f,h,g,p,c,xs=c4.physical_example(T,2,Q(3),Q(2))
            *_,values,gram=c4.normalized_data(T,Q(3),Q(2),f,h,g,c,xs)
            rhs,target=cert.candidate(T)
            self.assertEqual(rhs,target)
            self.assertEqual(cert.ev(rhs,values,gram),cert.ev(target,values,gram))
            self.assertGreaterEqual(cert.ev(rhs,values,gram),0)

    def test_compact_fejer_without_residual_is_insufficient(self):
        # T=-I, alternating exact orbit: compact and Fejer to fixed point 0,
        # but the step residual is constantly 2 and the even cluster is not fixed.
        xs=[Q((-1)**k) for k in range(20)]
        self.assertEqual([x*x for x in xs],[Q(1)]*20)
        self.assertEqual([abs(-x-x) for x in xs],[Q(2)]*20)
        self.assertNotEqual(-xs[0],xs[0])

    def test_residual_and_compactness_without_fejer_are_insufficient(self):
        # Generic metric lemma, not a claimed exact PG orbit: T=I and u alternates.
        xs=[Q((-1)**k) for k in range(20)]
        self.assertTrue(all(x-x==0 for x in xs))
        ds=[abs(x-1) for x in xs]
        self.assertGreater(ds[1],ds[0])

    def test_noncofinal_sampling_does_not_inherit_residual_limit(self):
        # u(0)=1, u(k)=0 for k>0, T=0; constant sampling keeps the exceptional term.
        xs=[Q(1)]+[Q(0)]*20
        residual=[abs(x) for x in xs]
        self.assertEqual(residual[1:],[Q(0)]*20)
        sampled=[xs[0]]*20
        self.assertNotEqual(Q(0),sampled[-1])
        self.assertIn('(hφ : Tendsto φ atTop atTop)',statement(FEJER,'fixed_of_subsequence_of_residual'))

    def test_minimizer_premise_cannot_be_removed(self):
        # f=0, h=-x, L=1: total convex continuous prox exists, but T(x)=x+1.
        prox=lambda v,L:(v[0]+1/L,)
        g=lambda x:(Q(0),)
        xs=c6.iterate(prox,g,Q(1),(Q(0),),32)
        self.assertEqual(xs,[(Q(k),) for k in range(33)])
        self.assertLess(-xs[-1][0],-xs[0][0])

    def test_small_inexact_steps_are_not_exact_convergence(self):
        # For T=I, harmonic perturbations have decreasing vanishing step sizes.
        # Every dyadic block still moves at least 1/2; this is a finite diagnostic.
        for N in (1,2,4,8,16,32,64,128):
            block=sum((Q(1,k) for k in range(N+1,2*N+1)),Q(0))
            self.assertGreaterEqual(block,Q(1,2))
        self.assertNotIn('inexact_',strip_comments(CONV))

    def test_positive_time_and_lower_gap_bound_are_both_respected(self):
        C=Q(3)
        a=[Q(10**9)]+[C/k for k in range(1,65)]
        for k in range(64): self.assertLessEqual(a[k+1],C/(k+1))
        self.assertGreater(a[0],C)
        # An upper bound alone permits arbitrarily negative gaps.
        bad=[Q(-k) for k in range(65)]
        self.assertTrue(all(bad[k+1]<=C/(k+1) for k in range(64)))
        self.assertLess(bad[-1],0)
        self.assertIn('(ha : ∀ k, 0 ≤ a k)',statement(OBJ,'gap_tendsto_zero_of_succ_bound'))


if __name__ == '__main__':
    unittest.main()
