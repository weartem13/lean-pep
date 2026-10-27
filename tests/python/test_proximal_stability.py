"""C8 exact finite-coordinate regressions, not Lean elaboration.

Closed-form prox maps and rational matrices independently test energy identities,
noncommuting forward/prox composition, exact trajectories and error budgets.
These tests do not execute Classical.choose or prove an infinite-dimensional
limit. Source checks guard the reuse boundaries, not arbitrary proof validity.
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

ROOT = Path(__file__).resolve().parents[2]
PROX = (ROOT/'LeanPEP/ActualFunction/ProximalStability.lean').read_text()
STEP = (ROOT/'LeanPEP/ActualFunction/ForwardBackwardStability.lean').read_text()
ITER = (ROOT/'LeanPEP/ActualFunction/ProximalGradientStability.lean').read_text()
Vec = tuple[Q, ...]
Mat = tuple[Vec, ...]


def add(x: Vec, y: Vec) -> Vec:
    return tuple(a+b for a,b in zip(x,y,strict=True))


def dot(x: Vec, y: Vec) -> Q:
    return sum((a*b for a,b in zip(x,y,strict=True)),Q(0))


def norm2(x: Vec) -> Q:
    return dot(x,x)


def mv(A: Mat, x: Vec) -> Vec:
    if any(len(row) != len(x) for row in A):
        raise ValueError('Matrix dimension mismatch')
    return tuple(dot(row,x) for row in A)


def solve(A: Mat, b: Vec) -> Vec:
    """Exact Gaussian elimination, used only for positive-definite examples."""
    n=len(b)
    if len(A)!=n or any(len(row)!=n for row in A):
        raise ValueError('Non-square system')
    a=[list(row)+[rhs] for row,rhs in zip(A,b,strict=True)]
    for i in range(n):
        p=next((j for j in range(i,n) if a[j][i]),None)
        if p is None:
            raise ValueError('Singular system')
        a[i],a[p]=a[p],a[i]
        pivot=a[i][i]
        a[i]=[v/pivot for v in a[i]]
        for j in range(n):
            if j!=i:
                t=a[j][i]
                a[j]=[u-t*v for u,v in zip(a[j],a[i],strict=True)]
    return tuple(row[-1] for row in a)


def probes(dim: int):
    for t in range(-4,5):
        yield tuple(Q((j+1)*t-j, j+3) for j in range(dim))


def step(prox,g,L,x):
    if L<=0:
        raise ValueError('Positive inverse step required')
    return prox(c1.sub(x,c1.scale(1/L,g(x))),L)


def coupled(L: Q):
    """Smooth Hessian diag(L,0), convex h Hessian [[3L,3L],[3L,3L]].

    Their normalized forward and proximal linear maps do NOT commute.
    The origin is a minimizer; prox is an inverse positive-definite system.
    """
    A=((L,Q(0)),(Q(0),Q(0)))
    B=((3*L,3*L),(3*L,3*L))
    g=lambda x:mv(A,x)
    def prox(v,K):
        return solve(tuple(tuple((K if i==j else Q(0))+B[i][j]
                                 for j in range(2)) for i in range(2)),c1.scale(K,v))
    return g,prox


class ProximalStabilityTests(unittest.TestCase):
    def test_source_reuses_existing_maps_and_support(self):
        self.assertIn('subgradient_of_isProxPoint hL hh hp',PROX)
        self.assertIn('proxMap_spec hp v',PROX)
        self.assertNotIn('Classical.choose',PROX+STEP+ITER)
        self.assertNotRegex(PROX+STEP+ITER,r'\bdef\s+(proxMap|iterate|hilbertIterate)\b')
        self.assertIn('iterate_succ_eq_step',STEP)
        self.assertIn(':= rfl',STEP)

    def test_source_gradient_uses_both_ordered_interpolations(self):
        self.assertIn('pairwise_interpolation hf x y',STEP)
        self.assertIn('pairwise_interpolation hf y x',STEP)
        self.assertIn('ParametricGDScaling.normalizedFirstOrder hf hL',STEP)
        self.assertNotIn('checkUpperCertQ',PROX+STEP+ITER)

    def test_source_hilbert_wrappers_keep_continuity_and_use_c7(self):
        self.assertIn('hasProx_of_continuous hL hh hcont',ITER)
        for name in ('hilbertIterate_norm_sub_le','hilbertIterate_sum_step_energy',
                     'hilbertIterate_last_step_norm_sq_le','hilbertIterate_step_norm_tendsto_zero'):
            head=ITER.split('theorem '+name,1)[1].split(':=',1)[0]
            self.assertIn('[CompleteSpace E]',head)
            self.assertIn('(hcont : Continuous h)',head)
            self.assertNotIn('FiniteDimensional',head)
            self.assertNotIn('(hp :',head)

    def test_source_no_limit_claim_for_inexact_or_point_convergence(self):
        self.assertIn('not convergence of the point sequence',ITER)
        block=ITER.split('theorem inexact_iterate_distance_le',1)[1].split('/--',1)[0]
        self.assertNotIn('hmin',block)
        self.assertIn('revert herr',block)
        self.assertIn('Finset.range N',block)
        self.assertNotIn('Tendsto',block)
        self.assertIn('constant two is not asserted optimal',ITER)
        for word in ('sorry','admit','axiom','opaque','native_decide','unsafe'):
            stripped=re.sub(r'/-.*?-/', '', PROX+STEP+ITER,flags=re.S)
            self.assertNotRegex(stripped,rf'\b{word}\b')

    def test_support_monotonicity(self):
        for dim in (1,2,5):
            h=c6.penalty(dim)
            for L in (Q(1,5),Q(1),Q(7,2)):
                for v,w in zip(probes(dim),reversed(list(probes(dim))),strict=True):
                    p,q=h.prox(v,L),h.prox(w,L)
                    s,t=c1.scale(L,c1.sub(v,p)),c1.scale(L,c1.sub(w,q))
                    self.assertTrue(h.supports(p,s) and h.supports(q,t))
                    self.assertGreaterEqual(dot(c1.sub(s,t),c1.sub(p,q)),0)

    def test_firm_prox_with_negative_tilts(self):
        for dim in (0,1,2,5):
            h=c6.penalty(dim)
            for L in (Q(1,11),Q(1),Q(7)):
                for v,w in zip(probes(dim),reversed(list(probes(dim))),strict=True):
                    d=c1.sub(h.prox(v,L),h.prox(w,L))
                    self.assertLessEqual(norm2(d),dot(d,c1.sub(v,w)))

    def test_prox_two_square_energy(self):
        for dim in (0,1,2,5):
            h=c6.penalty(dim)
            for L in (Q(1,3),Q(2),Q(11)):
                for v in probes(dim):
                    w=tuple(Q(j+1,7) for j in range(dim))
                    d=c1.sub(h.prox(v,L),h.prox(w,L)); a=c1.sub(v,w)
                    self.assertLessEqual(norm2(d)+norm2(c1.sub(a,d)),norm2(a))

    def test_prox_residual_nonexpansive(self):
        h=c6.penalty(5)
        for L in (Q(1,7),Q(1),Q(5)):
            for v,w in zip(probes(5),reversed(list(probes(5))),strict=True):
                rv=c1.sub(v,h.prox(v,L)); rw=c1.sub(w,h.prox(w,L))
                self.assertLessEqual(norm2(c1.sub(rv,rw)),norm2(c1.sub(v,w)))

    def test_nonconvex_prox_can_expand(self):
        # h(x)=-x^2/4, L=1: prox(v)=2v exists uniquely but is expansive.
        self.assertGreater((2*Q(1)-2*Q(0))**2,(Q(1)-Q(0))**2)

    def test_normalized_gradient_cocoercivity(self):
        for dim in (1,2,5):
            for L in (Q(1,5),Q(1),Q(9,2)):
                ex=c5.example(dim,L)
                for x,y in zip(probes(dim),reversed(list(probes(dim))),strict=True):
                    d=c1.scale(1/L,c1.sub(ex.g(x),ex.g(y)))
                    self.assertLessEqual(norm2(d),dot(d,c1.sub(x,y)))

    def test_lipschitz_without_convexity_is_not_cocoercivity(self):
        # g(x)=-x is 1-Lipschitz, but comes from a concave quadratic.
        g=lambda x:-x
        x,y=Q(1),Q(0)
        self.assertGreater((g(x)-g(y))**2,(g(x)-g(y))*(x-y))
        self.assertGreater(((x-g(x))-(y-g(y)))**2,(x-y)**2)

    def test_forward_map_energy(self):
        for dim in (1,2,5):
            for L in (Q(1,5),Q(1),Q(9,2)):
                ex=c5.example(dim,L)
                for x,y in zip(probes(dim),reversed(list(probes(dim))),strict=True):
                    a=c1.sub(x,y)
                    b=c1.sub(c1.sub(x,c1.scale(1/L,ex.g(x))),c1.sub(y,c1.scale(1/L,ex.g(y))))
                    self.assertLessEqual(norm2(b)+norm2(c1.sub(a,b)),norm2(a))

    def test_noncommuting_forward_prox_energy(self):
        for L in (Q(1,5),Q(1),Q(3)):
            g,p=coupled(L)
            for x in probes(2):
                for y in probes(2):
                    a=c1.sub(x,y); c=c1.sub(step(p,g,L,x),step(p,g,L,y))
                    self.assertLessEqual(norm2(c)+norm2(c1.sub(a,c))/2,norm2(a))
            x=(Q(1),Q(1))
            F=lambda v:c1.sub(v,c1.scale(1/L,g(v)))
            self.assertNotEqual(p(F(x),L),F(p(x,L)))

    def test_full_step_is_not_in_general_firm(self):
        g,p=coupled(Q(1)); a=(Q(1),Q(1)); c=step(p,g,Q(1),a)
        self.assertEqual(c,(Q(-3,7),Q(4,7)))
        self.assertGreater(norm2(c),dot(c,a))
        self.assertGreater(norm2(c)+norm2(c1.sub(a,c)),norm2(a))
        self.assertLessEqual(norm2(c)+norm2(c1.sub(a,c))/2,norm2(a))

    def test_initial_point_stability_all_prefixes(self):
        for dim in (1,2,5):
            for L in (Q(1,3),Q(1),Q(5)):
                ex=c5.example(dim,L); points=list(probes(dim))
                xs=c6.iterate(ex.prox,ex.g,L,points[0],24)
                ys=c6.iterate(ex.prox,ex.g,L,points[-1],24)
                for x,y in zip(xs,ys,strict=True):
                    self.assertLessEqual(norm2(c1.sub(x,y)),norm2(c1.sub(points[0],points[-1])))

    def test_fejer_energy_each_step(self):
        for dim in (1,2,5):
            L=Q(3); ex=c5.example(dim,L); star=ex.minimum()
            for x0 in probes(dim):
                xs=c6.iterate(ex.prox,ex.g,L,x0,16)
                for x,y in zip(xs,xs[1:]):
                    self.assertLessEqual(norm2(c1.sub(y,star))+norm2(c1.sub(y,x))/2,norm2(c1.sub(x,star)))

    def test_telescoped_energy_and_zero_horizon(self):
        for dim in (0,1,2,5):
            if dim==0:
                xs=[()]*33; star=()
            else:
                ex=c5.example(dim,Q(2)); star=ex.minimum()
                xs=c6.iterate(ex.prox,ex.g,Q(2),next(probes(dim)),32)
            energy=Q(0)
            for N,x in enumerate(xs):
                if N:
                    energy+=norm2(c1.sub(x,xs[N-1]))/2
                self.assertLessEqual(norm2(c1.sub(x,star))+energy,norm2(c1.sub(xs[0],star)))
            self.assertEqual(norm2(c1.sub(xs[0],star))+Q(0),norm2(c1.sub(xs[0],star)))

    def test_step_norms_are_antitone(self):
        for L in (Q(1,7),Q(1),Q(5)):
            for dim in (1,2,5):
                ex=c5.example(dim,L); xs=c6.iterate(ex.prox,ex.g,L,next(probes(dim)),32)
                ns=[norm2(c1.sub(y,x)) for x,y in zip(xs,xs[1:])]
                self.assertTrue(all(b<=a for a,b in zip(ns,ns[1:])))

    def test_last_step_square_bound(self):
        for dim in (1,2,5):
            ex=c5.example(dim,Q(3)); xs=c6.iterate(ex.prox,ex.g,Q(3),next(probes(dim)),65)
            radius2=norm2(c1.sub(xs[0],ex.minimum()))
            for N,(x,y) in enumerate(zip(xs,xs[1:])):
                self.assertLessEqual((N+1)*norm2(c1.sub(y,x)),2*radius2)

    def test_zero_radius_nonzero_component_cancellation(self):
        for dim in (1,2,5):
            ex=c5.example(dim,Q(3)); star=ex.minimum()
            self.assertNotEqual(ex.g(star),(Q(0),)*dim)
            xs=c6.iterate(ex.prox,ex.g,Q(3),star,32)
            self.assertEqual(xs,[star]*33)

    def test_witness_energy_is_not_claimed_sharp(self):
        for T in range(1,33):
            a,f,h,g,p,xs=c4.witness(T,Q(3),Q(2))
            energy=sum(((y-x)**2/2 for x,y in zip(xs,xs[1:])),Q(0))
            self.assertLessEqual(xs[-1]**2+energy,Q(4))
            self.assertEqual(f(xs[-1])+h(xs[-1])-f(Q(0))-h(Q(0)),Q(3)*4/(4*T))
            self.assertLess(T*(xs[-1]-xs[-2])**2,8)  # derived bound has slack

    def test_original_certificate_on_same_actual_trajectories(self):
        for T in (1,2,4,8):
            f,h,g,p,c,xs=c4.physical_example(T,2,Q(3),Q(2))
            *_,vals,gram=c4.normalized_data(T,Q(3),Q(2),f,h,g,c,xs)
            rhs,target=cert.candidate(T)
            self.assertEqual(rhs,target)
            self.assertEqual(cert.ev(rhs,vals,gram),cert.ev(target,vals,gram))
            self.assertGreaterEqual(cert.ev(rhs,vals,gram),0)
            self.assertLessEqual(norm2(c1.sub(xs[-1],c)),norm2(c1.sub(xs[0],c)))

    def test_inexact_step_error_budget(self):
        for L in (Q(1,5),Q(1),Q(3)):
            ex=c5.example(1,L); x0=(Q(2),); xs=c6.iterate(ex.prox,ex.g,L,x0,32)
            z=(Q(5,2),); budget=Q(1,2)
            self.assertLessEqual(norm2(c1.sub(z,xs[0])),budget**2)
            for k in range(32):
                err=Q((-1)**k,k+3)
                z=add(step(ex.prox,ex.g,L,z),(err,)); budget+=abs(err)
                self.assertLessEqual(norm2(c1.sub(z,xs[k+1])),budget**2)

    def test_gradient_error_scale_and_accumulation(self):
        for L in (Q(1,5),Q(1),Q(7)):
            ex=c5.example(1,L); xs=c6.iterate(ex.prox,ex.g,L,(Q(2),),24)
            z=(Q(2),); budget=Q(0)
            for k in range(24):
                e=Q((-1)**k,k+2)
                exact=step(ex.prox,ex.g,L,z)
                znext=ex.prox(c1.sub(z,c1.scale(1/L,add(ex.g(z),(e,)))),L)
                self.assertLessEqual(norm2(c1.sub(znext,exact)),(abs(e)/L)**2)
                budget+=abs(e)/L; z=znext
                self.assertLessEqual(norm2(c1.sub(z,xs[k+1])),budget**2)

    def test_error_budget_scaling_is_necessary(self):
        # f=h=0, exact map I; aligned errors attain the distance budget.
        for L in (Q(1,4),Q(3)):
            e=Q(1); z=Q(0)
            for N in range(1,9):
                z-=e/L
                self.assertEqual(abs(z),N*abs(e)/L)
                if L<1:
                    self.assertGreater(abs(z),N*abs(e))
        # Omitting the per-step sum falsely predicts zero distance from x0=0.
        exact=[Q(0)]*3
        approximate=[Q(0),Q(1),Q(2)]
        self.assertGreater(abs(approximate[2]-exact[2]),abs(approximate[0]-exact[0]))

    def test_additive_function_offsets_preserve_stability(self):
        ex=c5.example(2,Q(3))
        shifted=c5.Example(ex.curvature,ex.linear,ex.tilt,ex.lam,ex.shift,Q(999),Q(-333))
        for x0 in probes(2):
            self.assertEqual(c6.iterate(ex.prox,ex.g,Q(3),x0,12),
                             c6.iterate(shifted.prox,shifted.g,Q(3),x0,12))


if __name__=='__main__':
    unittest.main()
