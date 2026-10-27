"""C11 exact diagnostics; not a Lean interpreter or a proof of a limit.

All trajectories here use rational closed-form maps. Infinite-series budgets
are explicit geometric formulas, not floating-point or truncated-tsum tests.
Boundary examples do not execute Classical.choose or prove Hilbert compactness.
"""
from __future__ import annotations
from fractions import Fraction as Q
from pathlib import Path
import re
import unittest

from tests.python import test_composite_proximal as c1
from tests.python import test_composite_minimizer as c5
from tests.python import test_proximal_canonical as c6
from tests.python import test_proximal_stability as c8
from tests.python import test_proximal_gradient_certificate as cert

ROOT = Path(__file__).resolve().parents[2]
SCALAR = (ROOT/'LeanPEP/ActualFunction/SummablePerturbation.lean').read_text()
WEAK = (ROOT/'LeanPEP/ActualFunction/WeakQuasiFejerConvergence.lean').read_text()
ALG = (ROOT/'LeanPEP/ActualFunction/ProximalGradientInexactConvergence.lean').read_text()
Vec = tuple[Q, ...]


def strip_comments(s: str) -> str:
    return re.sub(r'--[^\n]*', '', re.sub(r'/-.*?-/', '', s, flags=re.S))


def statement(s: str, name: str) -> str:
    return s.split('theorem '+name, 1)[1].split(':=', 1)[0]


def geom_budget(a: Q, r: Q, n: int) -> tuple[Q, Q, Q]:
    """Term, prefix sum and infinite tail of an exact geometric budget."""
    if a < 0 or not 0 <= r < 1 or n < 0:
        raise ValueError('Requires nonnegative budget, 0 <= ratio < 1, n >= 0')
    return a*r**n, a*(1-r**n)/(1-r), a*r**n/(1-r)


def norm_le_norm_add(a2: Q, b2: Q, e: Q) -> bool:
    """sqrt(a2) <= sqrt(b2)+e, preserving sign before squaring."""
    if min(a2,b2,e) < 0:
        raise ValueError('Nonnegative norms and error required')
    z=a2-b2-e*e
    return z <= 0 or z*z <= 4*b2*e*e


def axis(dim: int, q: Q, k: int = 0) -> Vec:
    return tuple(q if j == k % dim else Q(0) for j in range(dim))


def orbit(T, x0: Vec, a: Q, r: Q, N: int):
    if N < 0:
        raise ValueError('Nonnegative horizon required')
    xs=[x0]
    for k in range(N):
        e=axis(len(x0),(-1 if k % 3 == 1 else 1)*a*r**k,k)
        xs.append(c8.add(T(xs[-1]),e))
    return xs


class ProximalInexactConvergenceTests(unittest.TestCase):
    def test_source_same_step_and_no_trust_bypass(self):
        code=strip_comments(SCALAR+WEAK+ALG)
        for bad in ('sorry','admit','axiom','opaque','unsafe','native_decide','implemented_by'):
            self.assertNotRegex(code,rf'\b{bad}\b')
        self.assertNotRegex(code,r'\b(?:def|abbrev)\s+(?:iterate|proxMap|hilbertIterate|forwardBackwardStep)\b')
        self.assertNotIn('Classical.choose',code)
        self.assertNotIn('checkUpperCertQ',code)
        self.assertIn('forwardBackwardStep_energy hp hf hL hh',ALG)
        self.assertIn('forwardBackwardStep_fixed_iff_minimizer',ALG)

    def test_source_scalar_budget_is_a_real_summable_tail(self):
        self.assertIn('(∑\' k, eps k) - ∑ k ∈ Finset.range n, eps k',SCALAR)
        for name in ('errorTail_nonneg','errorTail_tendsto_zero','exists_limit_of_summable_error'):
            self.assertIn('Summable eps',statement(SCALAR,name))
        self.assertIn('hs.hasSum.tendsto_sum_nat',SCALAR)
        self.assertIn('tendsto_atTop_ciInf',SCALAR)

    def test_source_distances_converge_without_antitone_premise(self):
        head=statement(WEAK,'inner_limits_eq_of_distance_limits')
        self.assertIn('‖u n-z‖',head); self.assertIn('‖u n-w‖',head)
        self.assertNotIn('Antitone',head)
        for token in ('[lz.NeBot]','[lw.NeBot]','lz ≤ atTop','lw ≤ atTop'):
            self.assertIn(token,head)
        self.assertIn('distance_sq_difference_tendsto hz z w',WEAK)
        self.assertIn('distance_sq_difference_tendsto hw z w',WEAK)

    def test_source_hilbert_weak_has_no_finite_dimensional_premise(self):
        head=statement(ALG,'inexact_weak_tendsto_hilbert ')
        for token in ('[CompleteSpace E]','Continuous h','Summable eps','toWeakSpace ℝ E'):
            self.assertIn(token,head)
        for token in ('HasProx','SeparableSpace','FiniteDimensional','IsCompact','hres'):
            self.assertNotIn(token,head)
        self.assertIn('isCompact_weakRiesz_closedBall',WEAK)
        self.assertIn('fixed_of_weakRiesz_cluster hT hB hres',WEAK)

    def test_source_positive_energy_margin_and_distinct_residual(self):
        head=statement(SCALAR,'residual_tendsto_zero ')
        self.assertIn('(hc : 0 < c)',head)
        self.assertIn('c*‖T x-x‖^2',head)
        self.assertIn('‖u (n+1)-T (u n)‖',head)
        self.assertIn('‖T (u n)-u n‖',head)
        self.assertIn('distance_has_limit hT hs herr hp',SCALAR)
        self.assertIn('hs.tendsto_atTop_zero',SCALAR)
        self.assertIn('Real.sqrt_sq (norm_nonneg _)',SCALAR)

    def test_source_strong_convergence_has_explicit_compactness_boundary(self):
        self.assertIn('IsCompact K',statement(WEAK,'exists_strong_tendsto_fixed_of_compact'))
        head=statement(ALG,'inexact_tendsto_finiteDimensional_analytic')
        self.assertIn('[FiniteDimensional ℝ E]',head)
        self.assertNotIn('Continuous h',head)
        self.assertNotIn('(hp :',head)
        self.assertIn('hK.tendsto_subseq',WEAK)
        self.assertIn('fixed_of_subsequence_of_residual',WEAK)

    def test_source_oracle_errors_are_norm_summable_and_scaled(self):
        head=statement(ALG,'inexact_oracle_prox_weak_tendsto ')
        self.assertIn('Summable (fun n => ‖e n‖)',head)
        self.assertIn('Summable delta',head)
        self.assertIn('delta n+(L : ℝ)⁻¹*‖e n‖',ALG)
        self.assertIn('forwardBackwardStep_oracle_error',ALG)
        self.assertNotIn('Summable e)',head)

    def test_source_limit_is_not_prescribed_and_no_noisy_rate_claim(self):
        head=statement(ALG,'inexact_weak_tendsto ')
        self.assertIn('∃ z,',head); self.assertNotIn('hunique',head)
        self.assertIn('hunique',statement(ALG,'inexact_weak_tendsto_of_unique'))
        self.assertNotRegex(strip_comments(ALG),r'\btheorem\s+\w*(?:objective|tight|rate)\w*')
        self.assertNotIn('Continuous T',statement(WEAK,'exists_weak_tendsto_fixed_of_distance_limits'))

    def test_geometric_tails_and_prefixes_exact(self):
        for a in (Q(0),Q(1,9),Q(3)):
            for r in (Q(0),Q(1,3),Q(3,4)):
                for n in range(65):
                    term,prefix,tail=geom_budget(a,r,n)
                    self.assertEqual(prefix+tail,a/(1-r))
                    self.assertEqual(geom_budget(a,r,n+1)[2],tail-term)
                    self.assertEqual(prefix,sum((a*r**k for k in range(n)),Q(0)))
                    self.assertGreaterEqual(tail,0)

    def test_tail_correction_not_raw_distance_is_antitone(self):
        a,r=Q(2),Q(1,2)
        raw=[geom_budget(a,r,n)[1] for n in range(33)]
        corrected=[x+geom_budget(a,r,n)[2] for n,x in enumerate(raw)]
        self.assertTrue(all(y>x for x,y in zip(raw,raw[1:])))
        self.assertEqual(corrected,[a/(1-r)]*33)

    def test_scalar_quasi_fejer_with_downward_slack(self):
        for rho in (Q(0),Q(1,3),Q(1)):
            a,r=Q(1,5),Q(2,3); x=Q(7,3); budget=a/(1-r)
            for n in range(65):
                e,_,tail=geom_budget(a,r,n)
                y=rho*x+e
                self.assertLessEqual(y+geom_budget(a,r,n+1)[2],x+tail)
                self.assertLessEqual(y,Q(7,3)+budget)
                self.assertGreaterEqual(y,0)
                x=y

    def test_invalid_budget_arguments_are_not_silently_coerced(self):
        for a,r,n in ((Q(-1),Q(1,2),1),(Q(1),Q(1),1),(Q(1),Q(-1),1),(Q(1),Q(0),-1)):
            with self.assertRaises(ValueError): geom_budget(a,r,n)
        with self.assertRaises(ValueError): norm_le_norm_add(Q(1),Q(1),Q(-1))

    def test_affine_energy_and_uniform_budget_all_edges(self):
        for dim in (0,1,2,5):
            p=tuple(Q(j+1,7) for j in range(dim)); R=Q(3) if dim else Q(0)
            for rho in (Q(0),Q(1,3),Q(3,4),Q(1)):
                T=lambda x:c8.add(p,c1.scale(rho,c1.sub(x,p)))
                for a,r in ((Q(0),Q(1,2)),(Q(1,5),Q(1,3)),(Q(3),Q(3,4))):
                    xs=orbit(T,c8.add(p,axis(dim,R)),a,r,32); B=R+a/(1-r)
                    for n,(x,y) in enumerate(zip(xs,xs[1:])):
                        e=a*r**n; tx=T(x); D=c8.norm2(c1.sub(x,p)); Dnext=c8.norm2(c1.sub(y,p))
                        residual=c8.norm2(c1.sub(tx,x))
                        self.assertLessEqual(c8.norm2(c1.sub(tx,p))+residual/2,D)
                        self.assertLessEqual(residual/2,D-Dnext+2*B*e+e*e)
                        self.assertLessEqual(Dnext,B*B)
                        self.assertTrue(norm_le_norm_add(Dnext,D,e))

    def test_noncommuting_composition_perturbed_energy(self):
        for L in (Q(1,5),Q(1),Q(7)):
            g,p=c8.coupled(L); T=lambda x:c8.step(p,g,L,x)
            a,r=Q(2,5),Q(2,3); B=Q(1)+a/(1-r)
            xs=orbit(T,(Q(1),Q(0)),a,r,64)
            for n,(x,y) in enumerate(zip(xs,xs[1:])):
                e=a*r**n; res=c8.norm2(c1.sub(T(x),x))
                self.assertLessEqual(res/2,c8.norm2(x)-c8.norm2(y)+2*B*e+e*e)
                self.assertLessEqual(c8.norm2(y),B*B)

    def test_exact_residual_differs_from_adjacent_step(self):
        x=Q(1); eps=Q(1,5); T=lambda z:z
        y=T(x)+eps
        self.assertEqual(T(x)-x,0)
        self.assertEqual(y-x,eps)
        self.assertNotEqual(abs(T(x)-x),abs(y-x))

    def test_exact_zero_noise_reproduces_existing_recursion(self):
        for dim in (1,2,5):
            ex=c5.example(dim,Q(3)); T=lambda x:c8.step(ex.prox,ex.g,Q(3),x)
            x0=next(c8.probes(dim))
            self.assertEqual(orbit(T,x0,Q(0),Q(1,2),32),c6.iterate(ex.prox,ex.g,Q(3),x0,32))

    def test_simultaneous_gradient_and_prox_output_errors(self):
        for dim in (1,2,5):
            for L in (Q(1,4),Q(1),Q(5)):
                ex=c5.example(dim,L); u=next(c8.probes(dim))
                for n in range(32):
                    e=axis(dim,Q(1,3)*Q(1,2)**n,n)
                    d=Q(1,7)*Q(2,3)**n
                    q=ex.prox(c1.sub(u,c1.scale(1/L,c8.add(ex.g(u),e))),L)
                    y=c8.add(q,axis(dim,(-1)**n*d,n+1))
                    eta=d+Q(1,3)*Q(1,2)**n/L
                    self.assertLessEqual(c8.norm2(c1.sub(y,q)),d*d)
                    self.assertLessEqual(c8.norm2(c1.sub(y,c8.step(ex.prox,ex.g,L,u))),eta*eta)
                    u=y

    def test_missing_inverse_smoothness_factor_is_detected(self):
        L=Q(1,4); e=Q(1); delta=Q(1,3)
        # Zero smooth and nonsmooth objective: exact map is identity.
        actual_error=e/L+delta
        self.assertEqual(actual_error,delta+e/L)
        self.assertGreater(actual_error,delta+e)

    def test_one_summable_impulse_changes_the_limit(self):
        # I is a valid forward-backward map for f=h=0. Every point is optimal.
        exact=[Q(0)]*16; inexact=[Q(0)]+[Q(2)]*15
        error=[abs(y-x) for x,y in zip(inexact,inexact[1:])]
        self.assertEqual(sum(error),2)
        self.assertNotEqual(inexact[-1],exact[-1])
        self.assertGreater(abs(inexact[1]),abs(inexact[0]))

    def test_vanishing_square_summable_errors_can_still_drift(self):
        # Positive harmonic errors: each dyadic block has sum >= 1/2.
        # This finite diagnostic supports the analytic counterexample; it is
        # not a computation of an infinite sum or a proof of divergence.
        for j in range(10):
            block=sum((Q(1,k+1) for k in range(2**j,2**(j+1))),Q(0))
            self.assertGreaterEqual(block,Q(1,2))
        self.assertLess(Q(1,1025),Q(1,100))
        # A square-norm error contract would allow this, whereas our norm-sum
        # contract excludes it. The identity orbit accumulates the errors.
        self.assertGreater(sum((Q(1,k+1) for k in range(1024)),Q(0)),5)

    def test_nonexpansiveness_without_energy_margin_is_not_enough(self):
        x=Q(1); Tx=-x
        self.assertEqual(Tx*Tx,x*x)
        for c in (Q(1,9),Q(1,2),Q(1)):
            self.assertGreater(Tx*Tx+c*(Tx-x)**2,x*x)
        orbit_reflection=[Q((-1)**n) for n in range(32)]
        self.assertTrue(all(abs(x)==1 for x in orbit_reflection))
        self.assertEqual(abs(orbit_reflection[-1]-orbit_reflection[-2]),2)

    def test_noisy_objective_does_not_inherit_zero_radius_exact_rate(self):
        # f(x)=x²/4, L=1, h=0, x0=x*=0; one prox-output error sets x1=1.
        f=lambda x:x*x/4
        self.assertEqual(f(Q(0)),0)
        self.assertGreater(f(Q(1)),Q(0))  # exact LR²/(4T) with R=0 would be 0

    def test_prox_objective_tolerance_is_not_a_norm_tolerance(self):
        # Prox subproblem Q(y)=y²/2 has delta=1/8 at y=1/2.
        y=Q(1,2); delta=y*y/2
        self.assertGreater(abs(y),delta)
        self.assertEqual(y*y,2*delta)

    def test_zero_dimension_and_zero_initial_radius(self):
        self.assertEqual(orbit(lambda x:x,(),Q(1),Q(1,2),64),[()]*65)
        # Zero initial radius does NOT imply stationarity with nonzero errors.
        xs=orbit(lambda x:x,(Q(0),),Q(1),Q(1,2),8)
        self.assertNotEqual(xs[1],xs[0])

    def test_offsets_and_nonzero_component_cancellation_preserved(self):
        ex=c5.example(2,Q(3)); star=ex.minimum()
        shifted=c5.Example(ex.curvature,ex.linear,ex.tilt,ex.lam,ex.shift,Q(101),Q(-37))
        T=lambda x:c8.step(ex.prox,ex.g,Q(3),x)
        S=lambda x:c8.step(shifted.prox,shifted.g,Q(3),x)
        self.assertNotEqual(ex.g(star),(Q(0),Q(0)))
        self.assertEqual(T(star),star)
        self.assertEqual(orbit(T,star,Q(1,3),Q(1,2),32),orbit(S,star,Q(1,3),Q(1,2),32))

    def test_original_exact_certificate_is_unchanged(self):
        for T in (1,2,4,8):
            rhs,target=cert.candidate(T)
            self.assertEqual(rhs,target)

    def test_closed_form_scalar_inexact_limit_with_resonant_error(self):
        # u(n+1)=rho*u(n)+a*rho^n, u(0)=0; u(n)=a*n*rho^(n-1).
        # An exact identity check, not an empirical limit proof.
        for rho in (Q(1,3),Q(1,2),Q(3,4)):
            a=Q(2,5); u=Q(0)
            for n in range(1,65):
                u=rho*u+a*rho**(n-1)
                self.assertEqual(u,a*n*rho**(n-1))
                self.assertLessEqual(u,a/(1-rho))


if __name__=='__main__':
    unittest.main()
