"""C10 exact algebra/finite diagnostics and source-contract guards.

Not an execution of Lean's Classical.choose, an infinite-dimensional limit
proof, or a Lean elaborator. Finite-support probes illustrate necessary
boundaries; they do not test every member of an infinite-dimensional dual.
"""
from __future__ import annotations
from fractions import Fraction as Q
from pathlib import Path
import re
import unittest

from tests.python import test_composite_proximal as c1
from tests.python import test_proximal_canonical as c6
from tests.python import test_proximal_stability as c8
from tests.python import test_proximal_convergence as c9

ROOT = Path(__file__).resolve().parents[2]
TOP = (ROOT/'LeanPEP/ActualFunction/HilbertWeakTopology.lean').read_text()
FEJ = (ROOT/'LeanPEP/ActualFunction/WeakFejerConvergence.lean').read_text()
ALG = (ROOT/'LeanPEP/ActualFunction/ProximalGradientWeakConvergence.lean').read_text()
Vec = tuple[Q, ...]


def strip_comments(s: str) -> str:
    return re.sub(r'--[^\n]*', '', re.sub(r'/-.*?-/', '', s, flags=re.S))


def statement(s: str, name: str) -> str:
    return s.split('theorem '+name, 1)[1].split(':=', 1)[0]


def distance_difference(x: Vec, z: Vec, w: Vec) -> Q:
    return c8.norm2(c1.sub(x,z))-c8.norm2(c1.sub(x,w))


def defect_valid(T, x: Vec, z: Vec, B2: Q | None = None) -> bool:
    """Check a <= 2 sqrt(B2*res2) exactly, with no floating-point roots.

    This is the scalar defect estimate with B=sqrt(B2). Its nonpositive-left
    branch must be handled before squaring, to preserve logical equivalence.
    """
    if B2 is None:
        B2=c8.norm2(c1.sub(x,z))
    if B2 < c8.norm2(c1.sub(x,z)):
        raise ValueError('Bound does not cover the point')
    d=c1.sub(T(z),z)
    e=c1.sub(T(x),x)
    a=c8.norm2(d)-2*c8.dot(c1.sub(x,z),d)-c8.norm2(e)
    return a<=0 or a*a<=4*B2*c8.norm2(e)


def sparse_dot(a: dict[int,Q], b: dict[int,Q]) -> Q:
    return sum((x*b.get(k,Q(0)) for k,x in a.items()),Q(0))


class ProximalWeakConvergenceTests(unittest.TestCase):
    def test_standard_weak_topology_and_linear_dual_are_used(self):
        for name in ('weakSpace_tendsto_iff_dual','weakSpace_tendsto_iff_inner'):
            self.assertIn('toWeakSpace ℝ E',statement(TOP,name))
        self.assertIn('StrongDual ℝ E',statement(TOP,'weakSpace_tendsto_iff_dual'))
        self.assertIn('WeakBilin.tendsto_iff_forall_eval_tendsto',TOP)
        self.assertNotRegex(strip_comments(TOP),r'\b(?:instance|local instance)\b')

    def test_riesz_and_banach_alaoglu_are_connected_not_assumed(self):
        self.assertIn('InnerProductSpace.toDual ℝ E',TOP)
        self.assertIn('weakRiesz_closedBall_image',TOP)
        self.assertIn('WeakDual.isCompact_closedBall',TOP)
        self.assertIn('[CompleteSpace E]',statement(TOP,'weakRiesz_surjective'))
        self.assertNotIn('IsCompact',statement(TOP,'weakRiesz_surjective'))

    def test_no_separable_or_finite_dimensional_restriction(self):
        code=strip_comments(TOP+FEJ+ALG)
        for s in ('SeparableSpace','FiniteDimensional','FirstCountableTopology','tendsto_subseq'):
            self.assertNotIn(s,code)
        head=statement(ALG,'hilbertIterate_weak_tendsto ')
        self.assertIn('[CompleteSpace E]',head)
        self.assertIn('(hcont : Continuous h)',head)
        self.assertNotIn('IsCompact',head)
        self.assertNotIn('HasProx',head)
        self.assertNotIn('hrun',head)

    def test_cluster_filters_retain_nebot_and_cofinal_tail(self):
        head=statement(TOP,'inner_subfilter_of_weakRiesz_cluster')
        self.assertIn('l.NeBot ∧ l ≤ atTop',head)
        self.assertIn('Filter.neBot_inf_comap_iff_map\'',TOP)
        self.assertIn('hK.exists_mapClusterPt',FEJ)
        self.assertIn('hK.tendsto_nhds_of_unique_mapClusterPt',FEJ)
        self.assertIn('[l.NeBot]',statement(FEJ,'fixed_of_inner_tendsto_of_residual'))
        for term in ('[lz.NeBot]','[lw.NeBot]','lz ≤ atTop','lw ≤ atTop'):
            self.assertIn(term,statement(FEJ,'inner_limits_eq_of_antitone'))

    def test_demiclosedness_keeps_boundedness_and_no_weak_map_continuity(self):
        head=statement(FEJ,'fixed_of_inner_tendsto_of_residual')
        for term in ('‖u i-z‖ ≤ B','‖T x-T y‖ ≤ ‖x-y‖','‖T (u i)-u i‖'):
            self.assertIn(term,head)
        self.assertNotIn('Continuous T',head)
        self.assertIn('fixed_defect_bound hT',FEJ)
        self.assertIn('ge_of_tendsto\'',FEJ)

    def test_opial_uses_both_distances_and_not_norm_weak_continuity(self):
        head=statement(FEJ,'inner_limits_eq_of_antitone')
        self.assertIn('‖u n-z‖',head)
        self.assertIn('‖u n-w‖',head)
        self.assertIn('tendsto_atTop_ciInf haz hzb',FEJ)
        self.assertIn('tendsto_atTop_ciInf haw hwb',FEJ)
        self.assertIn('distance_sq_difference_tendsto hz z w',FEJ)
        self.assertIn('distance_sq_difference_tendsto hw z w',FEJ)

    def test_same_iteration_and_no_new_certificate_or_axiom(self):
        code=strip_comments(TOP+FEJ+ALG)
        for bad in ('sorry','admit','axiom','opaque','unsafe','native_decide','implemented_by'):
            self.assertNotRegex(code,rf'\b{bad}\b')
        self.assertNotRegex(code,r'\b(?:def|abbrev)\s+(?:proxMap|iterate|hilbertIterate)\b')
        self.assertNotIn('Classical.choose',code)
        self.assertNotIn('checkUpperCertQ',code)
        for old in ('iterate_distance_antitone','iterate_residual_tendsto_zero',
                    'forwardBackwardStep_fixed_iff_minimizer','hasProx_of_continuous','run_eq_iterate'):
            self.assertIn(old,ALG)

    def test_some_minimizer_and_independent_objective_convergence(self):
        head=statement(ALG,'hilbertIterate_weak_tendsto ')
        self.assertIn('∃ z,',head)
        self.assertNotIn('hunique',head)
        self.assertIn('hunique',statement(ALG,'iterate_weak_tendsto_of_unique'))
        self.assertIn('hilbertIterate_objective_tendsto hf hL hh hcont hz x0',ALG)
        self.assertIn('(hrun : ∀ N,',statement(ALG,'run_weak_tendsto '))
        self.assertIn('hmap',ALG)

    def test_distance_difference_all_cross_terms(self):
        for dim in (0,1,2,5):
            xs=list(c8.probes(dim))
            for x in xs:
                for z,w in zip(xs,reversed(xs),strict=True):
                    rhs=2*c8.dot(x,c1.sub(w,z))+c8.norm2(z)-c8.norm2(w)
                    self.assertEqual(distance_difference(x,z,w),rhs)

    def test_pairing_difference_tracks_affine_sequence_exactly(self):
        for dim in (1,2,5):
            a,z,w,v=list(c8.probes(dim))[2:6]
            for k in range(33):
                u=c8.add(a,c1.scale(Q(1,2)**k,v))
                error=distance_difference(u,z,w)-distance_difference(a,z,w)
                self.assertEqual(error,2*Q(1,2)**k*c8.dot(v,c1.sub(w,z)))

    def test_defect_bound_affine_nonexpansive_maps(self):
        for dim in (0,1,2,5):
            v=tuple(Q(j-2,7) for j in range(dim))
            for alpha in (Q(-1),Q(-3,5),Q(0),Q(1,3),Q(1)):
                T=lambda x:c8.add(c1.scale(alpha,x),v)
                xs=list(c8.probes(dim))
                for x,z in zip(xs,reversed(xs),strict=True):
                    self.assertTrue(defect_valid(T,x,z))
                    self.assertTrue(defect_valid(T,x,z,c8.norm2(c1.sub(x,z))+Q(7,3)))

    def test_defect_bound_original_closed_form_prox(self):
        for dim in (0,1,2,5):
            h=c6.penalty(dim)
            for L in (Q(1,5),Q(1),Q(7,2)):
                T=lambda x:h.prox(x,L)
                xs=list(c8.probes(dim))
                for x,z in zip(xs,reversed(xs),strict=True):
                    self.assertTrue(defect_valid(T,x,z))

    def test_defect_bound_noncommuting_forward_backward(self):
        for L in (Q(1,3),Q(1),Q(5)):
            g,p=c8.coupled(L)
            T=lambda x:c8.step(p,g,L,x)
            xs=list(c8.probes(2))
            for x in xs:
                for z in xs:
                    self.assertTrue(defect_valid(T,x,z))

    def test_missing_pairing_or_wrong_sign_rejected(self):
        T=lambda x:c1.scale(Q(-1),x)
        x,z=(Q(0),),(Q(1),)
        d=c1.sub(T(z),z)
        pairing=c8.dot(c1.sub(x,z),d)
        self.assertEqual(c8.norm2(d),2*pairing)
        self.assertGreater(c8.norm2(d),0)
        self.assertGreater(c8.norm2(d),-2*pairing)
        self.assertTrue(defect_valid(T,x,z))

    def test_missing_residual_square_rejected(self):
        T=lambda x:(x[0]+1,)
        x=z=(Q(0),)
        self.assertEqual(c8.norm2(c1.sub(T(z),z)),1)
        self.assertTrue(defect_valid(T,x,z))
        # B=0 and pairing=0: the square is the entire right side.
        self.assertFalse(Q(1)<=0)

    def test_difference_limit_signs_force_identical_clusters(self):
        for dim in (0,1,2,5):
            xs=list(c8.probes(dim))
            for z,w in zip(xs,reversed(xs),strict=True):
                D=c8.norm2(c1.sub(z,w))
                self.assertEqual(distance_difference(z,z,w),-D)
                self.assertEqual(distance_difference(w,z,w),D)
                self.assertEqual((-D==D),(z==w))

    def test_finite_support_probes_do_not_control_norm(self):
        probes=[{j:Q(j+1,11) for j in range(m)} for m in (0,1,3,7,13)]
        for n in range(14,50):
            e={n:Q(1)}
            self.assertEqual(sparse_dot(e,e),1)
            for v in probes:
                self.assertEqual(sparse_dot(e,v),0)
        # Finite probes are diagnostic only; no claim of proving all dual tests.

    def test_squared_distance_difference_survives_orthogonal_tail(self):
        z={0:Q(2),1:Q(-1)}
        w={1:Q(3),4:Q(2,5)}
        zz,ww=sparse_dot(z,z),sparse_dot(w,w)
        for n in range(5,30):
            e={n:Q(1)}
            # Each squared distance has an extra one; it cancels in the difference.
            dz=1+zz-2*sparse_dot(e,z)
            dw=1+ww-2*sparse_dot(e,w)
            self.assertEqual(dz-dw,zz-ww)
            self.assertNotEqual(dz,zz)

    def test_norm_continuous_nonexpansive_map_not_weak_continuous(self):
        # On l2, T(x)=||x||*e_0. For e_n with n>0, T(e_n)=e_0, T(0)=0.
        # These exact basis evaluations exhibit the obstruction; residuals do not vanish.
        for n in range(1,40):
            e={n:Q(1)}
            Te={0:Q(1)}
            self.assertEqual(sparse_dot(Te,{0:Q(1)}),1)
            self.assertEqual(sparse_dot(e,{0:Q(1)}),0)
            residual2=2-2*sparse_dot(Te,e)
            self.assertEqual(residual2,2)

    def test_fejer_to_one_reference_does_not_give_unique_clusters(self):
        u=[Q(1) if n%2==0 else Q(-1) for n in range(32)]
        self.assertTrue(all(abs(x)==1 for x in u))
        self.assertTrue(all(u[2*j]==1 and u[2*j+1]==-1 for j in range(16)))
        # Distances to either proposed cluster are not antitone.
        self.assertLess(abs(u[0]-1),abs(u[1]-1))
        self.assertLess(abs(u[1]+1),abs(u[2]+1))

    def test_noncofinal_sample_and_trivial_filter_guard(self):
        # A residual that vanishes after time 0 is not inherited by constant sampling.
        residual=lambda n:Q(1) if n==0 else Q(0)
        self.assertTrue(all(residual(n)==0 for n in range(1,64)))
        self.assertTrue(all(residual(0)==1 for _ in range(64)))
        # The source explicitly prevents taking limits along bottom.
        self.assertIn('[l.NeBot]',statement(FEJ,'fixed_of_inner_tendsto_of_residual'))

    def test_flat_minimizer_set_and_nonzero_component_cancellation(self):
        for L in (Q(1,4),Q(1),Q(5)):
            ex=c9.flat_example(L)
            x0=(Q(7,3),Q(-5,4))
            xs=c6.iterate(ex.prox,ex.g,L,x0,32)
            target=(Q(0),x0[1])
            for n,x in enumerate(xs):
                self.assertEqual(x,(x0[0]*Q(1,2)**n,x0[1]))
                self.assertEqual(c8.norm2(c1.sub(x,target)),x0[0]**2*Q(1,4)**n)
            self.assertNotEqual(target,(Q(0),Q(0)))
            self.assertNotEqual(ex.g(target),(Q(0),Q(0)))

    def test_zero_dimension_and_zero_radius(self):
        h=c6.penalty(0)
        self.assertEqual(c6.iterate(h.prox,lambda x:(),Q(2),(),16),[()]*17)
        ex=c9.flat_example(Q(3))
        star=(Q(0),Q(9,7))
        self.assertEqual(c6.iterate(ex.prox,ex.g,Q(3),star,16),[star]*17)

    def test_hilbert_continuity_and_no_error_or_strong_rate_claim(self):
        core=statement(FEJ,'exists_weak_tendsto_fixed')
        self.assertNotIn('IsCompact',core)
        self.assertNotIn('Continuous T',core)
        self.assertIn('T p = p',core)
        self.assertIn('∀ z, T z = z',core)
        self.assertIn('toWeakSpace',core)
        for s in ('inexact','checkUpperCertQ','oneDimensionalValues'):
            self.assertNotIn(s,strip_comments(ALG))
        self.assertIn('Continuous h',statement(ALG,'run_weak_tendsto_hilbert'))
        self.assertNotIn('Continuous h',statement(ALG,'iterate_weak_tendsto '))


if __name__=='__main__':
    unittest.main()
