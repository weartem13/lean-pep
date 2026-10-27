"""Exact C3B proof-decomposition regression; NOT a Lean interpreter.

Old certificate formulas are parsed by C3A's rejecting arithmetic parser;
new node/potential formulas are read from the delivered Lean source. Tests
use arbitrary signed data, rather than testing only the attaining witness.
"""
from __future__ import annotations
import ast
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
import random
import re
import unittest
from tests.python import test_proximal_gradient_certificate as cert
from tests.python import test_proximal_gradient_profile as pg
from tests.python import test_composite_proximal as alg

ROOT=Path(__file__).resolve().parents[2]
FLOW=(ROOT/'LeanPEP/Profiles/ProximalGradientCertificateFlow.lean').read_text()
LOCAL=(ROOT/'LeanPEP/Profiles/ProximalGradientCertificateLocal.lean').read_text()
IDENTITY=(ROOT/'LeanPEP/Profiles/ProximalGradientCertificateIdentity.lean').read_text()
RATE=(ROOT/'LeanPEP/ActualFunction/ProximalGradientRateAll.lean').read_text()

@lru_cache(None)
def formula(name: str) -> ast.AST:
    text=FLOW if name=='nodeFluxQ' else LOCAL
    match=re.search(r'def '+re.escape(name)+r' \(n k : ℕ\) : ℚ :=\s*(.*?)(?=\n\n)',text,re.S)
    if match is None: raise ValueError('Missing source formula: '+name)
    body=re.sub(r'\(([nk]) : ℚ\)',r'\1',match.group(1)).replace('^','**')
    return ast.parse(' '.join(body.split()),mode='eval').body

@lru_cache(None)
def evaluate(name: str,n: int,k: int) -> Q:
    if name not in ('nodeFluxQ','potentialQ'): raise ValueError('Unsupported formula')
    if type(n) is not int or type(k) is not int or not(n>=0 and 0<=k<=n+1):
        raise ValueError('Outside proved node interval')
    def go(t):
        if isinstance(t,ast.Constant) and type(t.value) is int: return Q(t.value)
        if isinstance(t,ast.Name) and t.id in ('n','k'): return Q(n if t.id=='n' else k)
        if isinstance(t,ast.BinOp):
            a,b=go(t.left),go(t.right)
            if isinstance(t.op,ast.Add): return a+b
            if isinstance(t.op,ast.Sub): return a-b
            if isinstance(t.op,ast.Mult): return a*b
            if isinstance(t.op,ast.Div): return a/b
            if isinstance(t.op,ast.Pow) and b.denominator==1: return a**int(b)
        raise ValueError('Unsupported arithmetic syntax')
    return go(formula(name))

def q(n,k): return evaluate('nodeFluxQ',n,k)
def rho(n,k): return evaluate('potentialQ',n,k)
def w(name,n,i): return cert.scalar(name,n,i)

def local_terms(n,i,X,Y,G,H):
    B=lambda a,b:pg.bilinear(3,a,b)
    norm=lambda a:B(a,a)
    d=alg.sub(G,H); s=alg.sub(alg.sub(X,Y),G)
    m=alg.sub(alg.sub(X,alg.scale(w('mixedRatioQ',n,i),Y)),alg.scale(w('mixedGradientQ',n,i),d))
    lhs=norm(m).scaled(w('mixedWeightQ',n,i))+norm(d).scaled(w('gradientDifferenceWeightQ',n,i))
    lhs=lhs+(B(d,X)-norm(d).scaled(Q(1,2))).scaled(w('smoothChainWeightQ',n,i))
    lhs=lhs+B(s,Y).scaled(q(n,i+1))-B(s,X).scaled(q(n,i))
    rhs=norm(X).scaled(rho(n,i))-norm(Y).scaled(rho(n,i+1))
    rhs=rhs+B(G,X).scaled(q(n,i))-B(H,Y).scaled(q(n,i+1))
    return lhs,rhs

class TelescopingTests(unittest.TestCase):
    def test_01_source_flux(self):
        for T in range(1,65):
            for k in range(T+1): self.assertEqual(q(T-1,k),Q(k,2*T-k))
    def test_02_source_potential(self):
        for T in range(1,65):
            for k in range(T+1): self.assertEqual(rho(T-1,k),Q(T-k,(2*T-k)**2))
    def test_03_denominators(self):
        for T in range(1,129):
            for k in range(T+1): self.assertGreater(2*T-k,0)
            for k in range(T):
                self.assertGreater(2*T-k-1,0)
                self.assertGreater(w('pivotNumeratorQ',T-1,k),0)
    def test_04_endpoints(self):
        for T in range(1,257):
            self.assertEqual(q(T-1,0),0); self.assertEqual(q(T-1,T),1)
            self.assertEqual(rho(T-1,0),cert.scalar('boundQ',T-1)); self.assertEqual(rho(T-1,T),0)
    def test_05_smooth_flux(self):
        for T in range(1,65):
            flux=[Q(k,2*T-k+1) for k in range(T+1)]+[Q(1)]
            for k in range(T+1): self.assertEqual(w('smoothStarWeightQ',T-1,k),flux[k+1]-flux[k])
            for k in range(T): self.assertEqual(w('smoothChainWeightQ',T-1,k),flux[k+1])
    def test_06_nonsmooth_flux(self):
        for T in range(1,65):
            for k in range(T): self.assertEqual(w('nonsmoothStarWeightQ',T-1,k),q(T-1,k+1)-q(T-1,k))
            for k in range(T-1): self.assertEqual(w('nonsmoothChainWeightQ',T-1,k),q(T-1,k+1))
    def test_07_smooth_signed_value_flow(self):
        for T in range(1,65):
            z=[Q((-1)**k*(3*k*k+7),k+2) for k in range(T+1)]; a=Q(-4,3)
            lhs=sum(w('smoothStarWeightQ',T-1,k)*(a-z[k]) for k in range(T+1))
            lhs+=sum(w('smoothChainWeightQ',T-1,k)*(z[k]-z[k+1]) for k in range(T))
            self.assertEqual(lhs,a-z[-1])
    def test_08_nonsmooth_signed_value_flow(self):
        for T in range(1,65):
            z=[Q((-1)**k*(k*k+1),2*k+1) for k in range(T)]; a=Q(5,7)
            lhs=sum(w('nonsmoothStarWeightQ',T-1,k)*(a-z[k]) for k in range(T))
            lhs+=sum(w('nonsmoothChainWeightQ',T-1,k)*(z[k]-z[k+1]) for k in range(T-1))
            self.assertEqual(lhs,a-z[-1])
    def test_09_rectangular_lookup(self):
        for r in range(10):
            for c in range(10):
                rows=[(i,j) for i in range(r) for j in range(c)]; self.assertEqual(len(rows),r*c)
                for i in range(r):
                    for j in range(c): self.assertEqual(rows[i*c+j],(i,j))
    def test_10_compiler_constraint_lookups(self):
        for T in range(1,7):
            cs,_=pg.compile_profile(T-1)
            for idx,c in enumerate(cs): self.assertEqual(c,cert.selected_constraint(T,idx))
    def test_11_six_local_weight_identities(self):
        for T in range(1,65):
            n=T-1
            for i in range(T):
                A,r,c,e,b=[w(name,n,i) for name in ('mixedWeightQ','mixedRatioQ','mixedGradientQ','gradientDifferenceWeightQ','smoothChainWeightQ')]
                self.assertEqual(A-q(n,i),rho(n,i)); self.assertEqual(A*r*r-q(n,i+1),-rho(n,i+1))
                self.assertEqual(2*A*r,q(n,i)+q(n,i+1)); self.assertEqual(2*A*c,b)
                self.assertEqual(2*A*r*c,q(n,i+1)); self.assertEqual(A*c*c+e,b/2)
    def test_12_arbitrary_scalar_data(self):
        rng=random.Random(130301)
        for T in range(1,33):
            for i in range(T):
                args=[(Q(rng.randrange(-20,21),rng.randrange(1,10)),) for _ in range(4)]
                self.assertEqual(*local_terms(T-1,i,*args))
    def test_13_full_offdiagonal_coefficients(self):
        rng=random.Random(130302)
        for m in (2,3,5):
            for T in range(1,13):
                for i in range(T):
                    args=[tuple(Q(rng.randrange(-9,10),rng.randrange(1,8)) for _ in range(m)) for _ in range(4)]
                    a,b=local_terms(T-1,i,*args); self.assertEqual(a,b)
                    self.assertEqual(a.const,0); self.assertTrue(all(v==0 for v in a.values))
    def test_14_polarization(self):
        rng=random.Random(130303)
        for _ in range(100):
            u=[Q(rng.randrange(-9,10),rng.randrange(1,8)) for _ in range(5)]
            v=[Q(rng.randrange(-9,10),rng.randrange(1,8)) for _ in range(5)]
            for i in range(5):
                for j in range(5): self.assertEqual(((u[i]+u[j])*(v[i]+v[j])-u[i]*v[i]-u[j]*v[j])/2,(u[i]*v[j]+u[j]*v[i])/2)
    def test_15_full_edge_telescope_arbitrary_vectors(self):
        rng=random.Random(130304)
        for T in (*range(1,17),32,64):
            xs=[tuple(Q(rng.randrange(-9,10),rng.randrange(1,8)) for _ in range(3)) for _ in range(T+1)]
            gs=[tuple(Q(rng.randrange(-9,10),rng.randrange(1,8)) for _ in range(3)) for _ in range(T+1)]
            total=alg.Expr.zero(3,3)
            for i in range(T): total=total+local_terms(T-1,i,xs[i],xs[i+1],gs[i],gs[i+1])[0]
            target=pg.bilinear(3,xs[0],xs[0]).scaled(Q(1,4*T))-pg.bilinear(3,gs[-1],xs[-1])
            self.assertEqual(total,target)
    def test_16_additional_full_original_certificate(self):
        for T in (17,24): self.assertEqual(*cert.candidate(T))
    def test_17_one_step_boundary(self):
        self.assertEqual(w('smoothStarWeightQ',0,0),Q(1,2)); self.assertEqual(w('smoothStarWeightQ',0,1),Q(1,2))
        self.assertEqual(w('nonsmoothStarWeightQ',0,0),1); self.assertEqual(w('gradientDifferenceWeightQ',0,0),0)
        self.assertEqual(*local_terms(0,0,(Q(7),),(Q(-3),),(Q(2),),(Q(9),)))
    def test_18_wrong_initial_potential(self):
        args=(Q(3),Q(-2)),(Q(1),Q(4)),(Q(0),Q(2)),(Q(-1),Q(3))
        lhs,rhs=local_terms(6,0,*args)
        self.assertNotEqual(lhs,rhs+pg.bilinear(3,args[0],args[0]).scaled(Q(1,100)))
    def test_19_wrong_terminal_flux(self):
        X,Y,G,H=(Q(3),),(Q(4),),(Q(1),),(Q(2),)
        lhs,rhs=local_terms(5,5,X,Y,G,H); self.assertNotEqual(lhs,rhs+pg.bilinear(3,H,Y))
    def test_20_asymmetric_outer(self):
        u,v=(Q(1),Q(3)),(Q(2),Q(5)); expected=pg.bilinear(3,u,v).gram; wrong=alg.outer(u,v)
        self.assertEqual(expected[0][0],wrong[0][0]); self.assertEqual(expected[1][1],wrong[1][1])
        self.assertNotEqual(expected,wrong)
    def test_21_residual_sign_mutation(self):
        n,i=4,2; X,Y,G,H=(Q(7),Q(3)),(Q(2),Q(-4)),(Q(1),Q(6)),(Q(5),Q(1))
        lhs,rhs=local_terms(n,i,X,Y,G,H); s=alg.sub(alg.sub(X,Y),G)
        support=pg.bilinear(3,s,Y).scaled(q(n,i+1))-pg.bilinear(3,s,X).scaled(q(n,i))
        self.assertNotEqual(lhs-support.scaled(2),rhs)
    def test_22_unrestricted_source_interfaces(self):
        for name in ('upper_all','upper_analytic_all','upper_analytic_steps'):
            m=re.search(r'theorem '+name+r'\b(.*?)(?=:=)',RATE,re.S); self.assertIsNotNone(m)
            self.assertNotIn('checkUpperCertQ',m.group(1)); self.assertNotIn('CertificateIdentityQ',m.group(1))
        self.assertIn('certificateIdentityQ_all (n : ℕ) : CertificateIdentityQ n',IDENTITY)
        self.assertIn('(upperCertQ_check_iff_identity n).mpr (certificateIdentityQ_all n)',IDENTITY)
        self.assertNotIn('decide +kernel',IDENTITY); self.assertNotIn('native_decide',IDENTITY)

if __name__=='__main__': unittest.main()
