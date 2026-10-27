"""C3A exact rational regression: no solver, floats or Lean interpreter.
Scalar arithmetic is parsed from the actual Lean definitions; vector assembly
is mirrored independently and checked by narrow source-shape guards.
"""
from __future__ import annotations
import ast
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
import re
import unittest
from tests.python import test_proximal_gradient_profile as pg
from tests.python import test_composite_proximal as c1
ROOT=Path(__file__).resolve().parents[2]
SOURCE=(ROOT/'LeanPEP/Profiles/ProximalGradientCertificate.lean').read_text()
WITNESS=(ROOT/'LeanPEP/ActualFunction/ProximalGradientWitness.lean').read_text()
RATE=(ROOT/'LeanPEP/ActualFunction/ProximalGradientRate.lean').read_text()

@lru_cache(None)
def body(name):
    m=re.search(r'def '+re.escape(name)+r'[^\n]* : ℚ :=\s*(.*?)(?=\n\n)',SOURCE,re.S)
    if m is None: raise ValueError('Missing formula '+name)
    s=re.sub(r'\((n|i\.val|j\.val) : ℚ\)',r'\1',m.group(1).strip())
    s=s.replace('i.val','k').replace('j.val','k').replace('^','**')
    s=re.sub(r'pivotNumeratorQ n [ij]','pivotNumeratorQ(n,k)',s)
    return ' '.join(s.split())

@lru_cache(None)
def scalar(name,n,k=0):
    if type(n) is not int or n<0 or type(k) is not int or k<0:
        raise ValueError('Nonnegative integer indices required')
    def evaluate(s):
        if s.startswith('if '):
            cond,branches=s[3:].split(' then ',1); yes,no=branches.split(' else ',1)
            left,right=cond.split(' = ',1)
            return evaluate(yes) if evaluate(left)==evaluate(right) else evaluate(no)
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
            if isinstance(t,ast.Call) and isinstance(t.func,ast.Name) and t.func.id=='pivotNumeratorQ':
                return scalar('pivotNumeratorQ',n,k)
            raise ValueError('Unsupported arithmetic source '+ast.dump(t))
        return go(ast.parse(s,mode='eval').body)
    return evaluate(body(name))

@lru_cache(None)
def terms(T):
    if type(T) is not int or T<1: raise ValueError('T must be positive')
    n=T-1; nf=T+2; nh=T+1
    out=[(i+1,scalar('smoothStarWeightQ',n,i)) for i in range(T+1)]
    out += [((i+1)*nf+i+2,scalar('smoothChainWeightQ',n,i)) for i in range(T)]
    out += [(nf*nf+j+1,scalar('nonsmoothStarWeightQ',n,j)) for j in range(T)]
    out += [(nf*nf+(j+1)*nh+j+2,scalar('nonsmoothChainWeightQ',n,j)) for j in range(T-1)]
    out += [(nf*nf+nh*nh,scalar('boundQ',n))]
    return tuple(out)

@lru_cache(None)
def factors(T):
    n=T-1; m=2*T+3; xs=pg.positions(n); g=lambda i: pg.unit(m,i+2); gs=pg.unit(m,1)
    out=[]
    for i in range(T):
        v=c1.sub(c1.sub(xs[i],c1.scale(scalar('mixedRatioQ',n,i),xs[i+1])),
            c1.scale(scalar('mixedGradientQ',n,i),c1.sub(g(i),g(i+1))))
        out.append((scalar('mixedWeightQ',n,i),v))
    for i in range(T+1): out.append((scalar('smoothStarWeightQ',n,i)/2,c1.sub(g(i),gs)))
    for i in range(T): out.append((scalar('gradientDifferenceWeightQ',n,i),c1.sub(g(i),g(i+1))))
    return tuple(out)

@lru_cache(None)
def selected_constraint(T,idx):
    n=T-1; nf=T+2; nh=T+1; p=m=2*T+3; f,h=pg.samples(n)
    if idx<nf*nf:
        i,j=divmod(idx,nf); return pg.pair(p,'smooth',f[i],f[j])
    idx-=nf*nf
    if idx<nh*nh:
        i,j=divmod(idx,nh); return pg.pair(p,'convex',h[i],h[j])
    if idx==nh*nh:
        u=pg.unit(m,0); return pg.const(p,m,1)-pg.bilinear(p,u,u)
    raise ValueError('Invalid constraint index')

@lru_cache(None)
def candidate(T):
    p=m=2*T+3; f,h=pg.samples(T-1)
    obj=pg.val(p,m,f[-1].slot)+pg.val(p,m,h[-1].slot)-pg.val(p,m,f[0].slot)-pg.val(p,m,h[0].slot)
    target=pg.const(p,m,scalar('boundQ',T-1))-obj; rhs=c1.Expr.zero(p,m)
    for idx,w in terms(T): rhs=rhs+selected_constraint(T,idx).scaled(w)
    for w,v in factors(T): rhs=rhs+pg.bilinear(p,v,v).scaled(w)
    return rhs,target

def data(T,tilt=Q(1)):
    a=Q(1,2*T); f=lambda x:tilt*x; g=lambda x:tilt; h=lambda x:a*max(x,Q(0))-tilt*x
    xs=tuple(Q(1)-k*a for k in range(T+1))
    base=(Q(1),tilt)+tuple(tilt for _ in range(T+1))+tuple(a-tilt for _ in range(T))
    vals=(f(0),)+tuple(map(f,xs))+(h(0),)+tuple(map(h,xs[1:]))
    G=tuple(tuple(u*v for v in base) for u in base)
    return f,g,h,xs,base,vals,G

def prox_h(v,a,b):
    u=v+b
    return u-a if u>a else (u if u<0 else Q(0))

def ev(e,v,G):
    return e.const+sum((x*y for x,y in zip(e.values,v)),Q(0))+sum(
        (e.gram[i][j]*G[i][j] for i in range(len(G)) for j in range(len(G))),Q(0))

class ProximalGradientCertificateTests(unittest.TestCase):
    def test_source_factor_assembly(self):
        s=' '.join(SOURCE.split())
        self.assertIn('vector := positionVecQ n i.val - mixedRatioQ n i • positionVecQ n (i.val + 1) - mixedGradientQ n i • (gradientVecQ i.castSucc - gradientVecQ i.succ)',s)
        self.assertIn('vector := gradientVecQ i - starGradientQ n',s)
        self.assertIn('index := smoothIndex n i.castSucc.succ i.succ.succ',s)
        self.assertIn('index := nonsmoothIndex n j.castSucc.succ j.succ.succ',s)
    def test_scope(self):
        self.assertIn('↔ CertificateIdentityQ n',SOURCE); self.assertIn('(hn : n ≤ 3)',SOURCE)
        self.assertNotIn('theorem upperCertQ_check_all',SOURCE)
        self.assertIn('(hc : GramPEP.checkUpperCertQ (upperCertQ n) = true)',RATE)
    def test_counts_indices(self):
        for T in range(1,34):
            self.assertEqual(len(terms(T)),4*T+1); self.assertEqual(len(factors(T)),3*T+1)
            self.assertTrue(all(0<=i<(T+2)**2+(T+1)**2+1 for i,w in terms(T)))
    def test_weights_nonnegative(self):
        for T in range(1,65):
            self.assertTrue(all(w>=0 for _,w in terms(T)))
            for i in range(T):
                self.assertGreater(scalar('pivotNumeratorQ',T-1,i),0)
                self.assertGreater(scalar('mixedWeightQ',T-1,i),0)
                self.assertGreaterEqual(scalar('gradientDifferenceWeightQ',T-1,i),0)
    def test_zero_factor(self):
        for T in range(1,33): self.assertEqual([w for w,v in factors(T)].count(0),1)
    def test_smooth_value_flow(self):
        for T in range(1,65):
            a=[scalar('smoothStarWeightQ',T-1,i) for i in range(T+1)]
            b=[scalar('smoothChainWeightQ',T-1,i) for i in range(T)]
            self.assertEqual(sum(a),1); self.assertEqual(a[0],b[0]); self.assertEqual(a[-1]+b[-1],1)
            for i in range(1,T): self.assertEqual(a[i],b[i]-b[i-1])
    def test_nonsmooth_value_flow(self):
        for T in range(1,65):
            a=[scalar('nonsmoothStarWeightQ',T-1,i) for i in range(T)]
            b=[Q(0)]+[scalar('nonsmoothChainWeightQ',T-1,i) for i in range(T-1)]+[Q(1)]
            self.assertEqual(sum(a),1)
            for i in range(T): self.assertEqual(a[i],b[i+1]-b[i])
    def test_indices_match_full_compiler(self):
        for T in range(1,6):
            cs,_=pg.compile_profile(T-1)
            for i,_ in terms(T): self.assertEqual(selected_constraint(T,i),cs[i])
    def test_coefficient_identity_1_to_16(self):
        for T in range(1,17): self.assertEqual(*candidate(T),msg=f'T={T}')
    def test_coefficient_identity_32(self): self.assertEqual(*candidate(32))
    def test_old_one_step_dual(self):
        old=c1.Expr.zero(5,5); new=c1.Expr.zero(5,5)
        for w,v in factors(1): new=new+pg.bilinear(5,v,v).scaled(w)
        fs=[(Q(1,4),(1,0,-1,-1,-2)),(Q(1,2),(0,1,Q(-1,2),Q(-1,2),0)),(Q(1,8),(0,0,1,-1,0))]
        for w,v in fs: old=old+pg.bilinear(5,tuple(map(Q,v)),tuple(map(Q,v))).scaled(w)
        self.assertEqual(old,new)
    def test_actual_prox(self):
        for T in range(1,65):
            f,g,h,xs,*_=data(T)
            for k in range(T): self.assertEqual(prox_h(xs[k]-g(xs[k]),Q(1,2*T),Q(1)),xs[k+1])
    def test_attainment(self):
        for T in range(1,129):
            f,g,h,xs,*_=data(T)
            self.assertEqual(xs[-1],Q(1,2)); self.assertEqual(xs[0]**2,1)
            self.assertEqual(f(xs[-1])+h(xs[-1])-f(0)-h(0),scalar('boundQ',T-1))
    def test_residual_stationarity(self):
        for T in range(1,33):
            f,g,h,xs,*_=data(T); self.assertEqual(g(0)-1,0)
            for k in range(T): self.assertEqual(xs[k]-g(xs[k])-xs[k+1],Q(1,2*T)-1)
    def test_support(self):
        for T in [1,2,4,8,32]:
            f,g,h,xs,*_=data(T); a=Q(1,2*T)
            for y in [Q(-3),Q(-1,7),Q(0),Q(1,2),Q(2)]:
                self.assertLessEqual(h(0)-y,h(y))
                for z in xs[1:]: self.assertLessEqual(h(z)+(a-1)*(y-z),h(y))
    def test_all_slacks(self):
        for T in range(1,9):
            *_,v,G=data(T); cs,_=pg.compile_profile(T-1)
            self.assertTrue(all(ev(c,v,G)>=0 for c in cs))
    def test_complementarity(self):
        for T in range(1,17):
            *_,base,v,G=data(T)
            for i,w in terms(T): self.assertEqual(w*ev(selected_constraint(T,i),v,G),0)
            for w,u in factors(T): self.assertEqual(w*c1.dot(u,base)**2,0)
    def test_affine_tilt(self):
        for T in [1,2,4,8]:
            for b in [Q(-3),Q(0),Q(1),Q(5,2)]:
                f,g,h,xs,base,v,G=data(T,b)
                self.assertEqual(f(xs[-1])+h(xs[-1]),Q(1,4*T))
                for k in range(T): self.assertEqual(prox_h(xs[k]-g(xs[k]),Q(1,2*T),b),xs[k+1])
                rhs,target=candidate(T); self.assertEqual(ev(rhs,v,G),ev(target,v,G))
    def test_wrong_bound_objective(self):
        rhs,target=candidate(2)
        self.assertNotEqual(rhs,target+pg.const(7,7,Q(1,9)-Q(1,8)))
        self.assertNotEqual(rhs,target+pg.val(7,7,6)-pg.val(7,7,4))
    def test_missing_negative_factor(self):
        rhs,target=candidate(3); w,v=factors(3)[0]; e=pg.bilinear(9,v,v).scaled(w)
        self.assertNotEqual(rhs-e,target); self.assertNotEqual(rhs-e.scaled(2),target)
    def test_reversed_pair(self):
        T=2; rhs,target=candidate(T); idx,w=terms(T)[0]; nf=T+2; wrong=(idx%nf)*nf+idx//nf
        self.assertNotEqual(rhs-selected_constraint(T,idx).scaled(w)+selected_constraint(T,wrong).scaled(w),target)
    def test_terminal_gradient_mutation(self):
        w,v=factors(2)[0]; bad=c1.add(v,pg.unit(7,4)); rhs,target=candidate(2)
        self.assertNotEqual(rhs-pg.bilinear(7,v,v).scaled(w)+pg.bilinear(7,bad,bad).scaled(w),target)
    def test_prefix_only(self):
        a=Q(1,6); self.assertNotEqual(prox_h(Q(-1),a,Q(1)),-a)
        self.assertIn('IsProxRun (n + 1)',WITNESS)
    def test_explicit_only(self):
        self.assertIn('interpTerms := []',SOURCE)
        self.assertIn('dualMatrix := factorGramQ (dualFactorsQ n)',SOURCE)
        self.assertIn('hc rfl rfl hf hh hs hrun hradius',RATE)
        self.assertNotIn('CoreFeasible',RATE)

if __name__=='__main__': unittest.main(verbosity=2)
