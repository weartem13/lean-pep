"""Independent exact C2 regression: positive-horizon PG compilation and runs.

The Python mirror is checked against a narrow source-shape contract, not a
Lean evaluator. It tests ordering, signs, indexing and actual data semantics;
only a Lean build can check the new proof scripts. No solver or float is used.
"""
from __future__ import annotations

import ast
from dataclasses import replace
from fractions import Fraction as Q
from pathlib import Path
import re
import unittest

from tests.python import test_composite_proximal as c1

ROOT = Path(__file__).resolve().parents[2]
PROFILE = (ROOT / 'LeanPEP/Profiles/ProximalGradient.lean').read_text(encoding='utf-8')
ACTUAL = (ROOT / 'LeanPEP/ActualFunction/ProximalGradient.lean').read_text(encoding='utf-8')


def count(name: str, n: int) -> int:
    expr = re.search(r'abbrev ' + name + r' \(n : ℕ\) : ℕ := ([^\n]+)', PROFILE).group(1)
    def go(t):
        if isinstance(t, ast.Constant) and type(t.value) is int:
            return t.value
        if isinstance(t, ast.Name) and t.id == 'n':
            return n
        if isinstance(t, ast.BinOp) and isinstance(t.op, ast.Add):
            return go(t.left) + go(t.right)
        raise ValueError('Unsupported dimension source expression')
    return go(ast.parse(expr, mode='eval').body)


def unit(m, i):
    if not 0 <= i < m:
        raise ValueError('Basis index outside declared horizon')
    return tuple(Q(j == i) for j in range(m))


def positions(n: int, until: int | None = None):
    if n < 0:
        raise ValueError('Profile parameter must be nonnegative')
    T, m = n + 1, count('basisCount', n)
    stop = T if until is None else until
    out = [unit(m, 0)]
    for k in range(stop):
        out.append(c1.sub(c1.sub(out[-1], unit(m, k + 2)), unit(m, n + 4 + k))
                   if k < T else out[-1])
    return out


def samples(n):
    T, m = n + 1, count('basisCount', n)
    xs = positions(n)
    zero = (Q(0),) * m
    smooth = [c1.Sample(0, zero, unit(m, 1))] + [
        c1.Sample(k + 1, xs[k], unit(m, k + 2)) for k in range(T + 1)]
    nonsmooth = [c1.Sample(n + 3, zero, c1.scale(Q(-1), unit(m, 1)))] + [
        c1.Sample(n + 4 + k, xs[k + 1], unit(m, n + 4 + k)) for k in range(T)]
    return smooth, nonsmooth


def val(p, m, i):
    return replace(c1.Expr.zero(p, m), values=tuple(Q(j == i) for j in range(p)))


def const(p, m, c):
    return replace(c1.Expr.zero(p, m), const=Q(c))


def bilinear(p, u, v):
    m = len(u)
    return replace(c1.Expr.zero(p, m), gram=tuple(tuple(
        (u[i] * v[j] + u[j] * v[i]) / 2 for j in range(m)) for i in range(m)))


def pair(p, kind, a, b):
    m = len(a.position)
    e = val(p, m, a.slot) - val(p, m, b.slot) - bilinear(p, b.oracle, c1.sub(a.position, b.position))
    if kind == 'smooth':
        dg = c1.sub(a.oracle, b.oracle)
        e = e - bilinear(p, dg, dg).scaled(Q(1, 2))
    elif kind != 'convex':
        raise ValueError('Unsupported function class')
    return e


def compile_profile(n):
    p, m = count('valueCount', n), count('basisCount', n)
    smooth, nonsmooth = samples(n)
    constraints = [pair(p, 'smooth', a, b) for a in smooth for b in smooth]
    constraints += [pair(p, 'convex', a, b) for a in nonsmooth for b in nonsmooth]
    u = unit(m, 0)
    constraints += [const(p, m, 1) - bilinear(p, u, u)]
    objective = val(p, m, n + 2) + val(p, m, p - 1) - val(p, m, 0) - val(p, m, n + 3)
    return constraints, objective


def realize(coeffs, base):
    return tuple(sum((a * v[j] for a, v in zip(coeffs, base, strict=True)), Q(0))
                 for j in range(len(base[0])))


def soft(z, lam):
    return max(z - lam, Q(0)) if z >= 0 else min(z + lam, Q(0))


def actual_example(n, dim, lam=Q(1, 7), translate=True, zero_radius=False):
    T = n + 1
    center = tuple(Q(j - 1, 5) if translate else Q(0) for j in range(dim))
    shift = tuple(Q(j + 1, 7) for j in range(dim))
    q = tuple(Q(j + 1, dim + 1) for j in range(dim))
    initial = center if zero_radius else c1.add(center, tuple(Q(1, dim * (j + 2)) for j in range(dim)))
    def f(z):
        return sum((qi * (zi-ci)**2/2 + ai*zi
                    for qi, zi, ci, ai in zip(q, z, center, shift, strict=True)), Q(0))
    def g(z):
        return tuple(qi*(zi-ci)+ai for qi, zi, ci, ai in zip(q, z, center, shift, strict=True))
    def h(z):
        return sum((lam*abs(zi-ci)-ai*zi for zi, ci, ai in zip(z, center, shift, strict=True)), Q(0))
    xs, residuals = [initial], []
    for _ in range(T):
        forward = c1.sub(xs[-1], g(xs[-1]))
        nxt = tuple(ci + soft(vi+ai-ci, lam) for ci, vi, ai in zip(center, forward, shift, strict=True))
        residuals.append(c1.sub(forward, nxt))
        xs.append(nxt)
    base = [c1.sub(initial, center), g(center)] + [g(z) for z in xs] + residuals
    values = [f(center)] + [f(z) for z in xs] + [h(center)] + [h(z) for z in xs[1:]]
    gram = tuple(tuple(c1.dot(u, v) for v in base) for u in base)
    return f, g, h, center, xs, residuals, base, tuple(values), gram


def finite_actual_pair(kind, fx, fy, x, y, s, t):
    out = fx - fy - c1.dot(t, c1.sub(x, y))
    if kind == 'smooth':
        out -= c1.dot(c1.sub(s, t), c1.sub(s, t)) / 2
    return out


class ProximalGradientProfileTests(unittest.TestCase):
    def test_source_recurrence_contract(self):
        body = PROFILE.split('def positionVecQ', 1)[1].split('@[simp]', 1)[0]
        self.assertIn('if hk : k < n + 1 then', body)
        self.assertRegex(body, r'positionVecQ n k - gradientVecQ.*\n\s*residualVecQ')
        self.assertIn('else positionVecQ n k', body)
        self.assertIn('Fin.castAdd (n + 1) i.succ.succ', PROFILE)
        self.assertIn('Fin.natAdd (n + 4) j', PROFILE)

    def test_source_component_and_bridge_contract(self):
        self.assertIn('Composite.compileModelQ (profileQ n)', PROFILE)
        self.assertIn('oracle := -starGradientQ n', PROFILE)
        self.assertIn('position := positionVecQ n (j.val + 1)', PROFILE)
        self.assertIn('x k - g (x k) - x (k + 1)', ACTUAL)
        self.assertIn('(hempty : c.interpTerms = [])', ACTUAL)
        self.assertIn('(hobjective : c.objective = objectiveQ n)', ACTUAL)

    def test_dimensions_from_source(self):
        for n in range(33):
            self.assertEqual(count('valueCount', n), 2*n+5)
            self.assertEqual(count('basisCount', n), 2*n+5)

    def test_value_block_disjoint_cover(self):
        for n in range(33):
            fs = set(range(n+3)); hs = set(range(n+3, count('valueCount', n)))
            self.assertFalse(fs & hs)
            self.assertEqual(fs | hs, set(range(2*n+5)))
            a, b = samples(n)
            self.assertEqual([s.slot for s in a+b], list(range(2*n+5)))

    def test_no_initial_nonsmooth_sample(self):
        for n in range(13):
            _, hs = samples(n)
            self.assertEqual(len(hs), n+2)
            self.assertNotIn(positions(n)[0], [s.position for s in hs])

    def test_position_closed_coefficients(self):
        for n in range(33):
            for k, v in enumerate(positions(n)):
                self.assertEqual(v[0], 1)
                self.assertEqual(v[1], 0)
                self.assertEqual(v[2:n+4], tuple(Q(-int(j < k)) for j in range(n+2)))
                self.assertEqual(v[n+4:], tuple(Q(-int(j < k)) for j in range(n+1)))

    def test_terminal_gradient_unused(self):
        for n in range(33):
            self.assertTrue(all(v[n+3] == 0 for v in positions(n)))

    def test_freeze_never_wraps(self):
        for n in range(13):
            vs = positions(n, n+5)
            self.assertTrue(all(v == vs[n+1] for v in vs[n+1:]))

    def test_one_step_exact_samples(self):
        smooth, convex = samples(0)
        self.assertEqual(smooth, c1.SMOOTH)
        self.assertEqual(convex, c1.NONSMOOTH)

    def test_one_step_exact_constraints_objective(self):
        cs, obj = compile_profile(0)
        self.assertEqual(cs, c1.CONSTRAINTS)
        self.assertEqual(obj, c1.OBJECTIVE)
        self.assertTrue(c1.accepted(constraints=cs, objective=obj))

    def test_one_step_primal_and_mutations_preserved(self):
        cs, obj = compile_profile(0)
        self.assertTrue(all(e.evaluate(c1.PRIMAL_VALUES, c1.PRIMAL_GRAM) >= 0 for e in cs))
        self.assertEqual(obj.evaluate(c1.PRIMAL_VALUES, c1.PRIMAL_GRAM), Q(1,4))
        self.assertFalse(c1.accepted(constraints=cs, objective=obj, bound=Q(1,5)))
        self.assertFalse(c1.accepted(constraints=cs, objective=val(5,5,2)-val(5,5,0)))

    def test_two_step_trajectory(self):
        self.assertEqual(positions(1)[2], tuple(map(Q, [1,0,-1,-1,0,-1,-1])))
        self.assertEqual(len(compile_profile(1)[0]), 26)

    def test_constraint_counts_and_self_pairs(self):
        for n in range(7):
            cs, _ = compile_profile(n)
            p, m = count('valueCount',n), count('basisCount',n)
            a, b = samples(n)
            self.assertEqual(len(cs), (n+3)**2+(n+2)**2+1)
            for kind, rows in [('smooth',a),('convex',b)]:
                for s in rows:
                    self.assertEqual(pair(p,kind,s,s), c1.Expr.zero(p,m))

    def test_generic_algebraic_realization(self):
        for n in range(13):
            for dim in (1,2,5):
                grad = [tuple(Q((k+1)*(j+2)-3, 11) for j in range(dim)) for k in range(n+2)]
                ss = [tuple(Q((k+2)*(j+1)-4, 13) for j in range(dim)) for k in range(n+1)]
                center = tuple(Q(j+1,3) for j in range(dim))
                xs = [tuple(Q(j+2,5) for j in range(dim))]
                for k in range(n+1):
                    xs.append(c1.sub(c1.sub(xs[-1],grad[k]),ss[k]))
                base = [c1.sub(xs[0],center),center] + grad + ss
                for k, v in enumerate(positions(n)):
                    self.assertEqual(realize(v,base), c1.sub(xs[k],center))

    def test_actual_prox_residuals_and_realization(self):
        for n in (0,1,2,5,11):
            for dim in (1,2,5):
                for lam in (Q(0),Q(1,7)):
                    f,g,h,c,xs,ss,base,values,G = actual_example(n,dim,lam)
                    for k in range(n+1):
                        self.assertEqual(xs[k+1],c1.sub(c1.sub(xs[k],g(xs[k])),ss[k]))
                        # Coordinate subgradient of lambda*|x-c|-a*x.
                        for z,ci,si,ai in zip(xs[k+1],c,ss[k],g(c),strict=True):
                            self.assertTrue(-lam-ai <= si <= lam-ai)
                            if z > ci: self.assertEqual(si,lam-ai)
                            if z < ci: self.assertEqual(si,-lam-ai)
                    for k,v in enumerate(positions(n)):
                        self.assertEqual(realize(v,base),c1.sub(xs[k],c))

    def test_actual_all_component_slacks(self):
        for n in (0,1,3,7,11):
            for dim in (1,2,5):
                f,g,h,c,xs,ss,base,values,G = actual_example(n,dim)
                smooth = [(c,g(c),f(c))]+[(x,g(x),f(x)) for x in xs]
                nonsmooth = [(c,c1.scale(-1,g(c)),h(c))]+[(x,s,h(x)) for x,s in zip(xs[1:],ss,strict=True)]
                for kind,rows in [('smooth',smooth),('convex',nonsmooth)]:
                    for x,s,fx in rows:
                        for y,t,fy in rows:
                            self.assertGreaterEqual(finite_actual_pair(kind,fx,fy,x,y,s,t),0)

    def test_compiled_actual_constraints_and_objective(self):
        for n in range(5):
            cs,obj = compile_profile(n)
            f,g,h,c,xs,ss,base,values,G = actual_example(n,2)
            self.assertTrue(all(e.evaluate(values,G) >= 0 for e in cs))
            self.assertEqual(obj.evaluate(values,G), f(xs[-1])+h(xs[-1])-f(c)-h(c))
            self.assertEqual(cs[-1].evaluate(values,G),1-c1.dot(base[0],base[0]))
            self.assertGreater(cs[-1].evaluate(values,G),0)

    def test_compiled_pair_equals_actual_pair(self):
        for n in range(4):
            f,g,h,c,xs,ss,base,values,G = actual_example(n,2)
            a,b = samples(n)
            for kind,rows in [('smooth',a),('convex',b)]:
                for u in rows:
                    for v in rows:
                        direct = finite_actual_pair(kind,values[u.slot],values[v.slot],
                            realize(u.position,base),realize(v.position,base),
                            realize(u.oracle,base),realize(v.oracle,base))
                        self.assertEqual(pair(len(values),kind,u,v).evaluate(values,G),direct)

    def test_zero_radius_and_nonzero_star_gradient(self):
        for n in range(7):
            f,g,h,c,xs,ss,base,values,G = actual_example(n,3,zero_radius=True)
            self.assertTrue(all(x == c for x in xs))
            self.assertTrue(any(gi != 0 for gi in g(c)))
            self.assertTrue(all(s == c1.scale(-1,g(c)) for s in ss))
            self.assertEqual(f(xs[-1])+h(xs[-1])-f(c)-h(c),0)

    def test_prefix_run_consistency(self):
        long = actual_example(11,2)
        for n in range(8):
            short = actual_example(n,2)
            self.assertEqual(short[4],long[4][:n+2])
            self.assertEqual(short[5],long[5][:n+1])

    def test_wrong_residual_sign_detected(self):
        _,g,_,c,xs,ss,base,_,_ = actual_example(1,1,lam=Q(1,5))
        wrong = list(positions(1)[1]); wrong[5] = Q(1)
        self.assertNotEqual(realize(wrong,base),c1.sub(xs[1],c))

    def test_off_by_one_residual_detected(self):
        n=2; v=positions(n)[1]
        swapped=list(v); swapped[n+4],swapped[n+5]=swapped[n+5],swapped[n+4]
        base=[(Q(i*i+1),) for i in range(count('basisCount',n))]
        self.assertNotEqual(realize(swapped,base),realize(v,base))

    def test_final_gradient_is_observation_not_update(self):
        n=3; base=[(Q(i+1),) for i in range(count('basisCount',n))]
        changed=list(base); changed[n+3]=(Q(999),)
        self.assertTrue(all(realize(v,base)==realize(v,changed) for v in positions(n)))
        a,_=samples(n)
        self.assertNotEqual(realize(a[-1].oracle,base),realize(a[-1].oracle,changed))

    def test_cross_component_and_wrong_smoothness_detected(self):
        a,b=samples(1);p=count('valueCount',1)
        self.assertNotEqual(pair(p,'smooth',a[0],a[-1]),pair(p,'smooth',a[0],b[-1]))
        self.assertNotEqual(pair(p,'convex',b[0],b[-1]),pair(p,'smooth',b[0],b[-1]))

    def test_zero_updates_do_not_imply_zero_gap(self):
        # No update => an arbitrary nonsmooth initial gap is possible.
        for M in (Q(1),Q(100),Q(10000)):
            self.assertEqual(M*max(Q(1),Q(0))-M*max(Q(0),Q(0)),M)

if __name__ == '__main__':
    unittest.main()
