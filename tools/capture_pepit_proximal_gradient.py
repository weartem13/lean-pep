#!/usr/bin/env python3
"""D9 optional PEPit 0.5.1/CVXPY live exporter, for unit proximal gradient.

Reads actual expression/point decompositions, actual prepared and sent row
objects, each row dual and the independent residual. It NEVER imports a
certificate formula, reads regression examples, rounds source coefficients,
recomputes a dual matrix, filters multipliers or runs dimension reduction.
The optional runtime is deliberately lazy; --help works without PEPit.
The exporter itself and its producer metadata are untrusted by Lean.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
import importlib.metadata
import json
import math
import numbers
from pathlib import Path
import sys
from typing import Any, Callable
import copy

import import_exact_gram_bundle as gram
import import_proximal_gradient_source as centered
import import_pepit_proximal_gradient_capture as adapter


def symbolic_scalar(x: Any) -> Q:
    """Exact represented binary rational for symbolic float coefficients.
    No limit_denominator and no threshold; L=step=radius=1 produce dyadics.
    """
    if isinstance(x,bool): raise ValueError('Boolean is not a symbolic coefficient')
    if isinstance(x,numbers.Integral): return Q(int(x))
    if isinstance(x,Q): return x
    if isinstance(x,numbers.Real):
        y=float(x)
        if not math.isfinite(y): raise ValueError('nonfinite symbolic coefficient')
        return Q.from_float(y)
    raise ValueError('unsupported symbolic coefficient type '+type(x).__name__)


def solver_decimal(x: Any) -> str:
    if isinstance(x,bool): raise ValueError('Boolean is not a solver number')
    y=float(x)
    if not math.isfinite(y): raise ValueError('nonfinite solver number')
    return repr(y)


def expression(expr: Any, points: list[Any], values: list[Any]) -> dict[str,Any]:
    """Canonical symmetric coefficients of an actual symbolic decomposition.
    A term q*<v_i,v_j> contributes q/2 to each transposed slot. This is
    expression encoding, NOT symmetrization of the numerical dual residual.
    """
    pi={id(x):i for i,x in enumerate(points)}; vi={id(x):i for i,x in enumerate(values)}
    m,p=len(points),len(values); cs=Q(0);vs=[Q(0)]*p;G=[[Q(0)]*m for _ in range(m)]
    for key,coeff in expr.decomposition_dict.items():
        q=symbolic_scalar(coeff)
        if type(key) is int and key==1: cs+=q
        elif id(key) in vi: vs[vi[id(key)]]+=q
        elif isinstance(key,tuple) and len(key)==2 and all(id(x) in pi for x in key):
            i,j=(pi[id(x)] for x in key);G[i][j]+=q/2;G[j][i]+=q/2
        else: raise ValueError('expression references unsupported or non-leaf data')
    return centered.exact_json(dict(const=cs,value_coeff=vs,gram_coeff=G))


def point_vector(point: Any, leaves: list[Any]) -> list[dict[str,int]]:
    ix={id(x):i for i,x in enumerate(leaves)}; out=[Q(0)]*len(leaves)
    for leaf,c in point.decomposition_dict.items():
        if id(leaf) not in ix: raise ValueError('unknown point leaf')
        out[ix[id(leaf)]]+=symbolic_scalar(c)
    return centered.exact_json(out)


def build_problem(T: int):
    if type(T) is not int or T<1: raise ValueError('steps must be a positive integer')
    try:
        version=importlib.metadata.version('PEPit')
    except importlib.metadata.PackageNotFoundError as exc:
        raise RuntimeError('PEPit 0.5.1 is not installed; use requirements-pepit-capture.txt in an optional environment') from exc
    if version!=adapter.SUPPORTED_PEPIT: raise RuntimeError('this exporter requires PEPit '+adapter.SUPPORTED_PEPIT)
    from PEPit import PEP
    from PEPit.expression import Expression
    from PEPit.functions import SmoothConvexFunction, ConvexFunction
    from PEPit.primitive_steps import proximal_step
    problem=PEP(); f=problem.declare_function(SmoothConvexFunction,L=1);h=problem.declare_function(ConvexFunction)
    f.set_name('f');h.set_name('h')
    xs=problem.set_initial_point(name='x_star');gs,fs=f.oracle(xs)
    gs.set_name('g_star');fs.set_name('f_star')
    hs=Expression();hs.set_name('h_star')
    h.add_point((xs,-gs,hs))  # composite stationarity, NOT separate stationarity
    x0=problem.set_initial_point(name='x0')
    initial=(x0-xs)**2<=1;problem.set_initial_condition(initial,name='initial_radius')
    p_roles={'x_star':xs,'x0':x0,'g_star':gs};v_roles={'f_star':fs,'h_star':hs}
    x=x0;points=[xs,x0];last_h=hs
    for i in range(T):
        g,fi=f.oracle(x);g.set_name(f'g{i}');fi.set_name(f'f{i}')
        p_roles[f'g{i}']=g;v_roles[f'f{i}']=fi
        x,s,last_h=proximal_step(x-g,h,1)
        x.set_name(f'x{i+1}');s.set_name(f's{i+1}');last_h.set_name(f'h{i+1}')
        p_roles[f's{i+1}']=s;v_roles[f'h{i+1}']=last_h;points.append(x)
    gt,ft=f.oracle(x);gt.set_name(f'g{T}');ft.set_name(f'f{T}')
    p_roles[f'g{T}']=gt;v_roles[f'f{T}']=ft
    metric=ft+last_h-fs-hs;problem.set_performance_metric(metric,name='composite_final_gap')
    return problem,f,h,points,p_roles,v_roles,initial,metric


def capture(T: int, solver: str='CLARABEL', prepare_only: bool=False,
            max_denominator: int=1000000, max_abs_error: str='0.000001', verbose: int=0,
            solver_options: dict[str,Any] | None=None, *,
            observer: Callable[[str, dict[str, Any]], None] | None=None) -> dict[str,Any]:
    problem,f,h,logical_points,p_roles,v_roles,initial,metric=build_problem(T)
    from PEPit.point import Point
    from PEPit.expression import Expression
    from PEPit.constraint import Constraint
    # Freeze class constraints and the tau leaf before solving. This is the
    # exact pinned API called by solve() itself, not a reimplementation of ICs.
    problem._prepare_constraints(verbose=verbose)
    problem.objective.set_name('tau');v_roles['tau']=problem.objective
    lp=list(Point.list_of_leaf_points);lv=list(Expression.list_of_leaf_expressions)
    if [x.counter for x in lp]!=list(range(len(lp))) or [x.counter for x in lv]!=list(range(len(lv))):
        raise ValueError('unsupported leaf-counter layout')
    def roles(leaves,mapping):
        inv={id(x):role for role,x in mapping.items()}
        if len(inv)!=len(mapping) or set(inv)!={id(x) for x in leaves}:
            raise ValueError('extra, missing or dependent leaves; exporter does not eliminate them')
        return [inv[id(x)] for x in leaves]
    basis=roles(lp,p_roles);values=roles(lv,v_roles)
    point_id={id(p):i for i,p in enumerate(logical_points)}
    def samples(function, nonsmooth=False):
        out=[]
        for x,g,val in function.list_of_points:
            if id(x) not in point_id: raise ValueError('unexpected function sample')
            logical=point_id[id(x)]
            if nonsmooth:
                if logical==1: raise ValueError('unexpected nonsmooth sample at x0')
                if logical>1: logical-=1
            if id(val) not in {id(v) for v in lv}: raise ValueError('nonleaf function value')
            out.append(dict(logical_index=logical,value_index=next(i for i,v in enumerate(lv) if v is val),
                position=point_vector(x,lp),oracle=point_vector(g,lp)))
        return out
    sm=samples(f);ns=samples(h,True)
    labels={id(initial):dict(kind='base',tag=dict(kind='radius',i=None,j=None))}
    for fn,tabname,kind,ss in ((f,'smoothness_convexity','smoothPair',sm),(h,'convexity','convexPair',ns)):
        table=fn.tables_of_constraints[tabname]
        for i in range(len(ss)):
            for j in range(len(ss)):
                entry=table.iat[i,j]
                if isinstance(entry,Constraint):
                    labels[id(entry)]=dict(kind='base',tag=dict(kind=kind,i=ss[i]['logical_index'],j=ss[j]['logical_index']))
                elif entry!=0: raise ValueError('unexpected table scalar')
    prepared=list(problem._list_of_prepared_constraints)
    unidentified=[x for x in prepared if id(x) not in labels]
    if len(unidentified)!=1: raise ValueError('expected exactly one performance constraint')
    labels[id(unidentified[0])]=dict(kind='performance')
    if problem._list_of_prepared_psd: raise ValueError('additional LMI constraints are unsupported')
    active=prepared
    # Snapshot the actual prepared objects BEFORE solve, not a rebuilt model.
    cons=[]
    for c in active:
        if c.equality_or_inequality!='inequality' or not c.activated: raise ValueError('unsupported equality/inactive row')
        cons.append(dict(name=c.get_name(),label=labels[id(c)],sense='leZero',expression=expression(c.expression,lp,lv)))
    d=dict(format=adapter.FORMAT,producer=dict(name='PEPit',version=adapter.SUPPORTED_PEPIT,
        mode='prepared_only',wrapper='cvxpy',solver='none',status='not_solved'),
        horizon=T,profile=centered.exact_json(dict(smooth_class='SmoothConvexFunction',nonsmooth_class='ConvexFunction',
            L=Q(1),step_size=Q(1),radius_squared=Q(1))),basis_order=basis,value_order=values,
        smooth_samples=sm,nonsmooth_samples=ns,metric=expression(metric,lp,lv),objective=expression(problem.objective,lp,lv),
        constraints=cons,numerical=None,policy=dict(method='limit_denominator',max_denominator=max_denominator,
            max_abs_error=max_abs_error))
    if observer is not None:
        # A source-only observer may reject before the numerical solve starts.
        # Copies prevent callbacks from changing the captured mathematical data.
        observer('prepared', copy.deepcopy(d))
    if prepare_only:
        return d
    options=dict(solver_options or {})
    forbidden={'wrapper','solver','dimension_reduction_heuristic','return_primal_or_dual','verbose',
        'safe_mode','eig_regularization','tol_dimension_reduction'}
    if forbidden.intersection(options): raise ValueError('reserved solver option')
    bound=problem.solve(wrapper='cvxpy',solver=solver,return_primal_or_dual='dual',
        dimension_reduction_heuristic=None,verbose=verbose,**options)
    if bound is None: raise RuntimeError('solver returned no dual candidate')
    if getattr(problem, '_list_of_psd_sent_to_wrapper', []):
        raise ValueError('additional LMI constraints were sent during solve')
    if [id(x) for x in problem._list_of_constraints_sent_to_wrapper]!=[id(x) for x in prepared]:
        raise ValueError('inactive/filtered constraints; refusing a silently changed formulation')
    if [id(x) for x in Point.list_of_leaf_points]!=[id(x) for x in lp] or \
            [id(x) for x in Expression.list_of_leaf_expressions]!=[id(x) for x in lv]:
        raise ValueError('leaf set/order changed during solve')
    if samples(f)!=sm or samples(h,True)!=ns:
        raise ValueError('function samples changed during solve')
    if any(expression(c.expression,lp,lv)!=row['expression'] for c,row in zip(prepared,cons)) or \
            expression(problem.objective,lp,lv)!=d['objective'] or expression(metric,lp,lv)!=d['metric']:
        raise ValueError('symbolic source changed during solve')
    residual=problem.residual
    if tuple(residual.shape)!=(len(lp),len(lp)): raise ValueError('unexpected residual size')
    d['producer'].update(mode='live_solver_capture',status=str(problem.wrapper.prob.status),
        solver=str(problem.wrapper.solver_name))
    d['numerical']=dict(bound=solver_decimal(bound),
        multipliers=[solver_decimal(c.eval_dual()) for c in prepared],
        residual=[[solver_decimal(residual[i,j]) for j in range(len(lp))] for i in range(len(lp))])
    if observer is not None:
        # Save the upper record first, so a later primal-export failure cannot
        # erase a successfully obtained numerical candidate.
        observer('capture', copy.deepcopy(d))
        observer('primal', primal_observation(problem, d))
    # No candidate acceptance asserted here. No sign/PSD/source repair.
    return d


def primal_observation(problem: Any, captured: dict[str, Any]) -> dict[str, Any]:
    """Archive wrapper G/F, NOT Point.eval()'s possibly projected realization.

    This sidecar is intentionally NOT a primal certificate, and is not supplied
    to the D9 schema or to an upper checker. Its later exact audit is v0.14B work.
    """
    G,F=problem.wrapper.get_primal_variables()
    m,p=len(captured['basis_order']),len(captured['value_order'])
    if G is None or F is None or tuple(G.shape)!=(m,m) or tuple(F.shape)!=(p,):
        raise ValueError('unexpected raw primal variable dimensions')
    return dict(format='leanpep-primal-observation-v1',
        capture_sha256=gram.canonical_json_sha256(captured),
        source='PEPit.wrapper.get_primal_variables (optimal_G, optimal_F)',
        basis_order=copy.deepcopy(captured['basis_order']),
        value_order=copy.deepcopy(captured['value_order']),
        tau_index=captured['value_order'].index('tau'),
        gram=[[solver_decimal(G[i,j]) for j in range(m)] for i in range(m)],
        values=[solver_decimal(F[i]) for i in range(p)],
        point_eval_used=False,projection_performed_by_exporter=False,
        numerical_convention='finite_decimal_strings_v1',
        feasibility_checked=False,actual_lower_bound_proved=False,lean_checked=False)


def main(argv: list[str] | None=None) -> int:
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--steps',type=int,required=True)
    p.add_argument('--output',type=Path,required=True);p.add_argument('--solver',default='CLARABEL')
    p.add_argument('--prepare-only',action='store_true');p.add_argument('--verbose',type=int,default=0)
    p.add_argument('--max-denominator',type=int,default=1000000);p.add_argument('--max-abs-error',default='0.000001')
    p.add_argument('--solver-options',default='{}',help='JSON dictionary of solver options; no formula defaults')
    a=p.parse_args(argv)
    try:
        options=json.loads(a.solver_options)
        if not isinstance(options,dict): raise ValueError('solver options must be an object')
        d=capture(a.steps,a.solver,a.prepare_only,a.max_denominator,a.max_abs_error,a.verbose,options)
        gram.atomic_write(a.output,json.dumps(d,indent=2,sort_keys=True)+'\n')
        print(json.dumps(dict(output=str(a.output),mode=d['producer']['mode'],source_rows=len(d['constraints']),
            lean_checked=False,candidate_acceptance_not_claimed=True)))
        return 0
    except (ValueError,RuntimeError,OSError,ImportError) as e:
        print('error: '+str(e),file=sys.stderr);return 1

if __name__=='__main__': raise SystemExit(main())
