#!/usr/bin/env python3
"""Untrusted real smooth-only GD(2) capture; explicit reference origin/gradient zero."""
import argparse
import importlib.metadata
from pathlib import Path
from fractions import Fraction as Q
import capture_pepit_proximal_gradient as common
import run_pepit_pipeline as pipeline


def capture():
    if importlib.metadata.version('PEPit') != '0.5.1':
        raise ValueError('requires pinned PEPit 0.5.1')
    from PEPit import PEP
    from PEPit.point import Point
    from PEPit.expression import Expression
    from PEPit.functions import SmoothConvexFunction
    from PEPit.constraint import Constraint
    problem = PEP()
    f = problem.declare_function(SmoothConvexFunction, L=1)
    # Translation invariance fixes x_star=0; analytic stationarity supplies g_star=0.
    xs = Point(is_leaf=False, decomposition_dict={})
    gs = Point(is_leaf=False, decomposition_dict={})
    fs = Expression(); f.add_point((xs, gs, fs))
    x0 = problem.set_initial_point(name='x0')
    g0, f0 = f.oracle(x0)
    x1 = x0 - g0
    g1, f1 = f.oracle(x1)
    x2 = x1 - g1
    g2, f2 = f.oracle(x2)
    radius = x0 ** 2 <= 1
    problem.set_initial_condition(radius, name='initial_radius')
    metric = f2 - fs
    problem.set_performance_metric(metric, name='smooth_final_gap')
    problem._prepare_constraints(verbose=2)
    lp, lv = list(Point.list_of_leaf_points), list(Expression.list_of_leaf_expressions)
    if lp != [x0, g0, g1, g2] or lv != [fs, f0, f1, f2, problem.objective]:
        raise ValueError('unexpected native leaf order')
    labels = {id(radius): ['radius']}
    table = f.tables_of_constraints['smoothness_convexity']
    for i in range(4):
        for j in range(4):
            entry = table.iat[i, j]
            if isinstance(entry, Constraint): labels[id(entry)] = ['smooth', i, j]
            elif entry != 0: raise ValueError('unexpected table entry')
    rows = list(problem._list_of_prepared_constraints)
    perf = [c for c in rows if id(c) not in labels]
    if len(perf) != 1 or problem._list_of_prepared_psd: raise ValueError('unexpected constraints')
    labels[id(perf[0])] = ['performance']
    expr = lambda e: common.expression(e, lp, lv)
    constraints = []
    for c in rows:
        if c.equality_or_inequality != 'inequality' or not c.activated: raise ValueError('unsupported row')
        constraints.append(dict(label=labels[id(c)], sense='leZero', expression=expr(c.expression)))
    d = dict(format='lean-pep-gd-two-capture-v1', algorithm='smooth_only_gd', steps=2,
        profile=dict(L='1', radius_squared='1', step_size='1', target='f2-f_star'),
        reference=dict(position=['0']*4, gradient=['0']*4, rule='translate_reference_to_origin_and_stationarity'),
        basis_order=['x0_minus_x_star','g0','g1','g2'], value_order=['f_star','f0','f1','f2','tau'],
        samples=[dict(position=common.point_vector(x,lp), gradient=common.point_vector(g,lp), value_index=i)
            for i,(x,g,v) in enumerate(f.list_of_points)],
        metric=expr(metric), objective=expr(problem.objective), constraints=constraints,
        policy=dict(max_denominator=1000000,max_abs_error='0.000001'))
    options = dict(tol_gap_abs=1e-10,tol_gap_rel=1e-10,tol_feas=1e-10,max_iter=300)
    bound = problem.solve(wrapper='cvxpy',solver='CLARABEL',return_primal_or_dual='dual',
        dimension_reduction_heuristic=None,verbose=2,**options)
    if [id(c) for c in rows] != [id(c) for c in problem._list_of_constraints_sent_to_wrapper]:
        raise ValueError('sent row order changed')
    if len(rows)!=14 or any(expr(c.expression)!=r['expression'] for c,r in zip(rows,constraints)):
        raise ValueError('source changed')
    if list(Point.list_of_leaf_points)!=lp or list(Expression.list_of_leaf_expressions)!=lv:
        raise ValueError('leaf order changed')
    if problem.residual.shape != (4,4): raise ValueError('residual dimension')
    d.update(producer=dict(name='PEPit',version='0.5.1',wrapper='cvxpy',solver=str(problem.wrapper.solver_name),
        status=str(problem.wrapper.prob.status),options=options,live_capture_performed=True),
        numerical=dict(bound=common.solver_decimal(bound),multipliers=[common.solver_decimal(c.eval_dual()) for c in rows],
            residual=[[common.solver_decimal(problem.residual[i,j]) for j in range(4)] for i in range(4)]))
    return d


if __name__ == '__main__':
    ap=argparse.ArgumentParser(); ap.add_argument('--output',type=Path,required=True); args=ap.parse_args()
    if args.output.exists(): raise SystemExit('refusing overwrite')
    pipeline.write_json(args.output.parent/'environment.json',pipeline.runtime_info('CLARABEL',True))
    pipeline.write_json(args.output,capture())
