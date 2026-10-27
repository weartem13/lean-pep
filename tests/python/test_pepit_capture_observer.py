#!/usr/bin/env python3
"""D13 extractor tests with explicit object-protocol doubles, NOT PEPit runs.

The old simulated archive supplies symbolic arrays only for the test double.
No fixture is relabelled or installed as live evidence, and no solve is invoked.
"""
from __future__ import annotations
import copy
from fractions import Fraction as Q
from pathlib import Path
from types import ModuleType, SimpleNamespace
import sys
import unittest
from unittest import mock

import numpy as np
import import_exact_gram_bundle as gram
import capture_pepit_proximal_gradient as live
import import_pepit_proximal_gradient_capture as cap

ROOT=Path(__file__).resolve().parents[2]

class Atom:
    def __init__(self, counter=-1, name=''):
        self.counter=counter;self.name=name;self.decomposition_dict={}
    def set_name(self,name):self.name=name
    def get_name(self):return self.name
    def eval(self):raise AssertionError('Point/Expression.eval must not be used by raw capture')

class Value(Atom):pass

class Constraint:
    def __init__(self,row,expr,weight):
        self.name=row['name'];self.expression=expr;self.weight=weight
        self.equality_or_inequality='inequality';self.activated=True
    def get_name(self):return self.name
    def eval_dual(self):return self.weight

class Iat:
    def __init__(self,rows):self.rows=rows
    def __getitem__(self,indices):i,j=indices;return self.rows[i][j]

class Protocol:
    """Minimal pinned-API shape; this class never numerically solves a PEP."""
    def __init__(self):
        self.d=gram.load_json(ROOT/'data/fixtures/pepit_capture/pg_one.json')
        self.points=[Atom(i,k) for i,k in enumerate(self.d['basis_order'])]
        self.values=[Value(i,k) for i,k in enumerate(self.d['value_order'])]
        for x in self.points+self.values:x.decomposition_dict={x:Q(1)}
        self.p_roles=dict(zip(self.d['basis_order'],self.points))
        self.v_roles={k:v for k,v in zip(self.d['value_order'],self.values) if k!='tau'}
        self.logical=[self.p_roles['x_star'],self.p_roles['x0'],self.point(next(s['position'] for s in self.d['smooth_samples'] if s['logical_index']==2))]
        def samples(records,nonsmooth=False):
            out=[]
            for r in records:
                j=r['logical_index'];i=0 if j==0 else j+1 if nonsmooth else j
                out.append((self.logical[i],self.point(r['oracle']),self.values[r['value_index']]))
            return out
        self.f=SimpleNamespace(list_of_points=samples(self.d['smooth_samples']))
        self.h=SimpleNamespace(list_of_points=samples(self.d['nonsmooth_samples'],True))
        self.rows=[Constraint(r,self.expr(r['expression']),float(w)) for r,w in
            zip(self.d['constraints'],self.d['numerical']['multipliers'])]
        tables={'smoothPair':[[0]*3 for _ in range(3)],'convexPair':[[0]*2 for _ in range(2)]}
        for r,c in zip(self.d['constraints'],self.rows):
            label=r['label']
            if label['kind']=='base':
                tag=label['tag']
                if tag['kind']=='radius':self.initial=c
                else:
                    samples=self.d['smooth_samples' if tag['kind']=='smoothPair' else 'nonsmooth_samples']
                    stored=[sample['logical_index'] for sample in samples]
                    tables[tag['kind']][stored.index(tag['i'])][stored.index(tag['j'])]=c
        self.f.tables_of_constraints={'smoothness_convexity':SimpleNamespace(iat=Iat(tables['smoothPair']))}
        self.h.tables_of_constraints={'convexity':SimpleNamespace(iat=Iat(tables['convexPair']))}
        self.objective=self.values[self.d['value_order'].index('tau')]
        self.metric=self.expr(self.d['metric'])
        self._list_of_prepared_constraints=self.rows
        self._list_of_prepared_psd=[]
        self._list_of_constraints_sent_to_wrapper=[]
        self.residual=np.array(self.d['numerical']['residual'],dtype=float)
        self.G=np.eye(len(self.points));self.F=np.arange(len(self.values),dtype=float)
        self.wrapper=SimpleNamespace(prob=SimpleNamespace(status='optimal'),solver_name='CLARABEL',
            get_primal_variables=lambda:(self.G,self.F))
        self.solve=mock.Mock(side_effect=self.solve_impl)
        self._prepare_constraints=mock.Mock()
        self.mutation=None
    def point(self,coeffs):
        qs=[Q(c['num'],c['den']) for c in coeffs]
        a=Atom();a.decomposition_dict={p:q for p,q in zip(self.points,qs) if q};return a
    def expr(self,e):
        a=Atom();d={};q=lambda c:Q(c['num'],c['den'])
        if q(e['const']):d[1]=q(e['const'])
        for v,c in zip(self.values,e['value_coeff']):
            if q(c):d[v]=q(c)
        for i,row in enumerate(e['gram_coeff']):
            for j,c in enumerate(row):
                if q(c):d[(self.points[i],self.points[j])]=q(c)
        a.decomposition_dict=d;return a
    def solve_impl(self,**kw):
        self._list_of_constraints_sent_to_wrapper=list(self.rows)
        if self.mutation:self.mutation()
        return .25
    def build(self):return self,self.f,self.h,self.logical,self.p_roles,self.v_roles,self.initial,self.metric
    def modules(self):
        pm,em,cm=ModuleType('PEPit.point'),ModuleType('PEPit.expression'),ModuleType('PEPit.constraint')
        pm.Point=Atom;em.Expression=Value;cm.Constraint=Constraint
        Atom.list_of_leaf_points=self.points;Value.list_of_leaf_expressions=self.values
        return {'PEPit.point':pm,'PEPit.expression':em,'PEPit.constraint':cm}
    def run(self,observer=None,**kwargs):
        with mock.patch.dict(sys.modules,self.modules()),mock.patch.object(live,'build_problem',return_value=self.build()):
            return live.capture(1,observer=observer,**kwargs)

class CaptureObserverTests(unittest.TestCase):
    def setUp(self):self.p=Protocol()
    def test_event_order(self):
        events=[]
        def observe(stage,d):
            if stage=='prepared':self.assertEqual(self.p.solve.call_count,0)
            else:self.assertEqual(self.p.solve.call_count,1)
            events.append(stage)
        self.p.run(observe);self.assertEqual(events,['prepared','capture','primal'])
    def test_prepared_only_never_solves(self):
        events=[];d=self.p.run(lambda s,d:events.append(s),prepare_only=True)
        self.assertEqual(events,['prepared']);self.p.solve.assert_not_called()
        self.assertEqual(d['producer']['mode'],'prepared_only');self.assertIsNone(d['numerical'])
    def test_prepared_source_passes_existing_audit(self):
        d=self.p.run(prepare_only=True);c=cap.convert(d)
        self.assertTrue(c.source_passed);self.assertTrue(all(cap.trace_diagnostic(c).values()))
    def test_observer_refusal_stops_before_solve(self):
        def refuse(stage,d):raise ValueError('stop at source')
        with self.assertRaisesRegex(ValueError,'stop at source'):self.p.run(refuse)
        self.p.solve.assert_not_called()
    def test_observer_cannot_mutate_captured_data(self):
        def edit(stage,d):d['unexpected']='mutation'
        d=self.p.run(edit);self.assertNotIn('unexpected',d)
    def test_order_filtering_detected(self):
        self.p.mutation=lambda:self.p._list_of_constraints_sent_to_wrapper.reverse()
        with self.assertRaisesRegex(ValueError,'filtered'):self.p.run()
    def test_leaf_change_detected(self):
        self.p.mutation=lambda:Atom.list_of_leaf_points.append(Atom(99,'extra'))
        with self.assertRaisesRegex(ValueError,'leaf'):self.p.run()
    def test_symbolic_constraint_mutation_detected(self):
        self.p.mutation=lambda:self.p.rows[0].expression.decomposition_dict.update({1:Q(8)})
        with self.assertRaisesRegex(ValueError,'symbolic source'):self.p.run()
    def test_objective_mutation_detected(self):
        self.p.mutation=lambda:self.p.objective.decomposition_dict.update({1:Q(8)})
        with self.assertRaisesRegex(ValueError,'symbolic source'):self.p.run()
    def test_function_sample_mutation_detected(self):
        self.p.mutation=lambda:self.p.f.list_of_points.reverse()
        with self.assertRaisesRegex(ValueError,'samples changed'):self.p.run()
    def test_missing_numeric_result(self):
        self.p.solve.side_effect=None;self.p.solve.return_value=None
        with self.assertRaisesRegex(RuntimeError,'no dual'):self.p.run()
    def test_solver_failure_preserves_prepared_event(self):
        self.p.solve.side_effect=RuntimeError('numeric failure');seen=[]
        with self.assertRaisesRegex(RuntimeError,'numeric failure'):self.p.run(lambda s,d:seen.append(s))
        self.assertEqual(seen,['prepared'])
    def test_primal_failure_follows_upper_archive(self):
        self.p.F=np.zeros(1);seen=[]
        with self.assertRaisesRegex(ValueError,'primal'):self.p.run(lambda s,d:seen.append(s))
        self.assertEqual(seen,['prepared','capture'])
    def test_original_no_observer_api_still_works(self):
        # Primal sidecar retrieval is optional for the legacy API.
        self.p.F=np.zeros(1);d=self.p.run()
        self.assertEqual(d['producer']['mode'],'live_solver_capture');self.assertEqual(len(d['numerical']['multipliers']),10)
    def test_all_weights_including_negative_and_zero_preserved(self):
        self.p.rows[0].weight=-1e-30;self.p.rows[1].weight=0.
        d=self.p.run();self.assertEqual(d['numerical']['multipliers'][:2],['-1e-30','0.0'])
    def test_numerical_residual_not_symmetrized(self):
        self.p.residual[0,1]=.125;self.p.residual[1,0]=.25
        d=self.p.run();self.assertEqual(d['numerical']['residual'][0][1],'0.125')
        self.assertEqual(d['numerical']['residual'][1][0],'0.25')
    def test_primal_matrix_negative_entry_preserved(self):
        self.p.G[0,0]=-1e-25;side={}
        self.p.run(lambda s,d:side.update({s:d}))
        self.assertEqual(side['primal']['gram'][0][0],'-1e-25')
        self.assertFalse(side['primal']['feasibility_checked']);self.assertFalse(side['primal']['actual_lower_bound_proved'])
    def test_primal_full_offdiagonal_axes_preserved(self):
        self.p.G[1,2]=.01;self.p.G[2,1]=.02;side={}
        self.p.run(lambda s,d:side.update({s:d}))
        self.assertEqual(side['primal']['gram'][1][2],'0.01');self.assertEqual(side['primal']['gram'][2][1],'0.02')
    def test_primal_records_tau_slot(self):
        side={};d=self.p.run(lambda s,d:side.update({s:d}))
        self.assertEqual(side['primal']['tau_index'],5)
        self.assertEqual(side['primal']['capture_sha256'],gram.canonical_json_sha256(d))
    def test_nonfinite_primal_rejected(self):
        self.p.G[0,0]=float('nan')
        with self.assertRaisesRegex(ValueError,'nonfinite'):self.p.run(lambda s,d:None)
    def test_dimension_reduction_not_requested(self):
        self.p.run();self.assertIsNone(self.p.solve.call_args.kwargs['dimension_reduction_heuristic'])
        self.assertEqual(self.p.solve.call_args.kwargs['solver'],'CLARABEL')
    def test_source_unchanged_by_solver_options(self):
        d=self.p.run(prepare_only=True)
        d2=self.p.run(solver_options={'tol_gap_abs':1e-10})
        for k in ('constraints','basis_order','value_order','metric','smooth_samples','nonsmooth_samples'):
            self.assertEqual(d[k],d2[k])
    def test_inactive_row_refused_before_solve(self):
        self.p.rows[0].activated=False
        with self.assertRaisesRegex(ValueError,'inactive'):self.p.run()
        self.p.solve.assert_not_called()
    def test_additional_psd_refused(self):
        self.p._list_of_prepared_psd=[object()]
        with self.assertRaisesRegex(ValueError,'LMI'):self.p.run()
        self.p.solve.assert_not_called()

if __name__=='__main__':unittest.main()
