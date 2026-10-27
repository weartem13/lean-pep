#!/usr/bin/env python3
"""Offline D9 protocol/extractor unit tests. No solver run is simulated as live."""
from __future__ import annotations
import copy
from dataclasses import replace
from fractions import Fraction as Q
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

import import_exact_gram_bundle as gram
import import_proximal_gradient_source as centered
import import_proximal_gradient_ordering as order
import import_proximal_gradient_rows as rows
import import_proximal_gradient_sparse as sparse
import prepare_proximal_gradient_candidates as prep
import import_pepit_proximal_gradient_capture as cap
import capture_pepit_proximal_gradient as live
import regenerate_pepit_proximal_gradient_capture as regen

ROOT=Path(__file__).resolve().parents[2]
class Atom:
    def __init__(self,d=None):self.decomposition_dict=d or {}

class CaptureTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.inputs={w:gram.load_json(ROOT/f'data/fixtures/pepit_capture/pg_{w}.json') for w in ('one','two','three')}
        cls.converted={w:cap.convert(d) for w,d in cls.inputs.items()}
    def case(self,w='one'):return copy.deepcopy(self.inputs[w])
    def test_01_all_sources_and_reconstruction(self):
        for c in self.converted.values():
            self.assertTrue(c.source_passed);self.assertTrue(c.prepared.report['reconstructed_joint_accepted_diagnostic'])
            self.assertTrue(all(cap.trace_diagnostic(c).values()))
            self.assertTrue(all(cap.raw_binding_diagnostic(c,c.prepared.raw.artifact.upper).values()))
    def test_02_raw_results_independent(self):
        self.assertTrue(self.converted['one'].prepared.report['raw_accepted_diagnostic'])
        for w in ('two','three'):self.assertFalse(self.converted[w].prepared.report['raw_accepted_diagnostic'])
    def test_03_every_dual_in_order(self):
        for c in self.converted.values():
            ts=c.prepared.raw.artifact.upper.assumption_terms
            self.assertEqual([t.index for t in ts],list(range(len(c.captured_rows))))
            self.assertTrue(any(t.weight==0 for t in ts))
    def test_04_tau_not_assumed_zero_slot(self):
        for c in self.converted.values():
            self.assertEqual(c.capture['value_order'].index('tau'),len(c.capture['value_order'])-1)
            self.assertEqual(c.source['objective']['value_coeff'][0],dict(num=1,den=1))
    def test_05_tau_all_positions(self):
        original=self.case();p=len(original['value_order'])
        for pos in range(p):
            d=self.case();perm=list(range(p-1));perm.insert(pos,p-1);inv={old:new for new,old in enumerate(perm)}
            d['value_order']=[d['value_order'][j] for j in perm]
            for e in [d['metric'],d['objective']]+[t['expression'] for t in d['constraints']]:
                e['value_coeff']=[e['value_coeff'][j] for j in perm]
            for s in d['smooth_samples']+d['nonsmooth_samples']:s['value_index']=inv[s['value_index']]
            c=cap.convert(d);self.assertTrue(c.source_passed)
            self.assertEqual(c.prepared.raw.artifact.upper,self.converted['one'].prepared.raw.artifact.upper)
    def test_06_reorder_rows_and_duals_together(self):
        d=self.case('two');d['constraints'].reverse();d['numerical']['multipliers'].reverse()
        c=cap.convert(d);self.assertTrue(c.prepared.report['reconstructed_joint_accepted_diagnostic'])
    def test_07_wrong_weight_order_rejected(self):
        d=self.case();d['numerical']['multipliers'].reverse()
        self.assertFalse(cap.convert(d).prepared.report['reconstructed_joint_accepted_diagnostic'])
    def test_08_missing_nonzero_row_rejected(self):
        d=self.case();i=next(i for i,c in enumerate(d['constraints']) if c['label']=={'kind':'performance'})
        d['constraints'].pop(i);d['numerical']['multipliers'].pop(i)
        with self.assertRaisesRegex(ValueError,'missing performance'):cap.convert(d)
    def test_09_missing_ordinary_row_rejected(self):
        d=self.case();d['constraints'].pop(0);d['numerical']['multipliers'].pop(0)
        with self.assertRaises(ValueError):cap.convert(d)
    def test_10_duplicate_row_rejected(self):
        d=self.case();d['constraints'].append(copy.deepcopy(d['constraints'][0]));d['numerical']['multipliers'].append('0')
        with self.assertRaises(ValueError):cap.convert(d)
    def test_11_equality_rejected(self):
        d=self.case();d['constraints'][0]['sense']='equality'
        with self.assertRaises(ValueError):cap.convert(d)
    def test_12_extra_metadata_rejected(self):
        d=self.case();d['trusted']=True
        with self.assertRaises(ValueError):cap.convert(d)
    def test_13_extra_leaf_rejected(self):
        d=self.case();d['basis_order'].append('extra')
        with self.assertRaises(ValueError):cap.convert(d)
    def test_14_wrong_class_rejected(self):
        d=self.case();d['profile']['smooth_class']='SmoothStronglyConvexFunction'
        with self.assertRaises(ValueError):cap.convert(d)
    def test_15_wrong_unit_parameter_rejected(self):
        for key in ('L','step_size','radius_squared'):
            d=self.case();d['profile'][key]={'num':2,'den':1}
            with self.assertRaises(ValueError):cap.convert(d)
    def test_16_wrong_horizon_rejected(self):
        with self.assertRaises(ValueError):cap.convert(self.case(),3)
    def test_17_wrong_version_rejected(self):
        d=self.case();d['producer']['version']='999'
        with self.assertRaises(ValueError):cap.convert(d)
    def test_18_wrong_sample_reference_rejected(self):
        d=self.case();d['smooth_samples'][0]['value_index']=len(d['value_order'])-1
        with self.assertRaises(ValueError):cap.convert(d)
    def test_19_sample_coefficient_not_repaired(self):
        d=self.case();d['smooth_samples'][0]['position'][0]={'num':123,'den':1}
        c=cap.convert(d);self.assertFalse(c.source_passed)
    def test_20_source_tiny_error_not_reconstructed(self):
        d=self.case();e=d['constraints'][0]['expression'];e['const']={'num':1,'den':10**30}
        c=cap.convert(d);self.assertFalse(c.source_passed)
        self.assertFalse(c.prepared.report['reconstructed_joint_accepted_diagnostic'])
    def test_21_hidden_tau_rejected(self):
        d=self.case();i=next(i for i,r in enumerate(d['constraints']) if r['label']['kind']=='base')
        d['constraints'][i]['expression']['value_coeff'][-1]={'num':1,'den':1}
        with self.assertRaisesRegex(ValueError,'depends on tau'):cap.convert(d)
    def test_22_negative_weight_not_filtered(self):
        d=self.case();i=d['numerical']['multipliers'].index('0');d['numerical']['multipliers'][i]='-0.000000000000000001'
        c=cap.convert(d);self.assertLess(c.prepared.raw.artifact.upper.assumption_terms[i].weight,0)
        self.assertFalse(c.prepared.report['raw_accepted_diagnostic'])
        self.assertEqual(len(c.prepared.raw.artifact.upper.assumption_terms),len(d['constraints']))
    def test_23_asymmetric_residual_not_repaired(self):
        d=self.case();d['numerical']['residual'][0][1]='123'
        c=cap.convert(d);self.assertEqual(c.prepared.raw.artifact.upper.dual_matrix[0][1],Q(123))
        self.assertFalse(c.prepared.report['raw_accepted_diagnostic'])
    def test_24_nonfinite_rejected(self):
        for x in ('NaN','Infinity','-Infinity'):
            d=self.case();d['numerical']['bound']=x
            with self.assertRaises(ValueError):cap.convert(d)
    def test_25_numeric_json_float_rejected(self):
        d=self.case();d['numerical']['bound']=.25
        with self.assertRaises(ValueError):cap.convert(d)
    def test_26_no_numeric_preparation_mode(self):
        d=self.case();d['numerical']=None;d['producer']['mode']='prepared_only'
        c=cap.convert(d);self.assertTrue(c.source_passed);self.assertIsNone(c.prepared)
        out=cap.outputs(c,Path('/tmp/d9-not-written'),'LeanPEP.Imported.Test')
        self.assertFalse(any(p.suffix=='.lean' for p in out))
    def test_27_no_live_claim_without_numbers(self):
        d=self.case();d['numerical']=None;d['producer']['mode']='live_solver_capture'
        with self.assertRaises(ValueError):cap.convert(d)
    def test_28_raw_bound_trace_mismatch(self):
        c=self.converted['one'];raw=c.prepared.raw.artifact.upper
        self.assertFalse(cap.raw_binding_diagnostic(c,replace(raw,bound=raw.bound+1))['bound'])
    def test_29_trace_residual_mismatch(self):
        c=self.converted['one'];raw=c.prepared.raw.artifact.upper
        G=[list(r) for r in raw.dual_matrix];G[0][1]+=1
        self.assertFalse(cap.raw_binding_diagnostic(c,replace(raw,dual_matrix=tuple(map(tuple,G))))['residual'])
    def test_30_extra_shared_zero_d8_passes_capture_fails(self):
        c=self.converted['one'];a=c.prepared.raw.artifact.upper;b=c.prepared.reconstructed.artifact.upper
        a=replace(a,assumption_terms=a.assumption_terms+(gram.AssumptionTermSpec(Q(0),0),))
        b=replace(b,assumption_terms=b.assumption_terms+(gram.AssumptionTermSpec(Q(0),0),))
        self.assertTrue(all(prep.changes_diagnostic(c.prepared.policy,a,b).values()))
        self.assertTrue(sparse.diagnose(replace(c.prepared.reconstructed.artifact,upper=b))['diagnostic_passed'])
        self.assertFalse(cap.raw_binding_diagnostic(c,a)['ordered_weights'])
    def test_31_wrong_tau_map_trace_fails(self):
        c=self.converted['one'];p=order.index_map(tuple(range(len(c.value_map.to_source))))
        self.assertFalse(cap.trace_diagnostic(c,value_map=p)['rows'])
    def test_32_symbolic_expansion_preserves_cross_terms(self):
        x,y,v=Atom(),Atom(),Atom();e=Atom({1:2,v:3,(x,y):5,(y,x):7,(x,x):-2})
        d=live.expression(e,[x,y],[v]);e=gram.parse_linear_expr(d,'e',1,2)
        self.assertEqual(e.gram_coeff,((Q(-2),Q(6)),(Q(6),Q(0))))
        self.assertEqual(e.const,2);self.assertEqual(e.value_coeff,(Q(3),))
    def test_33_exact_binary_source_vs_decimal_candidate(self):
        self.assertNotEqual(live.symbolic_scalar(.1),Q(1,10))
        self.assertEqual(prep.decimal(live.solver_decimal(.1),'x')[1],Q(1,10))
    def test_34_unknown_expression_leaf_rejected(self):
        with self.assertRaises(ValueError):live.expression(Atom({Atom():1}),[],[])
    def test_35_no_numeric_clipping(self):
        self.assertEqual(live.solver_decimal(-1e-30),'-1e-30')
        for x in (float('nan'),float('inf'),True):
            with self.assertRaises(ValueError):live.solver_decimal(x)
    def test_36_missing_runtime_is_explicit(self):
        with mock.patch('importlib.metadata.version',side_effect=live.importlib.metadata.PackageNotFoundError):
            with self.assertRaisesRegex(RuntimeError,'not installed'):live.build_problem(1)
    def test_37_regeneration_is_deterministic(self):
        for p,s in regen.generate().items():self.assertEqual(p.read_text(),s,str(p))
    def test_38_reports_do_not_claim_live(self):
        for c in self.converted.values():
            report=json.loads(cap.outputs(c,Path('/tmp/d9-no-write'),'LeanPEP.Imported.Test')[Path('/tmp/d9-no-write/capture_report.json')])
            self.assertEqual(report['producer_claim']['mode'],'simulated_regression')
            self.assertFalse(report['producer_authenticated']);self.assertFalse(report['lean_checked'])
            self.assertFalse(report['live_capture_performed_by_importer'])
    def test_39_cli_offline(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=subprocess.run([sys.executable,str(ROOT/'tools/import_pepit_proximal_gradient_capture.py'),
                str(ROOT/'data/fixtures/pepit_capture/pg_two.json'),'--output-dir',tmp,'--expected-steps','2',
                '--namespace','LeanPEP.Imported.TestCapture','--require-reconstructed-pass'],capture_output=True,text=True)
            self.assertEqual(p.returncode,0,p.stderr);self.assertTrue((Path(tmp)/'Capture.lean').exists())
    def test_40_help_needs_no_solver(self):
        p=subprocess.run([sys.executable,str(ROOT/'tools/capture_pepit_proximal_gradient.py'),'--help'],capture_output=True,text=True)
        self.assertEqual(p.returncode,0,p.stderr)
    def test_41_import_does_not_mutate_input(self):
        d=self.case();old=copy.deepcopy(d);cap.convert(d);self.assertEqual(old,d)
    def test_42_fixture_producer_untrusted(self):
        d=self.case();d['producer']['mode']='live_solver_capture'
        c=cap.convert(d);report=json.loads(cap.outputs(c,Path('/tmp/d9-x'),'LeanPEP.Imported.Test')[Path('/tmp/d9-x/capture_report.json')])
        self.assertFalse(report['producer_authenticated']);self.assertFalse(report['live_capture_performed_by_importer'])
    def test_43_exporter_no_formula_lookup(self):
        source=(ROOT/'tools/capture_pepit_proximal_gradient.py').read_text()
        self.assertNotIn('expected_snapshot(',source);self.assertNotIn('1/(4',source)
        self.assertNotIn('synthesize(',source);self.assertNotIn('data/fixtures/',source)
    def test_44_original_scalar_coefficients_exact(self):
        c=self.converted['two'];text=cap.render_module(c,'LeanPEP.Imported.Test')
        self.assertIn('def traceQ',text);self.assertIn('def rawUpperQ',text)
        self.assertNotRegex(text, r'(?m)^theorem\s');self.assertNotIn('native_decide',text)

if __name__=='__main__':unittest.main()
