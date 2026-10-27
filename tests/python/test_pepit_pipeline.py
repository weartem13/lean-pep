#!/usr/bin/env python3
"""D13 offline orchestration tests. Mocked live/Lean calls are NOT live or kernel evidence."""
from __future__ import annotations
import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import run_pepit_pipeline as pipe
import import_exact_gram_bundle as gram
import import_pepit_proximal_gradient_capture as cap

ROOT=Path(__file__).resolve().parents[2]
NS='LeanPEP.Imported.D13Test'

class PipelineTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name);self.out=self.root/'out'
    def replay(self, filename='data/fixtures/pepit_capture/pg_one.json', steps=1, **kw):
        return pipe.run_pipeline('replay', self.out, input_path=ROOT/filename,
            steps=steps, namespace=NS, skip_lean=kw.pop('skip_lean', True), **kw)
    def data(self): return gram.load_json(ROOT/'data/fixtures/pepit_capture/pg_one.json')
    def custom(self,d,**kw):
        path=self.root/'input.json';path.write_text(pipe.dump(d))
        return pipe.run_pipeline('replay',self.out,input_path=path,namespace=NS,skip_lean=True,**kw)
    def read_report(self): return gram.load_json(self.out/'pipeline_report.json')
    def test_raw_route(self):
        r,rc=self.replay();self.assertEqual(rc,0);self.assertEqual(r['selected_endpoint'],'raw')
        self.assertFalse(r['selection']['completion_attempted'])
    def test_reconstructed_route(self):
        r,rc=self.replay('data/fixtures/pepit_capture/pg_two.json',2)
        self.assertEqual((rc,r['selected_endpoint']),(0,'reconstructed'))
        self.assertFalse(r['selection']['raw_accepted']);self.assertTrue(r['selection']['reconstructed_accepted'])
    def test_completed_route(self):
        r,rc=self.replay('data/fixtures/pepit_bounded/pg_one.json')
        self.assertEqual((rc,r['selected_endpoint']),(0,'completed'))
        self.assertTrue(r['selection']['compiler_binding']['binding_diagnostic_passed'])
    def test_budget_obstruction_is_not_success(self):
        r,rc=self.replay('data/fixtures/pepit_bounded/pg_budget.json')
        self.assertEqual(rc,2);self.assertEqual(r['proof_kind'],'fixed_family_obstruction')
        self.assertFalse(r['candidate_accepted']);self.assertIsNone(r['bound'])
        self.assertFalse((self.out/'selected_exact.json').exists())
        self.assertNotIn('theorem actual_upper', (self.out/'Replay.lean').read_text())
    def test_skip_lean_never_verifies(self):
        with mock.patch.object(pipe,'check_lean',side_effect=AssertionError('not allowed')):
            r,_=self.replay()
        self.assertFalse(r['lean_checked']);self.assertFalse(r['actual_upper_verified'])
        self.assertFalse(r['d13_acceptance_met']);self.assertEqual(r['lean']['reason'],'explicitly_skipped')
    def test_copy_exact_archive_bytes(self):
        p=ROOT/'data/fixtures/pepit_capture/pg_one.json';before=p.read_bytes();r,_=self.replay()
        self.assertEqual((self.out/'capture.json').read_bytes(),before)
        self.assertEqual(p.read_bytes(),before);self.assertEqual(r['input_sha256'],r['capture_bytes_sha256'])
    def test_producer_metadata_cannot_make_replay_live(self):
        d=self.data();d['producer']['mode']='live_solver_capture';r,rc=self.custom(d)
        self.assertEqual(rc,0);self.assertFalse(r['live_capture_performed'])
        self.assertFalse(r['producer_authenticated']);self.assertFalse(r['d13_acceptance_met'])
    def test_source_corruption_is_not_repaired(self):
        d=self.data();d['metric']['const']={'num':1,'den':1};r,rc=self.custom(d)
        self.assertNotEqual(rc,0);self.assertFalse(r['actual_upper_verified'])
        self.assertFalse((self.out/'selected_exact.json').exists())
        self.assertEqual(gram.load_json(self.out/'capture.json'),d)
    def test_prepared_archive_has_no_upper(self):
        d=self.data();d['producer']['mode']='prepared_only';d['numerical']=None
        r,rc=self.custom(d);self.assertEqual((rc,r['status']),(0,'prepared_only'))
        self.assertFalse(r['candidate_accepted']);self.assertFalse((self.out/'Replay.lean').exists())
    def test_stale_directory_is_not_overwritten(self):
        self.out.mkdir();sentinel=self.out/'keep';sentinel.write_text('unchanged')
        with self.assertRaisesRegex(ValueError,'empty'):self.replay()
        self.assertEqual(sentinel.read_text(),'unchanged')
    def test_missing_input_leaves_error_not_success(self):
        r,rc=pipe.run_pipeline('replay',self.out,input_path=self.root/'missing',namespace=NS)
        self.assertEqual(rc,1);self.assertEqual(r['status'],'failed');self.assertTrue((self.out/'error.log').exists())
    def test_wrong_horizon(self):
        r,rc=self.replay(steps=2);self.assertNotEqual(rc,0);self.assertFalse(r['candidate_accepted'])
    def test_raw_template_uses_original_bridge(self):
        self.replay();t=(self.out/'Replay.lean').read_text()
        self.assertIn('raw_upper_firstOrder',t);self.assertIn('hf.toFirstOrder',t)
        self.assertIn('(rawUpperQ.bound : ℝ)',t);self.assertIn('theorem actual_upper',t)
        self.assertNotIn('sorry',t);self.assertNotIn('native_decide',t)
    def test_reconstructed_template_keeps_raw_rejection(self):
        self.replay('data/fixtures/pepit_capture/pg_two.json',2);t=(self.out/'Replay.lean').read_text()
        self.assertIn('rawUpperQ = false',t);self.assertIn('reconstructedUpperQ = true',t)
        self.assertIn('IsSmoothProxRun 2',t);self.assertIn('(reconstructedUpperQ.bound : ℝ)',t)
    def test_no_lean_binary(self):
        with mock.patch.object(pipe.shutil,'which',return_value=None):r,rc=self.replay(skip_lean=False)
        self.assertEqual(rc,3);self.assertEqual(r['lean']['reason'],'lake_unavailable')
        self.assertTrue(r['candidate_accepted']);self.assertFalse(r['lean_checked'])
    def test_lean_failure_keeps_candidate(self):
        with mock.patch.object(pipe,'check_lean',return_value={'checked':False,'reason':'replay_failed'}):
            r,rc=self.replay(skip_lean=False)
        self.assertEqual(rc,3);self.assertTrue((self.out/'selected_exact.json').exists())
        self.assertFalse(r['actual_upper_verified'])
    def test_mock_proof_success_replay_not_live(self):
        with mock.patch.object(pipe,'check_lean',return_value={'checked':True,'reason':None}):
            r,rc=self.replay(skip_lean=False)
        self.assertEqual(rc,0);self.assertTrue(r['actual_upper_verified'])
        self.assertFalse(r['live_capture_performed']);self.assertFalse(r['d13_acceptance_met'])
    def test_mock_negative_proof_is_not_upper(self):
        with mock.patch.object(pipe,'check_lean',return_value={'checked':True,'reason':None}):
            r,rc=self.replay('data/fixtures/pepit_bounded/pg_budget.json',skip_lean=False)
        self.assertEqual(rc,2);self.assertEqual(r['status'],'verified_obstruction')
        self.assertFalse(r['actual_upper_verified'])
    def test_missing_runtime_does_not_call_exporter(self):
        with mock.patch.object(pipe,'runtime_info',return_value={'capture_runtime_errors':['missing PEPit']}), \
             mock.patch.object(pipe.exporter,'capture',side_effect=AssertionError('should not run')):
            r,rc=pipe.run_pipeline('live',self.out,namespace=NS)
        self.assertEqual((rc,r['status']),(1,'runtime_unavailable'))
        self.assertFalse((self.out/'capture.json').exists());self.assertFalse(r['d13_acceptance_met'])
    def fake_exporter(self, bad_source=False, after_capture_error=False, wrong_solver=False):
        # Explicit TEST DOUBLE. Never written into the project's example tree.
        d=self.data();d['producer'].update(mode='live_solver_capture',solver='OTHER' if wrong_solver else 'CLARABEL')
        pre=copy.deepcopy(d);pre['producer']['mode']='prepared_only';pre['numerical']=None
        if bad_source:pre['metric']['const']={'num':1,'den':1}
        def fake(*args,observer=None,**kw):
            observer('prepared',pre)
            if args[2]:return pre
            observer('capture',d)
            if after_capture_error:raise RuntimeError('primal export failed')
            observer('primal',{'format':'explicit_test_double','feasibility_checked':False})
            return d
        return fake
    def mocked_live(self,**kw):
        with mock.patch.object(pipe,'runtime_info',return_value={'capture_runtime_errors':[]}), \
             mock.patch.object(pipe.exporter,'capture',side_effect=self.fake_exporter(
                 kw.pop('bad_source',False),kw.pop('after_capture_error',False),kw.pop('wrong_solver',False))):
            return pipe.run_pipeline('live',self.out,namespace=NS,skip_lean=True,**kw)
    def test_mock_live_prepared_saved(self):
        r,rc=self.mocked_live();self.assertEqual(rc,0)
        self.assertTrue((self.out/'prepared_capture.json').exists());self.assertTrue((self.out/'primal_observation.json').exists())
        self.assertFalse(r['actual_upper_verified']);self.assertFalse(r['d13_acceptance_met'])
    def test_bad_prepared_source_stops_mock_solve(self):
        r,rc=self.mocked_live(bad_source=True);self.assertEqual(rc,2)
        self.assertTrue((self.out/'prepared_capture.json').exists());self.assertFalse((self.out/'capture.json').exists())
    def test_primal_sidecar_failure_does_not_erase_upper_capture(self):
        r,rc=self.mocked_live(after_capture_error=True);self.assertEqual(rc,1)
        self.assertTrue((self.out/'capture.json').exists());self.assertFalse(r['actual_upper_verified'])
    def test_mock_live_prepare_only(self):
        r,rc=self.mocked_live(prepare_only=True);self.assertEqual(rc,0)
        self.assertEqual(r['status'],'prepared_only');self.assertFalse(r['live_capture_performed'])
        self.assertFalse((self.out/'capture.json').exists())
    def test_wrong_actual_solver_retains_record(self):
        r,rc=self.mocked_live(wrong_solver=True);self.assertEqual(rc,1)
        self.assertEqual(r['status'],'solver_mismatch');self.assertTrue((self.out/'capture.json').exists())
    def test_report_on_disk_matches_returned_report(self):
        r,_=self.replay();self.assertEqual(self.read_report(),r)
    def test_invalid_horizon_no_output(self):
        with self.assertRaises(ValueError):pipe.run_pipeline('live',self.out,steps=0)
        self.assertFalse(self.out.exists())
    def test_invalid_budget_no_output(self):
        with self.assertRaises(ValueError):pipe.run_pipeline('live',self.out,max_abs_error='-1')
        self.assertFalse(self.out.exists())
    def test_cli_reserved_solver_option(self):
        rc=pipe.main(['live','--output-dir',str(self.out),'--solver-options','{"dimension_reduction_heuristic":"trace"}'])
        self.assertEqual(rc,1);self.assertFalse(self.out.exists())
    def test_cli_nonfinite_solver_option(self):
        rc=pipe.main(['live','--output-dir',str(self.out),'--solver-options','{"tol":NaN}'])
        self.assertEqual(rc,1);self.assertFalse(self.out.exists())
    def test_axiom_summary_multiline(self):
        self.assertTrue(pipe.axiom_output_ok(f"'{NS}.actual_upper' depends on axioms: [propext,\n Classical.choice, Quot.sound]",NS,True))
    def test_missing_actual_theorem_rejected(self):
        self.assertFalse(pipe.axiom_output_ok(f"'{NS}.other' depends on axioms: [propext]",NS,True))
    def test_sorry_axiom_rejected(self):
        self.assertFalse(pipe.axiom_output_ok(f"'{NS}.actual_upper' depends on axioms: [propext, sorryAx]",NS,True))
    def test_foreign_namespace_rejected(self):
        self.assertFalse(pipe.axiom_output_ok("'Other.actual_upper' depends on axioms: [propext]",NS,True))
    def test_no_axiom_output_rejected(self):
        self.assertFalse(pipe.axiom_output_ok('exit 0',NS,True))
    def test_build_failure_does_not_run_replay(self):
        self.out.mkdir()
        with mock.patch.object(pipe.shutil,'which',return_value='/not-executed/lake'), \
             mock.patch.object(pipe,'invoke',return_value=1) as invoke:
            r=pipe.check_lean(self.out/'Replay.lean',self.out,NS,True)
        self.assertEqual(invoke.call_count,1);self.assertFalse(r['checked']);self.assertEqual(r['reason'],'build_failed')
    def test_mock_lean_zero_exit_needs_axiom_output(self):
        self.out.mkdir();(self.out/'lean_replay.log').write_text('no proof output')
        with mock.patch.object(pipe.shutil,'which',return_value='/not-executed/lake'), \
             mock.patch.object(pipe,'invoke',return_value=0):
            r=pipe.check_lean(self.out/'Replay.lean',self.out,NS,True)
        self.assertFalse(r['checked']);self.assertEqual(r['reason'],'missing_or_unexpected_axiom_output')

if __name__=='__main__':unittest.main()
