"""D11 candidate search. All committed examples are simulated, not live captures."""
import copy
from dataclasses import replace
from fractions import Fraction as Q
from pathlib import Path
import json
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import import_exact_gram_bundle as gram
import import_proximal_gradient_sparse as sparse
import prepare_proximal_gradient_candidates as prep
import complete_bounded_pepit_capture as comp
import regenerate_bounded_pepit_capture as regen
import solve_exact_box_system as box
import solve_exact_linear_system as lin

ROOT=Path(__file__).resolve().parents[2]

class CaptureTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.inputs={w:gram.load_json(ROOT/f'data/fixtures/pepit_bounded/pg_{w}.json') for w in ['one','two','three','budget']}
        cls.results={w:comp.complete(d) for w,d in cls.inputs.items()}
    def case(self,w='one'):return copy.deepcopy(self.inputs[w])
    def test_01_d10_rejected_d11_accepted(self):
        for w in ['one','two','three']:
            a=self.results[w];self.assertFalse(a.previous.report['completion_accepted']);self.assertTrue(a.report['completion_accepted'])
    def test_02_negative_free_variable_repaired(self):
        for w in ['one','two','three']:
            a=self.results[w];j=a.previous.linear.free_columns[-1]
            self.assertLess(a.previous.linear.solution[j],0);self.assertEqual(a.result.solution[j],0)
    def test_03_not_clipping_raw(self):
        for a in self.results.values():
            self.assertEqual(a.previous.capture.capture,self.inputs[next(w for w,v in self.results.items() if v is a)])
    def test_04_fixed_residual_and_factor(self):
        a=self.results['three'];s=a.previous.capture.prepared.reconstructed.artifact.upper
        self.assertEqual(a.artifact.upper.dual_matrix,s.dual_matrix);self.assertEqual(a.artifact.upper.dual_factor,s.dual_factor)
    def test_05_source_unchanged(self):
        a=self.results['one'];self.assertEqual(prep.source_tree(a.artifact),a.previous.capture.source)
    def test_06_references_zero_row_kept(self):
        a=self.results['one'];raw=a.previous.capture.prepared.raw.artifact.upper
        self.assertEqual([t.index for t in a.artifact.upper.assumption_terms],[t.index for t in raw.assumption_terms])
        self.assertEqual(len(a.artifact.compact_rows),11)
    def test_07_complete_equations(self):
        for w in ['one','two','three']:
            a=self.results[w];self.assertTrue(lin.is_solution(a.box.system,a.result.solution))
    def test_08_bounds_from_raw(self):
        a=self.results['one'];self.assertEqual(a.box.lower[0],Q('0.2501')-Q('0.001'))
        self.assertEqual(a.box.upper[-1],Q('-0.0001')+Q('0.001'));self.assertEqual(a.box.lower[-1],0)
    def test_09_bound_has_no_sign_clipping(self):
        c=self.results['one'].artifact.upper
        lo,hi=comp.raw_bounds(replace(c,bound=Q(-1)),Q(1,2));self.assertEqual(lo[0],Q(-3,2));self.assertEqual(hi[0],Q(-1,2))
    def test_10_original_policy_after_search(self):
        for w in ['one','two','three']:self.assertTrue(all(self.results[w].report['completed_policy_checks'].values()))
    def test_11_budget_infeasible_affine_feasible(self):
        a=self.results['budget'];self.assertEqual(a.previous.linear.status,'solution');self.assertEqual(a.result.status,'infeasible')
        self.assertTrue(a.previous.report['completed_diagnostic']['diagnostic_passed'])
    def test_12_exact_margin(self):
        a=self.results['budget'];self.assertEqual(box.obstruction_value(a.box,a.result.obstruction),Q(-21,10000))
    def test_13_no_false_pep_infeasibility_claim(self):
        self.assertIn('not general PEP infeasibility',self.results['budget'].report['failure_scope'])
    def test_14_infeasible_no_upper(self):
        a=self.results['budget'];self.assertIsNone(a.artifact);self.assertNotIn('theorem actual_upper',comp.render_replay(a,'LeanPEP.Imported.Test.Budget'))
    def test_15_limit_is_unknown(self):
        a=comp.complete(self.case(),max_pivots=0);self.assertEqual(a.result.status,'limit');self.assertIsNone(a.artifact)
        self.assertNotIn('no_box_solution',comp.render_replay(a,'LeanPEP.Imported.Test.Limit'))
    def test_16_data_is_not_live(self):
        for a in self.results.values():
            self.assertFalse(a.report['live_capture_performed']);self.assertFalse(a.report['lean_checked'])
            self.assertEqual(a.report['producer_claim']['mode'],'simulated_regression')
    def test_17_no_optimality_claim(self):
        for a in self.results.values():
            self.assertFalse(a.report['optimal_bound_claimed']);self.assertFalse(a.report['nearest_solution_claimed'])
            self.assertFalse(a.report['denominator_constraint_searched'])
    def test_18_standalone_replay_old_checker(self):
        t=comp.render_replay(self.results['one'],'LeanPEP.Imported.Test.Replay')
        self.assertIn(comp.old.AS+'.checkCompletedQ',t);self.assertIn('actual_upper',t)
        self.assertIn('completion_vector_check',t);self.assertIn('raw_vector_check',t);self.assertNotIn('native_decide',t)
    def test_19_only_data_in_module(self):
        t=comp.render_module(self.results['one'],'LeanPEP.Imported.Test.Data');self.assertNotRegex(t,r'(?m)^theorem ')
        self.assertIn('freeSeedUpperQ',t);self.assertIn('completedUpperQ',t)
    def test_20_generator_reproduces_files(self):
        for p,t in regen.generate().items():self.assertEqual(p.read_text(),t,str(p))
    def test_21_old_positive_input_reused(self):
        d=gram.load_json(ROOT/'data/fixtures/pepit_completion/pg_one.json');a=comp.complete(d)
        self.assertTrue(a.report['completion_accepted']);self.assertTrue(a.result.seed_used)
    def test_22_wrong_horizon(self):
        with self.assertRaises(ValueError):comp.complete(self.case(),3)
    def test_23_nonfinite_refused(self):
        d=self.case();d['numerical']['multipliers'][0]='NaN'
        with self.assertRaises(ValueError):comp.complete(d)
    def test_24_bad_source_not_repaired(self):
        d=self.case();d['constraints'][0]['expression']['const']={'num':12,'den':1}
        a=comp.complete(d);self.assertFalse(a.report['completion_accepted'])
    def test_25_malicious_solver_result_rejected(self):
        bad=box.Result('feasible',(Q(0),)*12,None,0)
        with patch.object(comp.box,'solve',return_value=bad):
            with self.assertRaises(ArithmeticError):comp.complete(self.case())
    def test_26_untrusted_system_compiler_cannot_prove_upper(self):
        def bogus(a):return lin.System.make(1+len(a.upper.assumption_terms),[],[])
        with patch.object(comp.old,'coefficient_system',side_effect=bogus):
            a=comp.complete(self.case());self.assertFalse(a.report['completion_accepted'])
    def test_27_roundtrip_final_exact_json(self):
        a=self.results['two'];b=sparse.parse_artifact(sparse.artifact_tree(a.artifact),2)
        self.assertTrue(sparse.diagnose(b)['diagnostic_passed'])
    def test_28_denominator_check_can_reject_after_feasibility(self):
        # Assert final acceptance actually incorporates all policy components,
        # including denominator bounds, rather than relying solely on the box.
        real=comp.prep.changes_diagnostic
        def deny(*args,**kw):
            d=real(*args,**kw);d['denominators']=False;return d
        with patch.object(comp.prep,'changes_diagnostic',side_effect=deny):
            a=comp.complete(self.case());self.assertEqual(a.result.status,'feasible');self.assertFalse(a.report['completion_accepted'])
    def test_29_cli_success(self):
        with tempfile.TemporaryDirectory() as td:
            r=subprocess.run([sys.executable,str(ROOT/'tools/complete_bounded_pepit_capture.py'),
                str(ROOT/'data/fixtures/pepit_bounded/pg_one.json'),'--output-dir',td,'--namespace','LeanPEP.Imported.Test.CLI','--require-completed-pass'],capture_output=True,text=True)
            self.assertEqual(r.returncode,0,r.stderr);self.assertTrue((Path(td)/'completed_exact.json').exists())
    def test_30_cli_infeasible_status(self):
        with tempfile.TemporaryDirectory() as td:
            r=subprocess.run([sys.executable,str(ROOT/'tools/complete_bounded_pepit_capture.py'),
                str(ROOT/'data/fixtures/pepit_bounded/pg_budget.json'),'--output-dir',td,'--namespace','LeanPEP.Imported.Test.CLI','--require-completed-pass'],capture_output=True,text=True)
            self.assertEqual(r.returncode,2,r.stderr);self.assertFalse((Path(td)/'completed_exact.json').exists())
            self.assertIn('no_box_solution',(Path(td)/'Replay.lean').read_text())
    def test_31_cli_refuses_stale_directory(self):
        with tempfile.TemporaryDirectory() as td:
            old=Path(td)/'completed_exact.json';old.write_text('old')
            r=subprocess.run([sys.executable,str(ROOT/'tools/complete_bounded_pepit_capture.py'),
                str(ROOT/'data/fixtures/pepit_bounded/pg_one.json'),'--output-dir',td,'--namespace','LeanPEP.Imported.Test.CLI'],capture_output=True,text=True)
            self.assertEqual(r.returncode,1);self.assertEqual(old.read_text(),'old')
    def test_32_outputs_keep_free_seed_attempt(self):
        a=self.results['one'];names={p.name for p in comp.outputs(a,Path('/tmp/x'),'LeanPEP.Imported.Test.X')}
        self.assertTrue({'free_seed_exact.json','free_seed_report.json','seed_exact.json','raw_exact.json','completed_exact.json'}<=names)
    def test_33_no_new_source_assumptions(self):
        a=self.results['three'];self.assertEqual(len(a.artifact.compact_rows),len(a.previous.capture.captured_rows))
    def test_34_both_gram_axes_still_fixed(self):
        a=self.results['two'];self.assertEqual(a.box.system,a.previous.system)
        self.assertEqual(len(a.box.system.rhs),1+len(a.artifact.upper.objective.value_coeff)+len(a.artifact.upper.dual_matrix)**2)

if __name__=='__main__':unittest.main()
