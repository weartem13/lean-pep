"""D10 completion and immutable-target tests; fixtures are NOT live captures."""
import copy
from dataclasses import replace
from fractions import Fraction as Q
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import import_exact_gram_bundle as gram
import import_proximal_gradient_sparse as sparse
import import_pepit_proximal_gradient_capture as cap
import prepare_proximal_gradient_candidates as prep
import complete_pepit_proximal_gradient_capture as comp
import regenerate_pepit_proximal_gradient_completion as regen
import solve_exact_linear_system as ls

ROOT=Path(__file__).resolve().parents[2]
class CompletionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data={w:gram.load_json(ROOT/f'data/fixtures/pepit_completion/pg_{w}.json') for w in ('one','two','three','inconsistent')}
        cls.results={w:comp.complete(d) for w,d in cls.data.items()}
    def case(self,w='one'):return copy.deepcopy(self.data[w])
    def test_01_seed_fails_final_passes(self):
        for w in ('one','two','three'):
            a=self.results[w];self.assertFalse(a.report['seed_accepted']);self.assertTrue(a.report['completion_accepted'])
    def test_02_all_equations_exact(self):
        for w in ('one','two','three'):
            a=self.results[w];self.assertTrue(ls.is_solution(a.system,a.linear.solution))
    def test_03_independent_residual_fixed(self):
        for w in ('one','two','three'):
            a=self.results[w];self.assertEqual(a.artifact.upper.dual_matrix,a.capture.prepared.reconstructed.artifact.upper.dual_matrix)
    def test_04_factor_payload_fixed(self):
        a=self.results['three'];self.assertEqual(a.artifact.upper.dual_factor,a.capture.prepared.reconstructed.artifact.upper.dual_factor)
    def test_05_objective_fixed(self):
        a=self.results['two'];self.assertEqual(a.artifact.upper.objective,a.capture.prepared.reconstructed.artifact.upper.objective)
    def test_06_source_fixed(self):
        for w in ('one','two','three'):
            a=self.results[w];self.assertEqual(prep.source_tree(a.artifact),a.capture.source)
    def test_07_references_and_zeros_retained(self):
        a=self.results['three'];raw=a.capture.prepared.raw.artifact.upper;out=a.artifact.upper
        self.assertEqual([t.index for t in raw.assumption_terms],[t.index for t in out.assumption_terms])
        self.assertEqual(len(out.assumption_terms),len(a.capture.captured_rows));self.assertTrue(any(t.weight==0 for t in out.assumption_terms))
    def test_08_input_immutable(self):
        d=self.case();before=copy.deepcopy(d);comp.complete(d);self.assertEqual(d,before)
    def test_09_raw_reconstructed_immutable(self):
        a=self.results['one'];before=cap.convert(self.case()).prepared
        self.assertEqual(a.capture.prepared.raw,before.raw);self.assertEqual(a.capture.prepared.reconstructed,before.reconstructed)
    def test_10_final_within_original_policy(self):
        for w in ('one','two','three'):
            self.assertTrue(all(self.results[w].report['completed_policy_checks'].values()))
    def test_11_correct_expected_fixture_values(self):
        for T,w in enumerate(('one','two','three'),1):self.assertEqual(self.results[w].artifact.upper.bound,Q(1,4*T))
    def test_12_failure_has_exact_obstruction(self):
        a=self.results['inconsistent'];self.assertIsNone(a.artifact);self.assertTrue(ls.is_obstruction(a.system,a.linear.obstruction))
    def test_13_psd_does_not_imply_linear_compatibility(self):
        a=self.results['inconsistent'];self.assertEqual(a.capture.prepared.reconstructed.psd_result.status,'psd')
        self.assertEqual(a.linear.status,'inconsistent')
    def test_14_no_live_or_lean_claim(self):
        for a in self.results.values():
            self.assertFalse(a.report['lean_checked']);self.assertFalse(a.report['live_capture_performed'])
            self.assertEqual(a.report['producer_claim']['mode'],'simulated_regression')
    def test_15_no_solution_not_general_infeasibility(self):
        self.assertIn('not a proof',self.results['inconsistent'].report['failure_scope'])
    def test_16_policy_can_reject_exact_valid_completion(self):
        d=self.case();d['numerical']['bound']='0.2531';a=comp.complete(d)
        self.assertIsNotNone(a.artifact);self.assertTrue(a.report['completed_diagnostic']['diagnostic_passed'])
        self.assertFalse(a.report['completion_accepted']);self.assertFalse(a.report['completed_policy_checks']['error_bounds'])
    def test_17_implicit_interpolation_not_discarded(self):
        a=self.results['one'].capture.prepared.reconstructed.artifact
        c=replace(a.upper,interp_terms=(gram.InterpTermSpec(Q(0),0,0),))
        with self.assertRaisesRegex(ValueError,'empty implicit'):comp.coefficient_system(replace(a,upper=c))
    def test_18_compiler_includes_two_gram_axes(self):
        a=self.results['one'].capture.prepared.reconstructed.artifact;s=comp.coefficient_system(a)
        m=len(a.upper.dual_matrix);p=len(a.upper.objective.value_coeff);G=[list(r) for r in a.upper.dual_matrix];G[0][1]+=Q(1,10000)
        ss=comp.coefficient_system(replace(a,upper=replace(a.upper,dual_matrix=tuple(map(tuple,G)))))
        self.assertEqual(ss.rhs[1+p+1]-s.rhs[1+p+1],Q(1,10000))
        self.assertEqual(ss.rhs[1+p+m],s.rhs[1+p+m]);self.assertEqual(ss.matrix,s.matrix)
    def test_19_bad_source_not_repaired(self):
        d=self.case();d['constraints'][0]['expression']['const']={'num':123,'den':1}
        a=comp.complete(d);self.assertFalse(a.report['completion_accepted'])
    def test_20_nonfinite_input_refused(self):
        d=self.case();d['numerical']['bound']='NaN'
        with self.assertRaises(ValueError):comp.complete(d)
    def test_21_horizon_checked(self):
        with self.assertRaises(ValueError):comp.complete(self.case(),3)
    def test_22_prepared_only_refused(self):
        d=self.case();d['numerical']=None;d['producer']['mode']='prepared_only'
        with self.assertRaisesRegex(ValueError,'no numerical'):comp.complete(d)
    def test_23_row_and_weights_permute_together(self):
        d=self.case('two');d['constraints'].reverse();d['numerical']['multipliers'].reverse()
        a=comp.complete(d);self.assertTrue(a.report['completion_accepted'])
        self.assertEqual([t.weight for t in a.artifact.upper.assumption_terms],
            list(reversed([t.weight for t in self.results['two'].artifact.upper.assumption_terms])))
    def test_24_factor_modification_detected(self):
        a=self.results['one'];u=replace(a.artifact.upper,dual_factor=gram.FactorCertSpec(()))
        self.assertFalse(comp.fixed_targets(a.capture.prepared.reconstructed.artifact.upper,u)['factors'])
    def test_25_reference_modification_detected(self):
        a=self.results['one'];u=a.artifact.upper;c=replace(u,assumption_terms=u.assumption_terms+(u.assumption_terms[0],))
        self.assertFalse(comp.fixed_targets(u,c)['references'])
    def test_26_replay_has_no_rate_lookup(self):
        s=comp.render_replay(self.results['three'],'LeanPEP.Imported.Example')
        self.assertTrue(s.startswith('import LeanPEP\n'));self.assertIn('completedUpperQ.bound',s)
        self.assertIn('decide +kernel',s);self.assertIn('#print axioms actual_upper',s)
        self.assertNotIn('sorry',s);self.assertNotIn('native_decide',s)
    def test_27_failure_replay_no_upper(self):
        s=comp.render_replay(self.results['inconsistent'],'LeanPEP.Imported.Example')
        self.assertIn('no_solution',s);self.assertNotIn('theorem actual_upper',s)
    def test_28_outputs_record_raw_seed_and_final(self):
        out=comp.outputs(self.results['one'],Path('/not-written'),'LeanPEP.Imported.Example')
        self.assertTrue({'raw_exact.json','seed_exact.json','completed_exact.json','linear_system.json','Replay.lean'} <= {p.name for p in out})
    def test_29_regeneration_deterministic(self):
        out=regen.generate()
        for path,text in out.items():self.assertEqual(path.read_text(),text)
    def test_30_no_formula_imports(self):
        s=(ROOT/'tools/complete_pepit_proximal_gradient_capture.py').read_text()
        for name in ('regenerate_', 'gdUpperCert', 'upperCertQ', 'generate_proximal_gradient_certificate'):
            self.assertNotIn(name,s)
    def test_31_existing_d9_success_unchanged(self):
        a=comp.complete(gram.load_json(ROOT/'data/fixtures/pepit_capture/pg_one.json'))
        self.assertTrue(a.report['completion_accepted']);self.assertEqual(a.report['changed_seed_entries'],0)
    def test_32_cli_success_and_exit(self):
        with tempfile.TemporaryDirectory() as td:
            r=subprocess.run([sys.executable,str(ROOT/'tools/complete_pepit_proximal_gradient_capture.py'),
                str(ROOT/'data/fixtures/pepit_completion/pg_two.json'),'--output-dir',td,'--namespace','LeanPEP.Imported.Temp',
                '--require-completed-pass'],capture_output=True,text=True)
            self.assertEqual(r.returncode,0,r.stderr);self.assertTrue(json.loads((Path(td)/'completion_report.json').read_text())['completion_accepted'])
    def test_33_cli_failure_retains_evidence(self):
        with tempfile.TemporaryDirectory() as td:
            r=subprocess.run([sys.executable,str(ROOT/'tools/complete_pepit_proximal_gradient_capture.py'),
                str(ROOT/'data/fixtures/pepit_completion/pg_inconsistent.json'),'--output-dir',td,'--namespace','LeanPEP.Imported.Temp',
                '--require-completed-pass'],capture_output=True,text=True)
            self.assertEqual(r.returncode,2,r.stderr);self.assertTrue((Path(td)/'linear_system.json').exists())
            self.assertFalse((Path(td)/'completed_exact.json').exists())
    def test_34_namespace_injection_refused(self):
        with self.assertRaises(ValueError):comp.render_module(self.results['one'],'X\naxiom bad : False')
    def test_35_final_policy_not_composed_error_budgets(self):
        a=self.results['one'];p=replace(a.capture.prepared.policy,max_denominator=100000,max_abs_error=Q(2,10000))
        final=a.artifact.upper;raw=replace(final,bound=final.bound+Q(3,10000));seed=replace(final,bound=final.bound+Q(15,100000))
        self.assertTrue(all(prep.changes_diagnostic(p,raw,seed).values()))
        self.assertTrue(all(prep.changes_diagnostic(p,seed,final).values()))
        self.assertFalse(prep.changes_diagnostic(p,raw,final)['error_bounds'])
    def test_36_compiler_sizes(self):
        for w,rc in [('one',(43,11)),('two',(73,21)),('three',(111,35))]:
            a=self.results[w];self.assertEqual((len(a.system.rhs),a.system.columns),rc)
    def test_37_no_seed_nearest_claim(self):
        self.assertFalse(self.results['one'].report['nearest_solution_claimed'])
    def test_38_completed_denominator_enforced(self):
        a=self.results['one'];u=a.artifact.upper;p=a.capture.prepared.policy
        final=replace(u,bound=Q(1,p.max_denominator+1))
        self.assertFalse(prep.changes_diagnostic(p,u,final)['denominator_bounds'])

    def test_39_nonempty_output_refused_without_deletion(self):
        with tempfile.TemporaryDirectory() as td:
            stale=Path(td)/'completed_exact.json';stale.write_text('old')
            r=subprocess.run([sys.executable,str(ROOT/'tools/complete_pepit_proximal_gradient_capture.py'),
                str(ROOT/'data/fixtures/pepit_completion/pg_inconsistent.json'),'--output-dir',td,
                '--namespace','LeanPEP.Imported.Temp'],capture_output=True,text=True)
            self.assertEqual(r.returncode,1);self.assertEqual(stale.read_text(),'old')
            self.assertIn('must be empty',r.stderr)

if __name__=='__main__':unittest.main()
