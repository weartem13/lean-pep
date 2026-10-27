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
from unittest.mock import patch

import import_exact_gram_bundle as gram
import import_proximal_gradient_sparse as sparse
import prepare_proximal_gradient_candidates as prep
import synthesize_psd_factors as psd

ROOT=Path(__file__).resolve().parents[2]

class CandidateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.inputs={w:gram.load_json(ROOT/f'data/fixtures/composite_candidates/pg_{w}.json') for w in ('one','two','three','exact')}
        cls.prepared={w:prep.prepare(x) for w,x in cls.inputs.items()}

    def inp(self,word='one'):
        return copy.deepcopy(self.inputs[word])

    def test_positive_reconstructed_all(self):
        for p in self.prepared.values(): self.assertTrue(p.report['reconstructed_joint_accepted_diagnostic'])

    def test_raw_exact_passes(self):
        self.assertTrue(self.prepared['exact'].report['raw_accepted_diagnostic'])

    def test_raw_decimal_truncations_rejected(self):
        for w in ('one','two','three'): self.assertFalse(self.prepared[w].report['raw_accepted_diagnostic'])

    def test_raw_psd_not_sufficient(self):
        for w in ('one','two'):
            d=self.prepared[w].raw.diagnostic['compact_certificate']
            self.assertTrue(d['factor']); self.assertFalse(d['identity'])

    def test_negative_raw_matrix_has_original_witness(self):
        p=self.prepared['three']; r=p.raw.psd_result
        self.assertEqual(r.status,'negative')
        self.assertTrue(psd.verify_result(p.raw.artifact.upper.dual_matrix,r))
        self.assertEqual(r.quadratic_value,Q(-1,83333333325))

    def test_reconstructed_factors_exact(self):
        for p in self.prepared.values():
            r=p.reconstructed.psd_result
            self.assertEqual(r.status,'psd')
            self.assertEqual(psd.reconstruct(r.dimension,r.factors),p.reconstructed.artifact.upper.dual_matrix)

    def test_no_source_mutation(self):
        for p in self.prepared.values():
            self.assertEqual(prep.source_tree(p.raw.artifact),p.source)
            self.assertEqual(prep.source_tree(p.reconstructed.artifact),p.source)

    def test_input_not_mutated(self):
        x=self.inp(); y=copy.deepcopy(x); prep.prepare(x); self.assertEqual(x,y)

    def test_reference_order_and_counts(self):
        for p in self.prepared.values():
            a=p.raw.artifact.upper; b=p.reconstructed.artifact.upper
            self.assertEqual([t.index for t in a.assumption_terms],[t.index for t in b.assumption_terms])
            self.assertEqual([(t.i,t.j) for t in a.interp_terms],[(t.i,t.j) for t in b.interp_terms])

    def test_split_performance_references_retained(self):
        a=self.prepared['two'].raw.artifact
        indices=[t.index for t in a.upper.assumption_terms]
        self.assertGreater(len(indices),len(set(indices)))

    def test_every_numeric_field_in_report(self):
        for p in self.prepared.values():
            self.assertEqual(tuple(e.raw for e in p.entries),prep.numerical_coefficients(p.raw.artifact.upper))
            self.assertEqual(tuple(e.reconstructed for e in p.entries),prep.numerical_coefficients(p.reconstructed.artifact.upper))

    def test_every_delta_exact(self):
        for p in self.prepared.values():
            for e,r in zip(p.entries,p.report['entries']):
                self.assertEqual(Q(r['delta']['num'],r['delta']['den']),e.reconstructed-e.raw)
                self.assertEqual(Q(r['absolute_error']['num'],r['absolute_error']['den']),abs(e.reconstructed-e.raw))

    def test_denominator_cap_all(self):
        for p in self.prepared.values():
            self.assertTrue(all(e.reconstructed.denominator<=p.policy.max_denominator for e in p.entries))

    def test_nonbinary_decimal_raw(self):
        _,q=prep.decimal('0.1','x')
        self.assertEqual(q,Q(1,10)); self.assertNotEqual(q,Q(0.1))

    def test_scientific_and_signed_zero(self):
        for text,q in [('1.25e-3',Q(1,800)),('-0.000',Q(0)),('+2e2',Q(200)),('.5',Q(1,2))]:
            self.assertEqual(prep.decimal(text,'x')[1],q)

    def test_invalid_numbers_rejected(self):
        for bad in [0,0.1,True,None,'NaN','Infinity','1/3',' 0.5','1.0 ', '1_000', {},[]]:
            with self.subTest(bad=bad),self.assertRaises(ValueError): prep.decimal(bad,'x')

    def test_huge_decimal_limits(self):
        for bad in ['1e10000000','1e-10000000','1'*5000]:
            with self.assertRaises(ValueError): prep.decimal(bad,'x')

    def test_policy_failure_preserves_raw_candidate(self):
        x=self.inp(); x['policy']['max_abs_error']='0'
        p=prep.prepare(x)
        self.assertFalse(p.report['reconstruction_policy_passed'])
        self.assertTrue(p.report['reconstructed_exact_accepted_diagnostic'])
        self.assertFalse(p.report['reconstructed_joint_accepted_diagnostic'])
        self.assertEqual(p.raw.artifact.upper,self.prepared['one'].raw.artifact.upper)

    def test_small_denominator_can_fail(self):
        x=self.inp(); x['policy'].update(max_denominator=1,max_abs_error='10')
        p=prep.prepare(x)
        self.assertTrue(p.report['reconstruction_policy_passed'])
        self.assertFalse(p.report['reconstructed_joint_accepted_diagnostic'])

    def test_invalid_policy_rejected(self):
        for field,value in [('method','known_formula'),('max_denominator',0),('max_denominator',True),('max_abs_error','-1')]:
            x=self.inp(); x['policy'][field]=value
            with self.assertRaises(ValueError): prep.prepare(x)

    def test_wrong_bound_not_overwritten(self):
        x=self.inp(); x['upper']['bound']='0.125'
        p=prep.prepare(x)
        self.assertEqual(p.reconstructed.artifact.upper.bound,Q(1,8))
        self.assertFalse(p.report['reconstructed_joint_accepted_diagnostic'])

    def test_within_policy_does_not_imply_identity(self):
        x=self.inp(); x['policy'].update(max_denominator=10**12,max_abs_error='0.0000000001')
        x['upper']['bound']='0.250000000001'
        p=prep.prepare(x)
        self.assertTrue(p.report['reconstruction_policy_passed'])
        self.assertFalse(p.report['reconstructed_exact_accepted_diagnostic'])

    def test_matrix_not_recomputed_from_weights(self):
        x=self.inp(); x['upper']['dual_matrix'][0][0]='7'
        p=prep.prepare(x)
        self.assertEqual(p.raw.artifact.upper.dual_matrix[0][0],7)
        self.assertEqual(p.reconstructed.artifact.upper.dual_matrix[0][0],7)
        self.assertFalse(p.report['reconstructed_joint_accepted_diagnostic'])

    def test_asymmetry_not_silently_averaged(self):
        x=self.inp(); x['upper']['dual_matrix'][0][1]='7'
        p=prep.prepare(x)
        self.assertEqual(p.raw.psd_result.status,'asymmetric')
        self.assertEqual(p.reconstructed.psd_result.status,'asymmetric')
        self.assertEqual(p.reconstructed.artifact.upper.dual_matrix[0][1],7)
        self.assertNotEqual(p.reconstructed.artifact.upper.dual_matrix[1][0],7)

    def test_tiny_asymmetry_reported_per_track(self):
        x=self.inp(); q=Q(x['upper']['dual_matrix'][0][1])+Q(1,10**12)
        from regenerate_proximal_gradient_candidates import decimal_trunc
        x['upper']['dual_matrix'][0][1]=decimal_trunc({'num':q.numerator,'den':q.denominator})
        p=prep.prepare(x)
        self.assertEqual(p.raw.psd_result.status,'asymmetric')
        self.assertEqual(p.reconstructed.psd_result.status,'psd')
        self.assertTrue(p.report['reconstructed_joint_accepted_diagnostic'])

    def test_negative_target_not_fixed(self):
        x=self.inp(); x['upper']['dual_matrix'][0][0]='-1'
        p=prep.prepare(x)
        self.assertEqual(p.reconstructed.psd_result.status,'negative')
        self.assertEqual(p.reconstructed.artifact.upper.dual_matrix[0][0],-1)
        self.assertEqual(p.reconstructed.artifact.upper.dual_factor.factors,())

    def test_negative_weight_not_clipped(self):
        x=self.inp(); x['upper']['assumption_terms'][0]['weight']='-1'
        p=prep.prepare(x)
        self.assertEqual(p.reconstructed.artifact.upper.assumption_terms[0].weight,-1)
        self.assertFalse(p.report['reconstructed_joint_accepted_diagnostic'])

    def test_wrong_reference_not_repaired(self):
        x=self.inp(); x['upper']['assumption_terms'][0]['index']=0
        p=prep.prepare(x)
        self.assertEqual(p.reconstructed.artifact.upper.assumption_terms[0].index,0)
        self.assertFalse(p.report['reconstructed_joint_accepted_diagnostic'])

    def test_out_of_range_reference_rejected(self):
        x=self.inp(); x['upper']['assumption_terms'][0]['index']=1000
        with self.assertRaises(ValueError): prep.prepare(x)

    def test_zero_weight_preserved(self):
        x=self.inp(); x['upper']['assumption_terms'].append({'index':0,'weight':'0'})
        p=prep.prepare(x)
        self.assertEqual(len(p.raw.artifact.upper.assumption_terms),7)
        self.assertEqual(p.reconstructed.artifact.upper.assumption_terms[-1].weight,0)
        self.assertTrue(p.report['reconstructed_joint_accepted_diagnostic'])

    def test_implicit_zero_term_still_rejected(self):
        x=self.inp(); x['upper']['interp_terms']=[dict(i=0,j=1,weight='0')]
        p=prep.prepare(x)
        self.assertEqual(len(p.reconstructed.artifact.upper.interp_terms),1)
        self.assertFalse(p.report['reconstructed_joint_accepted_diagnostic'])

    def test_wrong_source_scale_not_reconstructed(self):
        x=self.inp(); x['source']['performance_rule']['scale']={'num':2,'den':3}
        # Default is 2/3, so use a close but DISTINCT exact scale.
        x['source']['performance_rule']['scale']={'num':2000000000001,'den':3000000000000}
        p=prep.prepare(x)
        self.assertEqual(gram.parse_rational(p.source['performance_rule']['scale'],'x'),
            gram.parse_rational(x['source']['performance_rule']['scale'],'x'))
        self.assertFalse(p.report['reconstructed_joint_accepted_diagnostic'])

    def test_wrong_coverage_not_reconstructed(self):
        x=self.inp(); x['source']['coverage']['from_full']=[None]*len(x['source']['coverage']['from_full'])
        p=prep.prepare(x)
        self.assertFalse(p.report['reconstructed_joint_accepted_diagnostic'])
        self.assertTrue(p.reconstructed.diagnostic['compact_certificate']['accepted'])

    def test_objective_not_replaced(self):
        x=self.inp(); x['upper']['objective']['value_coeff'][0]='0'
        p=prep.prepare(x)
        self.assertEqual(p.reconstructed.artifact.upper.objective.value_coeff[0],0)
        self.assertFalse(p.report['reconstructed_joint_accepted_diagnostic'])

    def test_extra_exact_upper_rejected(self):
        x=self.inp(); x['source']['upper']={}
        with self.assertRaises(ValueError): prep.prepare(x)

    def test_unknown_keys_rejected(self):
        for parent,key in [('', 'unexpected'),('upper','dual_factor'),('policy','snap_zero')]:
            x=self.inp(); (x if not parent else x[parent])[key]=0
            with self.assertRaises(ValueError): prep.prepare(x)

    def test_dimensions_rejected(self):
        x=self.inp(); x['upper']['dual_matrix'][0].pop()
        with self.assertRaises(ValueError): prep.prepare(x)

    def test_expected_horizon_enforced(self):
        with self.assertRaises(ValueError): prep.prepare(self.inp(),2)

    def test_duplicate_json_keys_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'bad.json';p.write_text('{"format":1,"format":2}')
            with self.assertRaises(ValueError): gram.load_json(p)

    def test_policy_references_and_factors_independent(self):
        p=self.prepared['one']; a=p.raw.artifact.upper; b=p.reconstructed.artifact.upper
        empty=replace(b,dual_factor=gram.FactorCertSpec(()))
        self.assertTrue(all(prep.changes_diagnostic(p.policy,a,empty).values()))
        changed=replace(b,assumption_terms=b.assumption_terms+(gram.AssumptionTermSpec(Q(0),0),))
        self.assertFalse(prep.changes_diagnostic(p.policy,a,changed)['assumption_references'])

    def test_empty_lists_not_truncating_comparison(self):
        p=self.prepared['exact']; a=p.raw.artifact.upper
        b=replace(a,assumption_terms=())
        d=prep.changes_diagnostic(p.policy,a,b)
        self.assertFalse(d['coefficient_lengths']);self.assertFalse(d['assumption_references'])

    def test_renderer_single_source_two_uppers(self):
        p=self.prepared['three']; text=prep.render_module(p,'LeanPEP.Imported.Test.Three')
        self.assertEqual(text.count('def rawUpperQ :'),1)
        self.assertEqual(text.count('def reconstructedUpperQ :'),1)
        self.assertIn('def rawNegativeVecQ',text)
        self.assertNotIn('theorem',text.replace('No acceptance theorem is generated.',''))
        self.assertNotIn('native_decide',text)

    def test_invalid_namespace_rejected(self):
        with self.assertRaises(ValueError): prep.render_module(self.prepared['one'],'X\naxiom danger : False')

    def test_reports_disclaim_live_and_lean(self):
        for p in self.prepared.values():
            for key in ('lean_checked','live_capture_performed','provenance_authenticated','known_bound_used','matrix_repaired','source_reconstructed'):
                self.assertFalse(p.report[key])

    def test_no_expected_certificate_formula_called(self):
        import import_proximal_gradient_source as c
        # Diagnostics may use expected source coefficients, but synthesis cannot
        # obtain any expected upper bound/weights/matrix from a fixture creator.
        import regenerate_proximal_gradient_sparse as fixtures
        with patch.object(fixtures,'fixture',side_effect=AssertionError('known certificate lookup')):
            self.assertTrue(prep.prepare(self.inp()).report['reconstructed_joint_accepted_diagnostic'])

    def test_old_d7_parser_reads_both_outputs(self):
        for p in self.prepared.values():
            for t in (p.raw,p.reconstructed):
                a=sparse.parse_artifact(sparse.artifact_tree(t.artifact))
                self.assertEqual(a.upper,t.artifact.upper)

    def test_cli_writes_tracks(self):
        with tempfile.TemporaryDirectory() as d:
            cmd=[sys.executable,str(ROOT/'tools/prepare_proximal_gradient_candidates.py'),
                str(ROOT/'data/fixtures/composite_candidates/pg_one.json'),'--expected-steps','1',
                '--output-dir',d,'--namespace','LeanPEP.Imported.CLI.One','--require-reconstructed-pass']
            r=subprocess.run(cmd,text=True,capture_output=True,timeout=30)
            self.assertEqual(r.returncode,0,r.stderr)
            self.assertEqual({p.name for p in Path(d).iterdir()},
                {'Candidates.lean','report.json','source.json','raw_exact.json','reconstructed_exact.json'})

    def test_cli_budget_failure_keeps_diagnostics(self):
        with tempfile.TemporaryDirectory() as d:
            x=self.inp();x['policy']['max_abs_error']='0'
            inp=Path(d)/'input.json';inp.write_text(json.dumps(x))
            out=Path(d)/'out'
            r=subprocess.run([sys.executable,str(ROOT/'tools/prepare_proximal_gradient_candidates.py'),
                str(inp),'--output-dir',str(out),'--namespace','LeanPEP.Imported.CLI.Fail','--require-reconstructed-pass'],
                text=True,capture_output=True,timeout=30)
            self.assertEqual(r.returncode,2,r.stderr)
            self.assertFalse(json.loads((out/'report.json').read_text())['reconstruction_policy_passed'])

    def test_regeneration_matches(self):
        import regenerate_proximal_gradient_candidates as regen
        for path,text in regen.generate().items(): self.assertEqual(path.read_text(),text,str(path))

if __name__=='__main__': unittest.main()
