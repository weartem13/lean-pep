"""D7 exact finite diagnostics, not a substitute for Lean elaboration."""
from __future__ import annotations
from dataclasses import replace
from fractions import Fraction as Q
import copy
import itertools
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import import_exact_gram_bundle as gram
import import_proximal_gradient_source as centered
import import_proximal_gradient_coordinates as native
import import_proximal_gradient_rows as rows
import import_proximal_gradient_performance as perf
import import_proximal_gradient_sparse as sparse
import regenerate_proximal_gradient_sparse as regen

ROOT=Path(__file__).resolve().parents[2]


def evaluate(e,values,G):
    return e.const+sum((a*b for a,b in zip(e.value_coeff,values)),Q(0))+sum(
        (e.gram_coeff[i][j]*G[i][j] for i in range(len(G)) for j in range(len(G))),Q(0))


def delete_row(a,delete):
    """Deliberate mutation helper: unlike fixture creator permits invalid omissions."""
    keep=tuple(i for i in range(len(a.compact_rows)) if i!=delete)
    forward=tuple(a.coverage.to_full[i] for i in keep)
    back=[None]*len(a.coverage.from_full)
    for i,j in enumerate(forward): back[j]=i
    c=replace(a.upper,assumption_terms=tuple(replace(t,index=t.index-(t.index>delete))
        for t in a.upper.assumption_terms if t.index!=delete))
    return replace(a,coverage=sparse.Coverage(forward,tuple(back)),compact_rows=tuple(a.compact_rows[i] for i in keep),
        compact_rules=tuple(a.compact_rules[i] for i in keep),compact_labels=tuple(a.compact_labels[i] for i in keep),upper=c)


class SparseTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data={w:sparse.parse_artifact(gram.load_json(ROOT/f'data/fixtures/composite_sparse/pg_{w}.json'))
            for w in ('one','two','three','all')}
        cls.diags={w:sparse.diagnose(a) for w,a in cls.data.items()}

    def test_positive_fixtures(self):
        for d in self.diags.values():
            self.assertTrue(d['diagnostic_passed']); self.assertFalse(d['lean_checked'])
            self.assertFalse(d['live_capture_performed']); self.assertFalse(d['provenance_authenticated'])

    def test_exact_row_counts(self):
        for w,T in [('one',1),('two',2),('three',3)]:
            d=self.diags[w]
            self.assertEqual(d['full_row_count'],(T+2)**2+(T+1)**2+2)
            self.assertEqual(d['compact_row_count'],(T+2)*(T+1)+(T+1)*T+2)
            self.assertEqual(len(d['coverage']['omitted_full_indices']),2*T+3)

    def test_all_rows_compatibility(self):
        a=self.data['all']; self.assertEqual(a.coverage.to_full,tuple(range(15)))
        self.assertEqual(a.coverage.from_full,tuple(range(15)))
        self.assertFalse(self.diags['all']['coverage']['omitted_full_indices'])

    def test_auxiliary_position_moves(self):
        for w in ('one','two','three'):
            a=self.data[w]; self.assertNotEqual(a.coverage.to_full[0],0)
            self.assertEqual(a.coverage.to_full[-1],0)
            self.assertEqual(a.compact_labels[-1],{'kind':'performance'})

    def test_empty_coverage_generic(self):
        self.assertTrue(sparse.Coverage((),()).valid())
        self.assertTrue(sparse.Coverage((),(None,None)).valid())
        self.assertFalse(sparse.Coverage((),(0,)).valid())

    def test_all_small_partial_injections(self):
        for r in range(6):
            for k in range(r+1):
                for forward in itertools.permutations(range(r),k):
                    back=[None]*r
                    for i,j in enumerate(forward): back[j]=i
                    a=sparse.Coverage(forward,tuple(back))
                    self.assertTrue(a.valid())
                    self.assertEqual({j for j,i in enumerate(back) if i is None},set(range(r))-set(forward))

    def test_duplicate_mapping_rejected(self):
        a=self.data['one']; f=list(a.coverage.to_full); f[1]=f[0]
        b=replace(a,coverage=replace(a.coverage,to_full=tuple(f)))
        self.assertFalse(sparse.coverage_diagnostic(b)['guards']['partial_inverse'])

    def test_bad_partial_inverse_completed_passes(self):
        a=self.data['one']; b=list(a.coverage.from_full); b[2]=0
        a=replace(a,coverage=replace(a.coverage,from_full=tuple(b)))
        d=sparse.diagnose(a)
        self.assertTrue(d['bound_guards']['full_bound']); self.assertFalse(d['diagnostic_passed'])

    def test_omitted_zero_indices_are_not_guessed(self):
        a=self.data['one']; back=list(a.coverage.from_full); back[a.coverage.to_full[0]]=None
        b=replace(a,coverage=replace(a.coverage,from_full=tuple(back)))
        self.assertFalse(sparse.coverage_diagnostic(b)['passed'])

    def test_unused_nonzero_row_cannot_disappear(self):
        a=delete_row(self.data['one'],0); d=sparse.diagnose(a)
        self.assertTrue(d['compact_certificate']['accepted'])
        self.assertTrue(d['bound_guards']['full_bound'])
        self.assertFalse(d['coverage']['guards']['omitted_rows_zero'])
        self.assertFalse(d['diagnostic_passed'])

    def test_zero_weight_does_not_authorize_omission(self):
        a=self.data['one']; a=replace(a,upper=replace(a.upper,assumption_terms=
            a.upper.assumption_terms+(gram.AssumptionTermSpec(Q(0),0),)))
        self.assertTrue(sparse.diagnose(a)['diagnostic_passed'])
        self.assertFalse(sparse.diagnose(delete_row(a,0))['diagnostic_passed'])

    def test_performance_row_not_omittable(self):
        a=self.data['one']; i=a.coverage.from_full[0]
        d=sparse.coverage_diagnostic(delete_row(a,i))
        self.assertIn(0,d['nonzero_omitted_indices'])
        full=sparse.expected_rows(a.base,a.performance_rule)[0]
        self.assertTrue(sparse.is_zero(perf.substitute(a.base.ordered.payload.source.objective,full)))
        self.assertFalse(sparse.is_zero(full))

    def test_radius_row_not_omittable(self):
        a=self.data['one']; i=next(i for i,t in enumerate(a.compact_labels) if t.get('tag',{}).get('kind')=='radius')
        self.assertFalse(sparse.coverage_diagnostic(delete_row(a,i))['guards']['omitted_rows_zero'])

    def test_zero_at_witness_not_zero_polynomial(self):
        a=self.data['one']; e=a.compact_rows[0]
        p,m=len(e.value_coeff),len(e.gram_coeff)
        self.assertEqual(evaluate(e,[Q(0)]*p,[[Q(0)]*m for _ in range(m)]),0)
        self.assertFalse(sparse.is_zero(e))

    def test_skew_and_tiny_coefficients_not_discarded(self):
        e=gram.LinearExprSpec(Q(0),(),((Q(0),Q(1)),(Q(-1),Q(0))))
        self.assertEqual(evaluate(e,[],[[Q(2),Q(3)],[Q(3),Q(7)]]),0)
        self.assertFalse(sparse.is_zero(e))
        self.assertFalse(sparse.is_zero(replace(centered.zero(0,0),const=Q(1,10**100))))

    def test_bad_zero_labels_rejected(self):
        a=self.data['all']; tags=list(a.compact_labels); tags[1],tags[5]=tags[5],tags[1]
        b=replace(a,compact_labels=tuple(tags)); d=sparse.coverage_diagnostic(b)
        self.assertTrue(d['guards']['retained_rows']); self.assertFalse(d['guards']['retained_labels'])

    def test_zero_row_sense_still_checked(self):
        a=self.data['all']; rr=list(a.compact_rules); rr[1]=replace(rr[1],sense='leZero')
        b=replace(a,compact_rules=tuple(rr)); d=sparse.diagnose(b)
        self.assertTrue(d['compact_certificate']['accepted']); self.assertFalse(d['source_passed'])

    def test_hidden_tau_detected_before_substitution(self):
        a=self.data['one']; es=list(a.compact_rows); o=a.base.ordered.payload.source.objective
        es[0]=centered.add(es[0],perf.link(o)); b=replace(a,compact_rows=tuple(es))
        self.assertEqual(perf.substitute(o,b.compact_rows[0]),perf.substitute(o,a.compact_rows[0]))
        self.assertFalse(sparse.coverage_diagnostic(b)['guards']['retained_rows'])

    def test_all_terms_weights_factors_preserved(self):
        for a in self.data.values():
            b=sparse.completed_artifact(a)
            self.assertEqual(len(a.upper.assumption_terms),len(b.upper.assumption_terms))
            self.assertEqual([t.weight for t in a.upper.assumption_terms],[t.weight for t in b.upper.assumption_terms])
            for key in ('bound','objective','dual_matrix','dual_factor','interp_terms'):
                self.assertEqual(getattr(a.upper,key),getattr(b.upper,key))

    def test_repeated_and_zero_references_preserved(self):
        a=self.data['two']; c=a.upper
        a=replace(a,upper=replace(c,assumption_terms=c.assumption_terms+(gram.AssumptionTermSpec(Q(0),0),)))
        b=sparse.completed_artifact(a)
        self.assertEqual(sum(t.index==0 for t in b.upper.assumption_terms),2)
        self.assertEqual(b.upper.assumption_terms[-1].weight,0)
        self.assertTrue(sparse.diagnose(a)['diagnostic_passed'])

    def test_performance_mass_after_mapping(self):
        for d in self.diags.values(): self.assertTrue(d['completed_diagnostic']['performance_mass_is_one'])

    def test_full_assumption_sum_equality(self):
        for a in self.data.values():
            x=perf._sum(sparse.compact_snapshot(a),a.upper)
            b=sparse.completed_artifact(a); y=perf._sum(perf.oriented_snapshot(b),b.upper)
            self.assertEqual(x,y)

    def test_arbitrary_real_data_row_evaluation(self):
        for a in self.data.values():
            b=sparse.completed_artifact(a)
            compact=sparse.compact_snapshot(a).constraints; full=perf.oriented_snapshot(b).constraints
            p,m=len(a.objective.value_coeff),len(a.objective.gram_coeff)
            for seed in range(3):
                v=[Q(3*i-seed,7) for i in range(p)]
                G=[[Q(i-2*j+seed,11) for j in range(m)] for i in range(m)]
                for i,j in enumerate(a.coverage.to_full): self.assertEqual(evaluate(compact[i],v,G),evaluate(full[j],v,G))
                for j,i in enumerate(a.coverage.from_full):
                    if i is None: self.assertEqual(evaluate(full[j],v,G),0)

    def test_implicit_zero_term_rejected_not_removed(self):
        a=self.data['one']; raw=sparse.artifact_tree(a)
        raw['upper']['interp_terms']=[dict(weight=dict(num=0,den=1),i=0,j=1)]
        b=sparse.parse_artifact(raw); d=sparse.diagnose(b)
        self.assertTrue(d['compact_certificate']['accepted']); self.assertFalse(d['diagnostic_passed'])
        self.assertEqual(sparse.completed_artifact(b).upper.interp_terms,b.upper.interp_terms)

    def test_bound_is_never_replaced(self):
        a=self.data['one']; b=replace(a,upper=replace(a.upper,bound=Q(0)))
        self.assertEqual(sparse.completed_artifact(b).upper.bound,0)
        self.assertFalse(sparse.diagnose(b)['diagnostic_passed'])

    def test_no_preaccepted_full_upper_input(self):
        raw=sparse.artifact_tree(self.data['one']); self.assertNotIn('upper',raw['base_source'])
        raw['base_source']['upper']=raw['upper']
        with self.assertRaises(ValueError): sparse.parse_artifact(raw)

    def test_template_binding_not_trusted(self):
        raw=sparse.artifact_tree(self.data['all'])
        raw['base_source']['source']['header']['step_size']={'num':2,'den':1}
        d=sparse.diagnose(sparse.parse_artifact(raw)); self.assertFalse(d['source_passed'])

    def test_roundtrip_exact_json(self):
        for a in self.data.values():
            raw=sparse.artifact_tree(a)
            self.assertEqual(sparse.artifact_tree(sparse.parse_artifact(raw)),raw)

    def test_bad_array_lengths_rejected(self):
        for field in ('rows','row_rules','row_labels'):
            raw=sparse.artifact_tree(self.data['one']); raw[field]=raw[field][:-1]
            with self.assertRaises(ValueError): sparse.parse_artifact(raw)
        for field in ('to_full','from_full'):
            raw=sparse.artifact_tree(self.data['one']); raw['coverage'][field]=raw['coverage'][field][:-1]
            with self.assertRaises(ValueError): sparse.parse_artifact(raw)

    def test_noninteger_out_of_range_indices_rejected(self):
        for field,values in [('to_full',[-1,15,True,1.0]),('from_full',[-1,10,False,1.0])]:
            for value in values:
                raw=sparse.artifact_tree(self.data['one']); raw['coverage'][field][0]=value
                with self.assertRaises(ValueError): sparse.parse_artifact(raw)

    def test_float_and_decimal_string_coefficients_rejected(self):
        for value in (0.0,'0.0'):
            raw=sparse.artifact_tree(self.data['one']); raw['rows'][0]['const']=value
            with self.assertRaises(ValueError): sparse.parse_artifact(raw)

    def test_unknown_fields_and_namespace_rejected(self):
        raw=sparse.artifact_tree(self.data['one']); raw['repair_missing_rows']=True
        with self.assertRaises(ValueError): sparse.parse_artifact(raw)
        with self.assertRaises(ValueError): sparse.render_module(self.data['one'],'Bad; axiom boom : False')

    def test_wrong_horizon_rejected(self):
        with self.assertRaises(ValueError): sparse.parse_artifact(sparse.artifact_tree(self.data['one']),2)

    def test_generated_modules_data_only(self):
        text=sparse.render_module(self.data['one'],'LeanPEP.Imported.TestSparse')
        self.assertNotRegex(text,r'(?m)^\s*theorem\s'); self.assertNotIn('sorry',text)
        self.assertNotIn('native_decide',text)
        self.assertEqual(text.count('def upperQ :'),1)
        self.assertIn('SourceQ 0 10',text)

    def test_regeneration_matches_committed_files(self):
        for path,text in regen.generate().items(): self.assertEqual(path.read_text(),text)

    def test_fixture_constructor_refuses_nonzero_removal(self):
        a=sparse.completed_artifact(self.data['one'])
        with self.assertRaises(ValueError): regen.compact(a,tuple(range(1,len(a.extended_rows))))

    def test_partial_zero_retention(self):
        a=sparse.completed_artifact(self.data['all'])
        b=regen.compact(a,tuple(i for i in range(len(a.extended_rows)) if i!=1))
        self.assertTrue(sparse.diagnose(b)['diagnostic_passed'])
        self.assertEqual(len(b.compact_rows),14)

    def test_cli_good_export(self):
        with tempfile.TemporaryDirectory() as td:
            p=Path(td)
            args=[sys.executable,str(ROOT/'tools/import_proximal_gradient_sparse.py'),
                str(ROOT/'data/fixtures/composite_sparse/pg_one.json'),'--expected-steps','1',
                '--lean',str(p/'out.lean'),'--report',str(p/'report.json'),'--namespace','LeanPEP.Imported.TestSparse',
                '--completed-json',str(p/'full.json'),'--require-diagnostic-pass']
            proc=subprocess.run(args,capture_output=True,text=True)
            self.assertEqual(proc.returncode,0,proc.stderr)
            self.assertTrue(perf.diagnose(perf.parse_artifact(gram.load_json(p/'full.json')))['diagnostic_passed'])
            self.assertFalse(json.loads((p/'report.json').read_text())['lean_checked'])

    def test_cli_bad_coverage_cannot_be_laundered(self):
        with tempfile.TemporaryDirectory() as td:
            p=Path(td); a=delete_row(self.data['one'],0)
            (p/'bad.json').write_text(json.dumps(sparse.artifact_tree(a)))
            cmd=[sys.executable,str(ROOT/'tools/import_proximal_gradient_sparse.py'),str(p/'bad.json'),
                '--lean',str(p/'bad.lean'),'--report',str(p/'bad_report.json'),'--namespace','LeanPEP.Imported.TestBad']
            raw=subprocess.run(cmd,capture_output=True,text=True)
            self.assertEqual(raw.returncode,0,raw.stderr)
            self.assertFalse(json.loads((p/'bad_report.json').read_text())['diagnostic_passed'])
            bad=subprocess.run(cmd+['--completed-json',str(p/'laundered.json')],capture_output=True,text=True)
            self.assertNotEqual(bad.returncode,0); self.assertFalse((p/'laundered.json').exists())

    def test_cli_duplicate_keys_and_path_alias_rejected(self):
        with tempfile.TemporaryDirectory() as td:
            p=Path(td); (p/'bad.json').write_text('{"format":1,"format":2}')
            cmd=[sys.executable,str(ROOT/'tools/import_proximal_gradient_sparse.py'),str(p/'bad.json'),
                '--lean',str(p/'out.lean'),'--report',str(p/'out.json'),'--namespace','LeanPEP.Imported.TestBad']
            self.assertNotEqual(subprocess.run(cmd,capture_output=True).returncode,0)
            cmd[cmd.index('--lean')+1]=str(p/'bad.json')
            self.assertNotEqual(subprocess.run(cmd,capture_output=True).returncode,0)

if __name__=='__main__': unittest.main()
