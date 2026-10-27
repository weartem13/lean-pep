"""Exact D6 regressions. Finite diagnostics, not a substitute for Lean checking."""
from __future__ import annotations
from dataclasses import replace
from fractions import Fraction as Q
import copy
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

import import_exact_gram_bundle as gram
import import_proximal_gradient_source as centered
import import_proximal_gradient_coordinates as native
import import_proximal_gradient_ordering as order
import import_proximal_gradient_rows as rows
import import_proximal_gradient_performance as perf
import regenerate_proximal_gradient_performance as regen

ROOT=Path(__file__).resolve().parents[2]


def evaluate(e,values,G):
    return e.const+sum((a*b for a,b in zip(e.value_coeff,values)),Q(0))+sum(
        (e.gram_coeff[i][j]*G[i][j] for i in range(len(G)) for j in range(len(G))),Q(0))


class PerformanceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data={w:perf.parse_artifact(gram.load_json(ROOT/f'data/fixtures/composite_performance/pg_{w}.json'))
            for w in ('one','two','three','unit')}
        cls.diags={w:perf.diagnose(a) for w,a in cls.data.items()}

    def test_all_fixtures(self):
        for d in self.diags.values():
            self.assertTrue(d['diagnostic_passed'])
            self.assertFalse(d['lean_checked'])
            self.assertFalse(d['live_capture_performed'])
            self.assertFalse(d['provenance_authenticated'])

    def test_dimensions_add_scalar_not_gram(self):
        for d in self.diags.values():
            x=d['dimensions']
            self.assertEqual(x['extended_values'],x['base_values']+1)
            self.assertEqual(x['extended_rows'],x['base_rows']+1)
            self.assertEqual(x['basis'],x['base_values']+1)

    def test_empty_dimensions(self):
        o=replace(centered.zero(0,0),const=Q(3,7))
        self.assertEqual(perf.substitute(o,perf.tau(0,0)),o)
        self.assertEqual(perf.substitute(o,perf.link(o)),centered.zero(0,0))

    def test_embed_inverse(self):
        for p in (0,1,3):
            for m in (0,1,3):
                o=gram.LinearExprSpec(Q(2,3),tuple(Q(i+1,7) for i in range(p)),
                    tuple(tuple(Q(i-2*j,5) for j in range(m)) for i in range(m)))
                self.assertEqual(perf.substitute(o,perf.embed(o)),o)

    def test_tau_substitution_not_zero(self):
        o=gram.LinearExprSpec(Q(5), (Q(2),Q(-1)), ((Q(7),Q(2)),(Q(-3),Q(4))))
        self.assertEqual(perf.substitute(o,perf.tau(2,2)),o)
        self.assertNotEqual(o,centered.zero(2,2))

    def test_link_substitutes_zero(self):
        for a in self.data.values():
            o=a.base.ordered.payload.source.objective
            self.assertEqual(perf.substitute(o,perf.link(o)),centered.zero(len(o.value_coeff),len(o.gram_coeff)))

    def test_full_nonsymmetric_evaluation(self):
        for p in (0,1,4):
            for m in (0,1,3):
                for t in (-3,0,2):
                    o=gram.LinearExprSpec(Q(1,3),tuple(Q(i-2,7) for i in range(p)),
                        tuple(tuple(Q(2*i-j,5) for j in range(m)) for i in range(m)))
                    e=gram.LinearExprSpec(Q(-2,5),(Q(t),)+tuple(Q(2*i-1,9) for i in range(p)),
                        tuple(tuple(Q(i+3*j-1,11) for j in range(m)) for i in range(m)))
                    vals=tuple(Q(i-1,3) for i in range(p))
                    G=tuple(tuple(Q(3*i-2*j+1,13) for j in range(m)) for i in range(m))
                    self.assertEqual(evaluate(perf.substitute(o,e),vals,G),
                        evaluate(e,(evaluate(o,vals,G),)+vals,G))

    def test_affine_substitution_linearity(self):
        o=gram.LinearExprSpec(Q(2), (Q(3),), ((Q(4),),))
        e=gram.LinearExprSpec(Q(5),(Q(6),Q(7)),((Q(8),),))
        f=gram.LinearExprSpec(Q(9),(Q(10),Q(11)),((Q(12),),))
        self.assertEqual(perf.substitute(o,centered.add(e,f)),centered.add(perf.substitute(o,e),perf.substitute(o,f)))
        self.assertEqual(perf.substitute(o,centered.scale(Q(-3,7),e)),centered.scale(Q(-3,7),perf.substitute(o,e)))

    def test_feasibility_link_direction(self):
        o=gram.LinearExprSpec(Q(1),(Q(-2),),((Q(3),),))
        vals=(Q(2),); G=((Q(1),),); F=evaluate(o,vals,G)
        for gamma in (Q(1,3),Q(1),Q(7,2)):
            for sense in ('geZero','leZero'):
                r=rows.Rule(sense,gamma)
                e=rows.orient(r,rows.encode(r,perf.link(o)))
                for t in (F-2,F,F+3):
                    self.assertEqual(evaluate(e,(t,)+vals,G)>=0,t<=F)

    def test_lowering_recovers_old_certificate(self):
        for w,a in self.data.items():
            old=rows.parse_artifact(gram.load_json(ROOT/f'data/fixtures/composite_rows/pg_{w}.json'))
            b=perf.eliminated_artifact(a)
            self.assertEqual(b.ordered.payload.source,old.ordered.payload.source)
            self.assertEqual(b.rules,old.rules)
            self.assertEqual(b.ordered.ordering,old.ordered.ordering)
            self.assertEqual(b.ordered.payload.upper,old.ordered.payload.upper)

    def test_gram_and_factors_unchanged(self):
        for a in self.data.values():
            c=perf.eliminated_artifact(a).ordered.payload.upper
            self.assertIs(c.dual_matrix,a.upper.dual_matrix)
            self.assertIs(c.dual_factor,a.upper.dual_factor)
            self.assertEqual(c.bound,a.upper.bound)

    def test_source_indices_shift_before_D5_D4(self):
        a=self.data['three']
        c=perf.eliminated_artifact(a).ordered.payload.upper
        original=tuple(t for t in a.upper.assumption_terms if t.index!=0)
        self.assertEqual(tuple(t.index+1 for t in c.assumption_terms),tuple(t.index for t in original))
        self.assertEqual(tuple(t.weight for t in c.assumption_terms),tuple(t.weight for t in original))

    def test_nonunit_performance_multiplier(self):
        a=self.data['one']; linkterms=[t for t in a.upper.assumption_terms if t.index==0]
        self.assertNotEqual(linkterms[0].weight,Q(1))
        self.assertEqual(linkterms[0].weight*a.performance_rule.scale,Q(1))

    def test_split_multiplier_mass(self):
        a=self.data['two']; ts=[t for t in a.upper.assumption_terms if t.index==0]
        self.assertEqual(len(ts),2)
        self.assertTrue(all(t.weight*a.performance_rule.scale!=1 for t in ts))
        self.assertEqual(sum(t.weight*a.performance_rule.scale for t in ts),1)
        self.assertTrue(self.diags['two']['performance_mass_is_one'])

    def test_wrong_link_weight_projection_passes_raw_fails(self):
        a=self.data['one']
        c=replace(a.upper,assumption_terms=tuple(replace(t,weight=2*t.weight) if t.index==0 else t for t in a.upper.assumption_terms))
        d=perf.diagnose(replace(a,upper=c))
        self.assertTrue(d['eliminated_diagnostic']['diagnostic_passed'])
        self.assertFalse(d['source_certificate']['accepted'])
        self.assertFalse(d['diagnostic_passed'])

    def test_wrong_base_weight_rejected(self):
        a=self.data['unit']
        c=replace(a.upper,assumption_terms=tuple(replace(t,weight=2*t.weight) if t.index!=0 else t for t in a.upper.assumption_terms))
        self.assertFalse(perf.diagnose(replace(a,upper=c))['diagnostic_passed'])

    def test_hidden_tau_cancellation_rejected_before_substitution(self):
        a=self.data['unit']; o=a.base.ordered.payload.source.objective
        es=list(a.extended_rows); es[1]=centered.add(es[1],perf.link(o))
        b=replace(a,extended_rows=tuple(es))
        self.assertEqual(perf.substitute(o,b.extended_rows[1]),perf.substitute(o,a.extended_rows[1]))
        self.assertTrue(perf.diagnose(b)['eliminated_diagnostic']['diagnostic_passed'])
        self.assertFalse(perf.diagnose(b)['bound_guards']['all_extended_rows'])

    def test_reversed_performance_direction_rejected(self):
        a=self.data['unit']; b=replace(a,performance_rule=rows.Rule('leZero',Q(1)))
        self.assertFalse(perf.diagnose(b)['diagnostic_passed'])

    def test_wrong_performance_scale_rejected(self):
        a=self.data['unit']; b=replace(a,performance_rule=rows.Rule('geZero',Q(2)))
        self.assertFalse(perf.diagnose(b)['bound_guards']['all_extended_rows'])

    def test_zero_and_negative_scale_rejected(self):
        a=self.data['unit']
        for scale in (Q(0),Q(-1)):
            b=replace(a,performance_rule=rows.Rule('geZero',scale))
            self.assertFalse(perf.diagnose(b)['bound_guards']['positive_performance_scale'])

    def test_full_wrong_model_local_certificate_still_rejected(self):
        a=self.data['unit']
        # Replace link metric by zero and certify bound zero with row -tau.
        e=centered.scale(Q(-1),a.objective)
        c=replace(a.upper,bound=Q(0),assumption_terms=(gram.AssumptionTermSpec(Q(1),0),),
            dual_matrix=tuple((Q(0),)*len(a.upper.dual_matrix) for _ in a.upper.dual_matrix),
            dual_factor=gram.FactorCertSpec(()))
        b=replace(a,extended_rows=(e,)+a.extended_rows[1:],upper=c)
        d=perf.diagnose(b)
        self.assertTrue(d['source_certificate']['accepted'])
        self.assertFalse(d['bound_guards']['all_extended_rows'])
        self.assertFalse(d['diagnostic_passed'])

    def test_zero_objective_local_passes_joint_rejects(self):
        a=self.data['one']; p,m=len(a.objective.value_coeff),len(a.upper.dual_matrix)
        b=replace(a,upper=perf._empty_upper(p,m))
        d=perf.diagnose(b)
        self.assertTrue(d['source_certificate']['accepted'])
        self.assertFalse(d['bound_guards']['certificate_objective'])
        self.assertFalse(d['diagnostic_passed'])

    def test_implicit_zero_weight_rejected(self):
        a=self.data['one']; c=replace(a.upper,interp_terms=(gram.InterpTermSpec(Q(0),0,1),))
        d=perf.diagnose(replace(a,upper=c))
        self.assertTrue(d['source_certificate']['accepted'])
        self.assertTrue(d['eliminated_diagnostic']['diagnostic_passed'])
        self.assertFalse(d['bound_guards']['empty_implicit_interpolation'])
        self.assertFalse(d['diagnostic_passed'])

    def test_repeated_base_and_zero_terms_preserved(self):
        a=self.data['unit']; t=next(t for t in a.upper.assumption_terms if t.index!=0)
        zero=replace(t,weight=Q(0))
        c=replace(a.upper,assumption_terms=a.upper.assumption_terms+(zero,zero))
        b=perf.eliminated_artifact(replace(a,upper=c))
        self.assertEqual(b.ordered.payload.upper.assumption_terms[-2:],(replace(zero,index=zero.index-1),)*2)
        self.assertTrue(perf.diagnose(replace(a,upper=c))['diagnostic_passed'])

    def test_lower_bound_not_replaced_by_known_rate(self):
        a=self.data['one']; c=replace(a.upper,bound=Q(0))
        self.assertEqual(perf.eliminated_artifact(replace(a,upper=c)).ordered.payload.upper.bound,0)
        self.assertFalse(perf.diagnose(replace(a,upper=c))['diagnostic_passed'])

    def test_parser_roundtrip(self):
        for a in self.data.values():
            self.assertEqual(perf.artifact_tree(perf.parse_artifact(perf.artifact_tree(a))),perf.artifact_tree(a))
            self.assertNotIn('upper',perf.artifact_tree(a)['base_source'])

    def test_wrong_horizon_or_layout(self):
        raw=perf.artifact_tree(self.data['unit'])
        with self.assertRaises(ValueError): perf.parse_artifact(raw,2)
        raw['layout']='tau_last'
        with self.assertRaises(ValueError): perf.parse_artifact(raw)

    def test_missing_extra_rows_rejected(self):
        for op in ('missing','extra'):
            raw=perf.artifact_tree(self.data['unit'])
            if op=='missing': raw['extended_rows'].pop()
            else: raw['extended_rows'].append(raw['extended_rows'][0])
            with self.assertRaises(ValueError): perf.parse_artifact(raw)

    def test_extra_gram_coordinate_rejected(self):
        raw=perf.artifact_tree(self.data['unit'])
        raw['objective']['gram_coeff'].append(raw['objective']['gram_coeff'][0])
        with self.assertRaises(ValueError): perf.parse_artifact(raw)

    def test_wrong_value_dimension_rejected(self):
        raw=perf.artifact_tree(self.data['unit']);raw['objective']['value_coeff'].pop()
        with self.assertRaises(ValueError): perf.parse_artifact(raw)

    def test_index_out_of_range_rejected(self):
        raw=perf.artifact_tree(self.data['unit']);raw['upper']['assumption_terms'][0]['index']=999
        with self.assertRaises(ValueError): perf.parse_artifact(raw)

    def test_float_and_decimal_not_reconstructed(self):
        for x in (0.5,'0.5'):
            raw=perf.artifact_tree(self.data['unit']);raw['performance_rule']['scale']=x
            with self.assertRaises(ValueError): perf.parse_artifact(raw)

    def test_duplicate_unknown_keys(self):
        raw=perf.artifact_tree(self.data['unit']);raw['silently_ignore']=True
        with self.assertRaises(ValueError): perf.parse_artifact(raw)
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)/'x.json';path.write_text('{"format":"a","format":"b"}')
            with self.assertRaises(ValueError): gram.load_json(path)

    def test_no_unknown_base_certificate(self):
        raw=perf.artifact_tree(self.data['unit']);raw['base_source']['upper']=raw['upper']
        with self.assertRaises(ValueError): perf.parse_artifact(raw)

    def test_origin_is_not_authentication(self):
        a=self.data['unit'];raw=perf.artifact_tree(a)
        raw['base_source']['origin']['description']='claimed by somebody else'
        d=perf.diagnose(perf.parse_artifact(raw))
        self.assertTrue(d['diagnostic_passed'])
        self.assertFalse(d['provenance_authenticated'])
        self.assertNotEqual(d['canonical_json_sha256'],a.sha256)

    def test_renderer_no_acceptance_or_base_scaffold(self):
        text=perf.render_module(self.data['unit'],'LeanPEP.Imported.D6Test')
        self.assertEqual(len(re.findall(r'^def upperQ :',text,re.M)),1)
        self.assertFalse(re.search(r'^theorem\s',text,re.M))
        self.assertNotIn('native_decide',text)
        self.assertIn('performanceRule :=',text)
        self.assertIn('rows := ![',text)
        self.assertNotIn('rows := expectedRowsQ',text)
        self.assertNotIn('def upperQ',text.split('end LeanPEP.Imported.D6Test.Base')[0])

    def test_namespace_injection_rejected(self):
        with self.assertRaises(ValueError): perf.render_module(self.data['unit'],'Bad\naxiom evil : False')

    def test_deterministic_regeneration(self):
        for path,text in regen.generate().items(): self.assertEqual(path.read_text(),text)

    def test_five_stage_cli_replay(self):
        with tempfile.TemporaryDirectory() as tmp:
            t=Path(tmp);src=ROOT/'data/fixtures/composite_performance/pg_three.json'
            steps=[('performance','--base-json'),('rows','--normalized-json'),('ordering','--native-json'),
                ('coordinates','--centered-json'),('source',None)]
            for i,(stage,opt) in enumerate(steps):
                nxt=t/f'stage_{i}.json';report=t/f'report_{i}.json'
                cmd=[sys.executable,str(ROOT/f'tools/import_proximal_gradient_{stage}.py'),str(src),
                    '--lean',str(t/f'Stage{i}.lean'),'--report',str(report),'--namespace',f'LeanPEP.Imported.Stage{i}',
                    '--expected-steps','3','--require-diagnostic-pass']
                if opt: cmd += [opt,str(nxt)]
                result=subprocess.run(cmd,text=True,capture_output=True,timeout=30)
                self.assertEqual(result.returncode,0,result.stderr)
                d=json.loads(report.read_text());self.assertTrue(d['diagnostic_passed']);self.assertFalse(d['lean_checked'])
                src=nxt

    def test_cli_refuses_implicit_base_export(self):
        with tempfile.TemporaryDirectory() as tmp:
            t=Path(tmp);a=self.data['unit']
            a=replace(a,upper=replace(a.upper,interp_terms=(gram.InterpTermSpec(Q(0),0,1),)))
            src=t/'input.json';src.write_text(json.dumps(perf.artifact_tree(a)))
            cmd=[sys.executable,str(ROOT/'tools/import_proximal_gradient_performance.py'),str(src),
                '--lean',str(t/'X.lean'),'--report',str(t/'r.json'),'--base-json',str(t/'base.json'),
                '--namespace','LeanPEP.Imported.X']
            result=subprocess.run(cmd,text=True,capture_output=True,timeout=30)
            self.assertEqual(result.returncode,2)
            self.assertIn('nonempty implicit interpolation',result.stderr)
            self.assertFalse((t/'base.json').exists())

    def test_cli_diagnostic_failure_exit(self):
        with tempfile.TemporaryDirectory() as tmp:
            t=Path(tmp);a=self.data['unit'];a=replace(a,performance_rule=rows.Rule('geZero',Q(0)))
            src=t/'input.json';src.write_text(json.dumps(perf.artifact_tree(a)))
            cmd=[sys.executable,str(ROOT/'tools/import_proximal_gradient_performance.py'),str(src),
                '--lean',str(t/'X.lean'),'--report',str(t/'r.json'),'--namespace','LeanPEP.Imported.X','--require-diagnostic-pass']
            result=subprocess.run(cmd,text=True,capture_output=True,timeout=30)
            self.assertEqual(result.returncode,2)
            self.assertFalse(json.loads((t/'r.json').read_text())['diagnostic_passed'])
            self.assertIn('scale := (0 : ℚ)',(t/'X.lean').read_text())


if __name__=='__main__':
    unittest.main()
