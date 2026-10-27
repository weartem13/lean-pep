from __future__ import annotations

import copy
from dataclasses import replace
from fractions import Fraction as Q
import json
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import unittest

import import_exact_gram_bundle as gram
import import_proximal_gradient_source as centered
import import_proximal_gradient_coordinates as native
import import_proximal_gradient_ordering as order
import import_proximal_gradient_rows as rows
import regenerate_proximal_gradient_rows as gen

ROOT=Path(__file__).resolve().parents[2]


def raw(word='one'):
    return gram.load_json(ROOT/f'data/fixtures/composite_rows/pg_{word}.json')


def artifact(word='one'):
    return rows.parse_artifact(raw(word))


def diag(d):
    return rows.diagnose(rows.parse_artifact(d))


def rat(x):
    return centered.exact_json(Q(x))


def evaluate(e,F,G):
    return e.const+sum((a*b for a,b in zip(e.value_coeff,F)),Q(0))+sum(
        (e.gram_coeff[i][j]*G[i][j] for i in range(len(G)) for j in range(len(G))),Q(0))


class RowNormalizationTests(unittest.TestCase):
    def test_all_committed_inputs_pass(self):
        for _,word,_ in gen.CASES:
            d=diag(raw(word))
            self.assertTrue(d['diagnostic_passed'])
            self.assertTrue(d['row_roundtrip'])
            self.assertTrue(d['weighted_assumption_sum_preserved'])

    def test_truthful_provenance_and_limits(self):
        d=diag(raw())
        for key in ('lean_checked','live_capture_performed','provenance_authenticated',
                    'equality_rows_supported','raw_solver_signed_multipliers_supported','primal_import_supported'):
            self.assertFalse(d[key],key)
        self.assertEqual(d['origin']['mode'],'deterministic_regression_fixture')

    def test_normalized_source_and_upper_match_D4(self):
        for _,word,_ in gen.CASES:
            old_word='identity' if word=='unit' else word
            old=order.parse_artifact(gram.load_json(ROOT/f'data/fixtures/composite_ordering/pg_{old_word}.json'))
            new=rows.normalized_artifact(artifact(word))
            a,b=order.artifact_tree(new),order.artifact_tree(old)
            del a['origin'];del b['origin']
            self.assertEqual(a,b)

    def test_mixed_senses_nonunit_scales_and_nontrivial_orders(self):
        a=artifact('three')
        self.assertEqual({r.sense for r in a.rules},{'geZero','leZero'})
        self.assertTrue(all(r.scale>0 and r.scale!=1 for r in a.rules))
        for p in a.ordered.ordering.values():
            self.assertNotEqual(p.to_source,tuple(range(len(p.to_source))))

    def test_unit_compatibility(self):
        a=artifact('unit')
        self.assertEqual(rows.normalized_artifact(a).payload,a.ordered.payload)

    def test_exact_scale_orient_roundtrips(self):
        e=gram.LinearExprSpec(Q(2,7),(Q(-3),Q(4,9)),((Q(5),Q(-2)),(Q(7),Q(1,13))))
        for scale in (Q(1),Q(2),Q(1,3),Q(-4),Q(1,10**40)):
            for sense in ('geZero','leZero'):
                r=rows.Rule(sense,scale)
                self.assertEqual(rows.normalize(r,rows.encode(r,e)),e)
                self.assertEqual(rows.encode(r,rows.normalize(r,e)),e)

    def test_full_non_symmetric_evaluation_feasibility(self):
        rng=random.Random(20260923)
        for p,m in ((0,0),(2,0),(0,3),(3,4),(5,2)):
            for _ in range(12):
                q=lambda:Q(rng.randint(-9,9),rng.randint(1,7))
                e=gram.LinearExprSpec(q(),tuple(q() for _ in range(p)),tuple(tuple(q() for _ in range(m)) for _ in range(m)))
                F=tuple(q() for _ in range(p));G=tuple(tuple(q() for _ in range(m)) for _ in range(m))
                for sense in ('geZero','leZero'):
                    r=rows.Rule(sense,Q(rng.randint(1,9),rng.randint(1,9)))
                    v=evaluate(e,F,G);oriented=evaluate(rows.orient(r,e),F,G)
                    normalized=evaluate(rows.normalize(r,e),F,G)
                    self.assertEqual(oriented,r.scale*normalized)
                    self.assertEqual(normalized>=0, v>=0 if sense=='geZero' else v<=0)

    def test_multiplier_transport_uses_source_index(self):
        a=artifact('three');b=rows.normalized_artifact(a)
        for old,new in zip(a.ordered.payload.upper.assumption_terms,b.payload.upper.assumption_terms):
            self.assertEqual(old.index,new.index)
            self.assertEqual(new.weight,old.weight*a.rules[old.index].scale)
        native_b=order.canonical_native(b)
        for old,new in zip(b.payload.upper.assumption_terms,native_b.upper.assumption_terms):
            self.assertEqual(new.index,b.ordering['rows'].to_canonical[old.index])
            self.assertEqual(new.weight,old.weight)

    def test_dividing_multiplier_is_wrong_forward_direction(self):
        a=artifact();b=rows.normalized_artifact(a)
        wrong=replace(b.payload.upper,assumption_terms=tuple(replace(t,weight=t.weight/a.rules[t.index].scale)
            for t in a.ordered.payload.upper.assumption_terms))
        self.assertFalse(native.local_check(b.payload.source,wrong)['accepted'])

    def test_lookup_after_row_permutation_is_wrong(self):
        a=artifact('three');b=rows.normalized_artifact(a)
        wrong=replace(b.payload.upper,assumption_terms=tuple(replace(t,
            weight=t.weight*a.rules[a.ordered.ordering['rows'].to_canonical[t.index]].scale)
            for t in a.ordered.payload.upper.assumption_terms))
        self.assertFalse(native.local_check(b.payload.source,wrong)['accepted'])

    def test_dual_factors_and_objective_unchanged(self):
        a=artifact();b=rows.normalized_artifact(a)
        for field in ('dual_matrix','dual_factor','bound','objective','interp_terms'):
            self.assertEqual(getattr(a.ordered.payload.upper,field),getattr(b.payload.upper,field))
        self.assertEqual(a.ordered.payload.source.objective,b.payload.source.objective)
        self.assertEqual(a.ordered.payload.center_matrix,b.payload.center_matrix)
        self.assertEqual(a.ordered.payload.section_matrix,b.payload.section_matrix)

    def test_zero_scale_on_zero_pair_normalizes_but_is_rejected(self):
        d=raw('unit');d['row_rules'][0]['scale']=rat(0)
        r=diag(d)
        self.assertTrue(r['bound_guards']['normalized_bound'])
        self.assertFalse(r['bound_guards']['positive_scales'])
        self.assertFalse(r['diagnostic_passed'])

    def test_negative_scale_on_zero_pair_is_rejected(self):
        d=raw('unit');d['row_rules'][0]['scale']=rat(-1)
        r=diag(d)
        self.assertTrue(r['bound_guards']['normalized_source'])
        self.assertFalse(r['diagnostic_passed'])

    def test_negative_scale_changes_inequality(self):
        e=gram.LinearExprSpec(Q(1),(),())
        r=rows.Rule('geZero',Q(-1))
        self.assertTrue(evaluate(e,(),())>=0)
        self.assertFalse(evaluate(rows.normalize(r,e),(),())>=0)

    def test_wrong_sense_on_nonzero_pair_rejected(self):
        d=raw('unit');d['row_rules'][1]['sense']='leZero'
        self.assertFalse(diag(d)['bound_guards']['normalized_source'])

    def test_wrong_scale_not_inferred_or_fixed(self):
        d=raw('unit');d['row_rules'][1]['scale']=rat(2)
        before=copy.deepcopy(d);r=diag(d)
        self.assertFalse(r['diagnostic_passed']);self.assertEqual(d,before)

    def test_wrong_weights_rejected(self):
        a=artifact()
        c=replace(a.ordered.payload.upper,assumption_terms=tuple(replace(t,weight=2*t.weight)
            for t in a.ordered.payload.upper.assumption_terms))
        b=replace(a,ordered=replace(a.ordered,payload=replace(a.ordered.payload,upper=c)))
        self.assertFalse(rows.diagnose(b)['diagnostic_passed'])
        self.assertTrue(rows.diagnose(b)['weighted_assumption_sum_preserved'])

    def test_negative_multiplier_not_abs_repaired(self):
        a=artifact();c=a.ordered.payload.upper
        terms=list(c.assumption_terms);terms[0]=replace(terms[0],weight=-abs(terms[0].weight)-1)
        b=replace(a,ordered=replace(a.ordered,payload=replace(a.ordered.payload,upper=replace(c,assumption_terms=tuple(terms)))))
        self.assertLess(rows.normalized_artifact(b).payload.upper.assumption_terms[0].weight,0)
        self.assertFalse(rows.diagnose(b)['diagnostic_passed'])

    def test_zero_weight_implicit_term_not_dropped(self):
        a=artifact();c=replace(a.ordered.payload.upper,interp_terms=(gram.InterpTermSpec(Q(0),0,1),))
        b=replace(a,ordered=replace(a.ordered,payload=replace(a.ordered.payload,upper=c)))
        r=rows.diagnose(b)
        self.assertTrue(r['oriented_source_certificate']['accepted'])
        self.assertFalse(r['diagnostic_passed'])
        self.assertEqual(len(rows.normalized_artifact(b).payload.upper.interp_terms),1)

    def test_zero_weight_assumption_and_duplicates_preserved(self):
        a=artifact();c=a.ordered.payload.upper;t=c.assumption_terms[0]
        terms=c.assumption_terms+(replace(t,weight=Q(0)),replace(t,weight=Q(0)))
        b=replace(a,ordered=replace(a.ordered,payload=replace(a.ordered.payload,upper=replace(c,assumption_terms=terms))))
        out=rows.normalized_artifact(b).payload.upper.assumption_terms
        self.assertEqual(len(out),len(terms));self.assertEqual(out[-1].weight,0)
        self.assertTrue(rows.diagnose(b)['diagnostic_passed'])

    def test_forged_model_locally_valid_but_rejected(self):
        a=artifact('unit');s=a.ordered.payload.source;c=a.ordered.payload.upper
        s=replace(s,constraints=(centered.scale(Q(-1),s.objective),)+s.constraints[1:])
        q=len(c.dual_matrix)
        c=replace(c,bound=Q(0),assumption_terms=(gram.AssumptionTermSpec(Q(1),0),),
            dual_matrix=tuple((Q(0),)*q for _ in range(q)),dual_factor=gram.FactorCertSpec(()))
        b=replace(a,ordered=replace(a.ordered,payload=replace(a.ordered.payload,source=s,upper=c)))
        r=rows.diagnose(b)
        self.assertTrue(r['oriented_source_certificate']['accepted']);self.assertFalse(r['diagnostic_passed'])

    def test_hidden_origin_pollution_still_rejected(self):
        a=artifact('unit');s=a.ordered.payload.source;e=s.constraints[0]
        G=[list(row) for row in e.gram_coeff];G[0][0]+=1
        e=replace(e,gram_coeff=tuple(tuple(row) for row in G));s=replace(s,constraints=(e,)+s.constraints[1:])
        b=replace(a,ordered=replace(a.ordered,payload=replace(a.ordered.payload,source=s)))
        self.assertFalse(rows.diagnose(b)['diagnostic_passed'])

    def test_constant_and_offdiagonal_changes_not_dropped(self):
        for part in ('const','offdiag'):
            a=artifact('unit');s=a.ordered.payload.source;e=s.constraints[1]
            if part=='const': e=replace(e,const=e.const+Q(1,10**30))
            else:
                G=[list(x) for x in e.gram_coeff];G[1][2]+=Q(1,10**30)
                e=replace(e,gram_coeff=tuple(tuple(x) for x in G))
            s=replace(s,constraints=s.constraints[:1]+(e,)+s.constraints[2:])
            b=replace(a,ordered=replace(a.ordered,payload=replace(a.ordered.payload,source=s)))
            self.assertFalse(rows.diagnose(b)['diagnostic_passed'])

    def test_bad_inverse_guard_survives_normalization(self):
        d=raw();d['ordering']['basis']['to_canonical']=[0]*len(d['ordering']['basis']['to_canonical'])
        r=diag(d)
        self.assertFalse(r['diagnostic_passed'])
        self.assertFalse(r['normalized_diagnostic']['permutation_guards']['basis'])

    def test_rule_count_short_or_long_rejected(self):
        for delta in (-1,1):
            d=raw();d['row_rules']=d['row_rules'][:delta] if delta==-1 else d['row_rules']+[d['row_rules'][0]]
            with self.assertRaises(ValueError): rows.parse_artifact(d)

    def test_row_deletion_rejected(self):
        d=raw();d['source']['constraints'].pop()
        with self.assertRaises(ValueError): rows.parse_artifact(d)

    def test_unknown_fields_rejected(self):
        for where in ('top','rule'):
            d=raw();(d if where=='top' else d['row_rules'][0])['ignored']=1
            with self.assertRaises(ValueError): rows.parse_artifact(d)

    def test_bad_convention_rejected(self):
        d=raw();d['multiplier_convention']='raw_signed_solver_duals'
        with self.assertRaises(ValueError): rows.parse_artifact(d)

    def test_unknown_sense_and_equalities_rejected(self):
        for sense in ('eqZero','ltZero','le','GE',None,0):
            d=raw();d['row_rules'][0]['sense']=sense
            with self.assertRaises(ValueError): rows.parse_artifact(d)

    def test_float_and_string_scales_rejected(self):
        for x in (0.5,'1/2','0.5',True):
            d=raw();d['row_rules'][0]['scale']=x
            with self.assertRaises(ValueError): rows.parse_artifact(d)

    def test_zero_denominator_rejected(self):
        d=raw();d['row_rules'][0]['scale']={'num':1,'den':0}
        with self.assertRaises(ValueError): rows.parse_artifact(d)

    def test_horizon_binding_rejected(self):
        with self.assertRaises(ValueError): rows.parse_artifact(raw('two'),3)

    def test_tiny_positive_and_large_scales_exact(self):
        a=artifact('unit');old=a.ordered.payload
        rs=tuple(rows.Rule('leZero',Q(1,10**30) if i%2==0 else Q(10**30)) for i in range(len(a.rules)))
        s=replace(old.source,constraints=tuple(rows.encode(r,e) for r,e in zip(rs,old.source.constraints)))
        c=replace(old.upper,assumption_terms=tuple(replace(t,weight=t.weight/rs[t.index].scale) for t in old.upper.assumption_terms))
        b=replace(a,rules=rs,ordered=replace(a.ordered,payload=replace(old,source=s,upper=c)))
        self.assertEqual(rows.normalized_artifact(b).payload,old)
        self.assertTrue(rows.diagnose(b)['diagnostic_passed'])

    def test_renderer_submitted_data_only(self):
        a=artifact();s=rows.render_module(a,'LeanPEP.Imported.D5Test')
        self.assertIn('def rulesQ',s);self.assertIn('rules := rulesQ',s)
        self.assertIn('def upperQ : UpperCertQ sourceQ.model',s)
        self.assertNotIn('\ntheorem ',s);self.assertNotIn('native_decide',s)
        self.assertNotIn('expectedSourceQ',s)
        with self.assertRaises(ValueError): rows.render_module(a,'Bad; namespace')

    def test_regeneration_exact(self):
        for p,text in gen.generate().items(): self.assertEqual(p.read_text(),text,str(p))

    def test_cli_four_layer_chain(self):
        with tempfile.TemporaryDirectory() as td:
            d=Path(td);source=ROOT/'data/fixtures/composite_rows/pg_three.json'
            commands=[('import_proximal_gradient_rows.py',source,'normalized-json','d4.json'),
                ('import_proximal_gradient_ordering.py',d/'d4.json','native-json','d3.json'),
                ('import_proximal_gradient_coordinates.py',d/'d3.json','centered-json','d2.json'),
                ('import_proximal_gradient_source.py',d/'d2.json',None,None)]
            for i,(tool,inp,flag,out) in enumerate(commands):
                cmd=[sys.executable,str(ROOT/'tools'/tool),str(inp),'--expected-steps','3',
                    '--lean',str(d/f'{i}.lean'),'--report',str(d/f'{i}.json'),
                    '--namespace',f'LeanPEP.Imported.D5Chain{i}']
                if flag: cmd += ['--'+flag,str(d/out)]
                proc=subprocess.run(cmd,capture_output=True,text=True,timeout=30)
                self.assertEqual(proc.returncode,0,proc.stderr)
                report=json.loads((d/f'{i}.json').read_text())
                self.assertTrue(report['diagnostic_passed'])

    def test_cli_invalid_math_written_without_repair(self):
        with tempfile.TemporaryDirectory() as td:
            d=Path(td);a=raw('unit');a['row_rules'][0]['scale']=rat(0)
            (d/'in.json').write_text(json.dumps(a))
            proc=subprocess.run([sys.executable,str(ROOT/'tools/import_proximal_gradient_rows.py'),str(d/'in.json'),
                '--lean',str(d/'out.lean'),'--report',str(d/'report.json'),'--namespace','LeanPEP.Imported.BadD5',
                '--require-diagnostic-pass'],capture_output=True,text=True,timeout=30)
            self.assertEqual(proc.returncode,2)
            self.assertFalse(json.loads((d/'report.json').read_text())['diagnostic_passed'])
            self.assertIn('scale := '+gram.lean_rat(Q(0)),(d/'out.lean').read_text())

    def test_cli_path_collision_rejected(self):
        with tempfile.TemporaryDirectory() as td:
            p=Path(td)/'x.json';p.write_text(json.dumps(raw()));before=p.read_bytes()
            proc=subprocess.run([sys.executable,str(ROOT/'tools/import_proximal_gradient_rows.py'),str(p),
                '--lean',str(p),'--report',str(Path(td)/'r.json'),'--namespace','LeanPEP.Imported.Collision'],
                capture_output=True,text=True,timeout=30)
            self.assertNotEqual(proc.returncode,0);self.assertEqual(p.read_bytes(),before)

    def test_duplicate_json_key_rejected(self):
        with tempfile.TemporaryDirectory() as td:
            p=Path(td)/'x.json';p.write_text('{"format":"a","format":"b"}')
            with self.assertRaises(ValueError): gram.load_json(p)


if __name__=='__main__':
    unittest.main()
