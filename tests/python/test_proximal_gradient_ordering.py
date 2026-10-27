from __future__ import annotations

import copy
from dataclasses import replace
from fractions import Fraction as Q
import itertools
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
import regenerate_proximal_gradient_ordering as gen
import regenerate_proximal_gradient_coordinates as previous
import synthesize_psd_factors as psd

ROOT=Path(__file__).resolve().parents[2]


def raw(word='one'):
    return gram.load_json(ROOT/f'data/fixtures/composite_ordering/pg_{word}.json')


def artifact(word='one'):
    return order.parse_artifact(raw(word))


def diag(d):
    return order.diagnose(order.parse_artifact(d))


def rat(x):
    return centered.exact_json(Q(x))


def evaluate(e,F,G):
    return e.const+sum((a*b for a,b in zip(e.value_coeff,F)),Q(0))+sum(
        (e.gram_coeff[i][j]*G[i][j] for i in range(len(G)) for j in range(len(G))),Q(0))


class OrderingTests(unittest.TestCase):
    def test_committed_inputs_pass_all_guards(self):
        for _,word,_ in gen.CASES:
            r=diag(raw(word))
            self.assertTrue(r['diagnostic_passed'])
            self.assertTrue(r['roundtrip_payload_and_certificate'])
            self.assertFalse(r['lean_checked'])
            self.assertFalse(r['live_capture_performed'])
            self.assertFalse(r['provenance_authenticated'])

    def test_all_five_orders_nontrivial(self):
        a=artifact('three')
        for key,p in a.ordering.items():
            self.assertTrue(p.valid(),key)
            self.assertNotEqual(p.to_source,tuple(range(len(p.to_source))),key)

    def test_not_only_involutions(self):
        a=artifact()
        self.assertNotEqual(a.ordering['basis'].to_source,a.ordering['basis'].to_canonical)
        self.assertNotEqual(a.ordering['values'].to_source,a.ordering['values'].to_canonical)
        self.assertNotEqual(a.ordering['rows'].to_source,a.ordering['rows'].to_canonical)

    def test_identity_order_compatibility(self):
        a=artifact('identity')
        self.assertEqual(order.native_tree(a.payload),order.native_tree(order.canonical_native(a)))

    def test_payload_and_certificate_roundtrip(self):
        for _,word,_ in gen.CASES:
            a=artifact(word)
            b=order.transport(a.payload,a.ordering)
            c=order.transport(b,{k:p.inverse() for k,p in a.ordering.items()})
            self.assertEqual(order.native_tree(c),order.native_tree(a.payload))

    def test_canonical_binding_to_previous_inputs(self):
        for T in range(1,7):
            a=order.parse_artifact(gen.fixture(T))
            b=order.canonical_native(a)
            old=native.parse_artifact(previous.fixture(T))
            self.assertEqual(b.source,old.source)
            self.assertEqual(b.upper,old.upper)
            self.assertEqual((b.center_matrix,b.section_matrix),(old.center_matrix,old.section_matrix))

    def test_new_valid_storage_is_not_old_fixed_order(self):
        a=artifact()
        self.assertTrue(native.local_check(a.payload.source,a.payload.upper)['accepted'])
        self.assertFalse(native.diagnose(a.payload)['diagnostic_passed'])
        self.assertTrue(order.diagnose(a)['diagnostic_passed'])

    def test_sample_value_references_use_inverse(self):
        a=artifact('two');b=order.canonical_native(a);o=a.ordering
        for i,j in enumerate(o['smooth'].to_source):
            self.assertEqual(b.source.smooth_samples[i].value_index,
                o['values'].to_canonical[a.payload.source.smooth_samples[j].value_index])

    def test_multiplier_indices_use_inverse_and_preserve_weights(self):
        a=artifact('three');b=order.canonical_native(a);o=a.ordering
        self.assertEqual(len(a.payload.upper.assumption_terms),len(b.upper.assumption_terms))
        for t,u in zip(a.payload.upper.assumption_terms,b.upper.assumption_terms):
            self.assertEqual(u.index,o['rows'].to_canonical[t.index])
            self.assertEqual(t.weight,u.weight)
            self.assertEqual(order.expr(o['values'],o['basis'],a.payload.source.constraints[t.index]),
                b.source.constraints[u.index])

    def test_center_section_only_native_axis_reindexed(self):
        a=artifact('three');b=order.canonical_native(a);p=a.ordering['basis']
        self.assertEqual(b.center_matrix,tuple(tuple(row[j] for j in p.to_source) for row in a.payload.center_matrix))
        self.assertEqual(b.section_matrix,tuple(a.payload.section_matrix[i] for i in p.to_source))

    def test_transport_does_not_mutate_inputs(self):
        d=raw('three'); saved=copy.deepcopy(d)
        a=order.parse_artifact(d);order.diagnose(a);order.canonical_native(a)
        self.assertEqual(d,saved)

    def test_bad_unused_inverse_does_not_hide(self):
        d=raw();d['ordering']['basis']['to_canonical']=[0]*6
        a=order.parse_artifact(d)
        self.assertTrue(native.diagnose(order.canonical_native(a))['diagnostic_passed'])
        r=order.diagnose(a)
        self.assertFalse(r['permutation_guards']['basis'])
        self.assertFalse(r['diagnostic_passed'])
        self.assertFalse(r['roundtrip_payload_and_certificate'])

    def test_duplicate_forward_map_is_rejected_not_repaired(self):
        d=raw();d['ordering']['basis']['to_source'][1]=d['ordering']['basis']['to_source'][0]
        a=order.parse_artifact(d)
        self.assertEqual(a.ordering['basis'].to_source[0],a.ordering['basis'].to_source[1])
        self.assertFalse(order.diagnose(a)['diagnostic_passed'])

    def test_wrong_basis_label_leaves_local_certificate_valid(self):
        d=raw();d['source']['header']['basis_order'][0]='wrong_basis'
        r=diag(d)
        self.assertTrue(r['source_certificate']['accepted'])
        self.assertFalse(r['diagnostic_passed'])

    def test_swap_equal_self_pair_labels_detected(self):
        a=artifact();d=raw();p=a.ordering['rows'].to_source
        i,j=p[0],p[4]
        self.assertEqual(d['source']['constraints'][i],d['source']['constraints'][j])
        tags=d['source']['header']['constraint_order'];tags[i],tags[j]=tags[j],tags[i]
        r=diag(d)
        self.assertTrue(r['source_certificate']['accepted'])
        self.assertFalse(r['diagnostic_passed'])

    def test_wrong_multiplier_references_rejected(self):
        d=raw()
        for t in d['upper']['assumption_terms']:t['index']=0
        r=diag(d)
        self.assertFalse(r['source_certificate']['accepted'])
        self.assertFalse(r['diagnostic_passed'])

    def test_wrong_value_reference_direction_detected(self):
        a=artifact('two');d=raw('two');p=a.ordering['values']
        # Pretend the two maps can be exchanged without changing source data.
        d['ordering']['values']['to_source']=list(p.to_canonical)
        d['ordering']['values']['to_canonical']=list(p.to_source)
        r=diag(d)
        self.assertTrue(r['permutation_guards']['values'])
        self.assertFalse(r['diagnostic_passed'])

    def test_wrong_value_coefficient_rejected(self):
        d=raw();d['source']['objective']['value_coeff'][0]=rat(17)
        self.assertFalse(diag(d)['diagnostic_passed'])

    def test_star_gradient_not_assumed_zero(self):
        a=artifact('two');b=order.canonical_native(a)
        self.assertTrue(any(b.source.smooth_samples[0].oracle))
        self.assertEqual(b.source.nonsmooth_samples[0].oracle,
            tuple(-x for x in b.source.smooth_samples[0].oracle))

    def test_wrong_declared_counts_not_overwritten(self):
        for key in ('steps','value_count','basis_count'):
            d=raw();d['source']['header'][key]+=1
            self.assertFalse(diag(d)['diagnostic_passed'])

    def test_missing_or_extra_payload_entries_fail_before_render(self):
        for key in ('smooth_samples','nonsmooth_samples','constraints'):
            for mode in ('missing','extra'):
                d=raw()
                if mode=='missing':d['source'][key].pop()
                else:d['source'][key].append(copy.deepcopy(d['source'][key][0]))
                with self.assertRaises(ValueError):order.parse_artifact(d)

    def test_missing_or_extra_label_entries_fail(self):
        for key in ('basis_order','value_order','constraint_order'):
            d=raw();d['source']['header'][key].append(copy.deepcopy(d['source']['header'][key][0]))
            with self.assertRaises(ValueError):order.parse_artifact(d)

    def test_map_dimensions_and_bounds_rejected(self):
        for key in order.AXES:
            for value in (-1,999,True,1.0):
                d=raw();d['ordering'][key]['to_source'][0]=value
                with self.assertRaises(ValueError):order.parse_artifact(d)
            d=raw();d['ordering'][key]['to_canonical'].pop()
            with self.assertRaises(ValueError):order.parse_artifact(d)

    def test_unknown_and_missing_fields_rejected(self):
        d=raw();d['ordering']['basis']['guess']=True
        with self.assertRaises(ValueError):order.parse_artifact(d)
        d=raw();del d['ordering']['values']
        with self.assertRaises(ValueError):order.parse_artifact(d)
        d=raw();d['source']['unverified_extra_row']=[]
        with self.assertRaises(ValueError):order.parse_artifact(d)

    def test_numeric_inputs_remain_exact(self):
        for bad in (0.5,'1/2',{'num':1,'den':0},{'num':True,'den':1}):
            d=raw();d['upper']['bound']=bad
            with self.assertRaises(ValueError):order.parse_artifact(d)

    def test_duplicate_json_keys_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)/'bad.json';p.write_text('{"format":1,"format":2}')
            with self.assertRaises(ValueError):gram.load_json(p)

    def test_zero_implicit_not_erased(self):
        d=raw();d['upper']['interp_terms']=[dict(weight=rat(0),i=0,j=1)]
        a=order.parse_artifact(d);b=order.canonical_native(a);r=order.diagnose(a)
        self.assertEqual(len(b.upper.interp_terms),1)
        self.assertTrue(r['source_certificate']['accepted'])
        self.assertFalse(r['bound_guards']['empty_implicit_interpolation'])
        self.assertFalse(r['diagnostic_passed'])

    def test_forged_model_local_acceptance_is_not_target_acceptance(self):
        a=artifact();d=raw()
        d['source']['constraints'][0]=centered.exact_json(native.expr_tree(centered.scale(Q(-1),a.payload.source.objective)))
        q=len(a.payload.upper.dual_matrix)
        d['upper'].update(bound=rat(0),assumption_terms=[dict(weight=rat(1),index=0)],interp_terms=[],
            dual_matrix=centered.exact_json(((Q(0),)*q,)*q),dual_factor=dict(factors=[]))
        r=diag(d)
        self.assertTrue(r['source_certificate']['accepted'])
        self.assertFalse(r['diagnostic_passed'])

    def test_origin_terms_cannot_hide_behind_permutation(self):
        a=artifact();d=raw();i=a.ordering['basis'].to_source[0];j=a.ordering['rows'].to_source[0]
        d['source']['constraints'][j]['gram_coeff'][i][i]=rat(1)
        r=diag(d)
        self.assertTrue(r['canonical_diagnostic']['source_guards']['centered_source'])
        self.assertFalse(r['canonical_diagnostic']['source_guards']['constraints_roundtrip'])
        self.assertFalse(r['diagnostic_passed'])

    def test_wrong_dual_origin_entry_rejected_before_quotient(self):
        a=artifact();d=raw();i=a.ordering['basis'].to_source[0]
        x=a.payload.upper.dual_matrix[i][i]
        d['upper']['dual_matrix'][i][i]=rat(x+1)
        r=diag(d)
        self.assertFalse(r['source_certificate']['accepted'])
        self.assertFalse(r['diagnostic_passed'])
        self.assertTrue(r['canonical_diagnostic']['centered_certificate']['source'])

    def test_asymmetric_cross_entry_not_symmetrized(self):
        a=artifact();d=raw();G=a.payload.upper.dual_matrix
        d['upper']['dual_matrix'][0][1]=rat(G[0][1]+1)
        r=diag(d)
        self.assertFalse(r['source_certificate']['symmetric'])
        self.assertFalse(r['diagnostic_passed'])

    def test_all_small_permutations_and_empty_dimension(self):
        for k in range(6):
            for p in itertools.permutations(range(k)):
                o=order.index_map(p)
                self.assertTrue(o.valid())
                self.assertEqual(order.gather(o.inverse(),order.gather(o,tuple(range(k)))),tuple(range(k)))
        self.assertTrue(order.IndexMap((),()).valid())

    def test_expression_evaluation_with_all_cross_entries(self):
        rng=random.Random(1304)
        for p,m in ((0,0),(1,1),(3,5),(5,3),(7,8)):
            pv=list(range(p));pb=list(range(m));rng.shuffle(pv);rng.shuffle(pb)
            v,b=order.index_map(tuple(pv)),order.index_map(tuple(pb))
            for _ in range(10):
                def q():return Q(rng.randrange(-9,10),rng.randrange(1,8))
                e=gram.LinearExprSpec(q(),tuple(q() for _ in range(p)),tuple(tuple(q() for _ in range(m)) for _ in range(m)))
                F=tuple(q() for _ in range(p));G=tuple(tuple(q() for _ in range(m)) for _ in range(m))
                self.assertEqual(evaluate(e,F,G),evaluate(order.expr(v,b,e),order.gather(v,F),order.matrix(b,G)))

    def test_factor_matrix_commutes_with_permutation(self):
        for word in ('one','two','three'):
            a=artifact(word);b=order.canonical_native(a)
            fs=tuple(psd.Factor(t.weight,t.vector) for t in b.upper.dual_factor.factors)
            self.assertEqual(psd.reconstruct(len(b.upper.dual_matrix),fs),b.upper.dual_matrix)
            self.assertEqual([t.weight for t in a.payload.upper.dual_factor.factors],[t.weight for t in b.upper.dual_factor.factors])

    def test_render_submits_raw_data_not_acceptance(self):
        a=artifact();s=order.render_module(a,'LeanPEP.Imported.OrderTest')
        self.assertIn('def orderingQ',s);self.assertIn('def snapshotQ',s)
        self.assertNotRegex(s,r'(?m)^\s*(?:private )?theorem\b');self.assertNotIn('expectedSourceQ',s)
        self.assertIn('valueIndex := 3, position :=',s)
        self.assertIn('constCoeff := (0 : ℚ), valueCoeff :=',s)
        self.assertNotIn('native_decide',s);self.assertNotIn('sorry',s)
        self.assertIn('by decide +kernel',s)
        with self.assertRaises(ValueError):order.render_module(a,'bad; import Evil')

    def test_committed_generation_exact(self):
        for p,s in gen.generate().items():self.assertEqual(p.read_text(),s,str(p))

    def test_cli_native_and_centered_chaining(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)
            cmd=[sys.executable,str(ROOT/'tools/import_proximal_gradient_ordering.py'),
                str(ROOT/'data/fixtures/composite_ordering/pg_three.json'),'--expected-steps','3',
                '--lean',str(p/'a.lean'),'--report',str(p/'a.json'),'--native-json',str(p/'native.json'),
                '--namespace','LeanPEP.Imported.CLIOrder','--require-diagnostic-pass']
            r=subprocess.run(cmd,capture_output=True,text=True)
            self.assertEqual(r.returncode,0,r.stderr)
            b=native.parse_artifact(gram.load_json(p/'native.json'),3)
            self.assertTrue(native.diagnose(b)['diagnostic_passed'])
            self.assertTrue(centered.diagnose(native.centered_artifact(b))['diagnostic_passed'])
            self.assertFalse(json.loads((p/'a.json').read_text())['lean_checked'])

    def test_cli_bad_inverse_still_emits_unaccepted_candidate(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp);d=raw();d['ordering']['basis']['to_canonical']=[0]*6
            (p/'input.json').write_text(json.dumps(d))
            r=subprocess.run([sys.executable,str(ROOT/'tools/import_proximal_gradient_ordering.py'),
                str(p/'input.json'),'--lean',str(p/'a.lean'),'--report',str(p/'r.json'),
                '--namespace','LeanPEP.Imported.BadOrder','--require-diagnostic-pass'],capture_output=True,text=True)
            self.assertEqual(r.returncode,2,r.stderr)
            self.assertTrue((p/'a.lean').exists())
            self.assertFalse(json.loads((p/'r.json').read_text())['diagnostic_passed'])

    def test_cli_refuses_output_alias_and_wrong_horizon(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp);f=p/'input.json';f.write_text(json.dumps(raw()));before=f.read_bytes()
            r=subprocess.run([sys.executable,str(ROOT/'tools/import_proximal_gradient_ordering.py'),str(f),
                '--lean',str(f),'--report',str(p/'r.json'),'--namespace','LeanPEP.Imported.BadOrder'],capture_output=True)
            self.assertNotEqual(r.returncode,0);self.assertEqual(f.read_bytes(),before)
        with self.assertRaises(ValueError):order.parse_artifact(raw(),expected_steps=3)


if __name__=='__main__':unittest.main()
