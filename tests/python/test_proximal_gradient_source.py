"""D2 exact source/upper separation regression; NOT a Lean evaluator."""
from __future__ import annotations
import copy
import json
from dataclasses import replace
from fractions import Fraction as Q
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import import_exact_gram_bundle as gram
import import_proximal_gradient_source as src
import regenerate_proximal_gradient_source as regen
from tests.python import test_proximal_gradient_profile as old
from tests.python import test_proximal_gradient_certificate as cert

ROOT = Path(__file__).resolve().parents[2]


def raw(T=1):
    return copy.deepcopy(regen.fixture(T))


def diag(x):
    return src.diagnose(src.parse_artifact(x))


def q(x):
    return src.exact_json(Q(x))


class ProximalGradientSourceTests(unittest.TestCase):
    def test_fixture_round_trip_and_all_guards(self):
        for T in (1,2,3,4):
            a = src.parse_artifact(raw(T))
            r = src.diagnose(a)
            self.assertTrue(r['diagnostic_passed'])
            self.assertTrue(all(r['guards'].values()))
            self.assertEqual(src.exact_json(src.source_tree(a.source)), raw(T)['source'])

    def test_all_expected_coefficients_against_old_independent_profile(self):
        for T in range(1,9):
            s = src.expected_snapshot(T)
            cs, obj = old.compile_profile(T-1)
            for a,b in zip(s.constraints,cs,strict=True):
                self.assertEqual((a.const,a.value_coeff,a.gram_coeff),(b.const,b.values,b.gram))
            self.assertEqual((s.objective.const,s.objective.value_coeff,s.objective.gram_coeff),
                             (obj.const,obj.values,obj.gram))
            sm,ns=old.samples(T-1)
            for aa,bb in ((s.smooth_samples,sm),(s.nonsmooth_samples,ns)):
                for a,b in zip(aa,bb,strict=True):
                    self.assertEqual((a.value_index,a.position,a.oracle),(b.slot,b.position,b.oracle))

    def test_weights_and_target_matrix_against_old_certificate(self):
        for T in range(1,9):
            a=src.parse_artifact(raw(T))
            self.assertEqual(tuple((t.index,t.weight) for t in a.upper.assumption_terms),cert.terms(T))
            m=src.dimensions(T)[1]
            expected=tuple(tuple(sum((w*v[i]*v[j] for w,v in cert.factors(T)),Q(0))
                         for j in range(m)) for i in range(m))
            self.assertEqual(a.upper.dual_matrix,expected)
            self.assertTrue(src.diagnose(a)['diagnostic_passed'])

    def test_dimensions_and_self_pairs(self):
        for T in range(1,9):
            s=src.expected_snapshot(T); p,m=src.dimensions(T)
            self.assertEqual(p,2*T+3); self.assertEqual(m,2*T+3)
            self.assertEqual(len(s.constraints),(T+2)**2+(T+1)**2+1)
            self.assertEqual(len(s.header['constraint_order']),len(s.constraints))
            self.assertEqual(len(s.smooth_samples),T+2)
            self.assertEqual(len(s.nonsmooth_samples),T+1)
            nf,nh=T+2,T+1
            for k in [i*nf+i for i in range(nf)]+[nf*nf+j*nh+j for j in range(nh)]:
                self.assertEqual(s.constraints[k],src.zero(p,m))

    def test_horizon_and_bool_rejected(self):
        for T in (0,-1,True,1.0,'1'):
            x=raw();x['horizon']=T
            with self.assertRaises(ValueError): src.parse_artifact(x)

    def test_caller_selected_horizon(self):
        with self.assertRaises(ValueError): src.parse_artifact(raw(2),expected_steps=1)

    def test_unknown_field_rejected(self):
        for path in ((),('source',),('source','header'),('upper',)):
            x=raw();d=x
            for k in path:d=d[k]
            d['unknown']=0
            with self.assertRaises(ValueError): src.parse_artifact(x)

    def test_duplicate_json_keys_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)/'x.json';p.write_text('{"horizon":1,"horizon":2}')
            with self.assertRaises(ValueError): gram.load_json(p)

    def test_exact_only_coefficients(self):
        for c in (0.1,True,'1/2',dict(num=1,den=0),dict(num=1,den=-2),dict(num=True,den=1)):
            x=raw();x['source']['constraints'][1]['const']=c
            with self.assertRaises(ValueError): src.parse_artifact(x)

    def test_nonreduced_rationals_are_exact(self):
        x=raw();x['source']['header']['step_size']={'num':2,'den':2}
        self.assertTrue(diag(x)['diagnostic_passed'])

    def test_tiny_exact_mutation_not_tolerance(self):
        x=raw();x['source']['constraints'][1]['const']={'num':-1,'den':10**100}
        r=diag(x)
        self.assertFalse(r['guards']['source'])
        self.assertEqual(r['source_mismatches'][0]['actual']['den'],10**100)

    def test_malformed_vector_matrix_and_index(self):
        x=raw();x['source']['smooth_samples'][0]['position'].pop()
        with self.assertRaises(ValueError):src.parse_artifact(x)
        x=raw();x['upper']['dual_matrix'].pop()
        with self.assertRaises(ValueError):src.parse_artifact(x)
        x=raw();x['source']['smooth_samples'][0]['value_index']=5
        with self.assertRaises(ValueError):src.parse_artifact(x)
        x=raw();x['upper']['assumption_terms'][0]['index']=999
        with self.assertRaises(ValueError):src.parse_artifact(x)

    def test_header_semantic_mutations(self):
        changes={'profile_id':'wrong','coordinates':'native-leaf','steps':2,'value_count':6,
                 'basis_count':6,'smoothness':q(2),'step_size':q(2),'radius_squared':q(4),
                 'smooth_class':'convex','nonsmooth_class':'oneSmoothConvex','sense':'leZero'}
        for k,v in changes.items():
            x=raw();x['source']['header'][k]=v
            r=diag(x);self.assertFalse(r['guards']['source']);self.assertTrue(r['guards']['certificate'])

    def test_basis_and_value_order(self):
        for k in ('basis_order','value_order'):
            x=raw();a=x['source']['header'][k];a[0],a[1]=a[1],a[0]
            self.assertFalse(diag(x)['guards']['source'])

    def test_mislabelled_equal_zero_self_pairs(self):
        x=raw();a=x['source']['header']['constraint_order'];a[0],a[4]=a[4],a[0]
        r=diag(x);self.assertFalse(r['guards']['source']);self.assertTrue(r['guards']['certificate'])
        self.assertTrue(r['source_block_checks']['constraints'])

    def test_zeroing_star_gradient_is_not_allowed(self):
        x=raw();x['source']['smooth_samples'][0]['oracle']=[q(0)]*5
        self.assertFalse(diag(x)['guards']['source'])

    def test_stationarity_cancellation_sign(self):
        x=raw();x['source']['nonsmooth_samples'][0]['oracle'][1]=q(1)
        self.assertFalse(diag(x)['guards']['source'])

    def test_subgradient_at_old_not_new_point(self):
        x=raw();x['source']['nonsmooth_samples'][1]['position']=x['source']['smooth_samples'][1]['position']
        r=diag(x);self.assertFalse(r['guards']['source']);self.assertTrue(r['guards']['certificate'])

    def test_no_extra_nonsmooth_initial_sample(self):
        x=raw();x['source']['nonsmooth_samples'].append(copy.deepcopy(x['source']['nonsmooth_samples'][0]))
        self.assertFalse(diag(x)['guards']['source'])

    def test_wrong_sample_slot_and_terminal_gradient(self):
        x=raw(2);x['source']['smooth_samples'][-1]['value_index']=0
        self.assertFalse(diag(x)['guards']['source'])
        x=raw(2);x['source']['smooth_samples'][-1]['oracle']=x['source']['smooth_samples'][-2]['oracle']
        self.assertFalse(diag(x)['guards']['source'])

    def test_missing_extra_reversed_constraint_rows(self):
        for how in ('missing','extra','reverse'):
            x=raw();cs=x['source']['constraints']
            if how=='missing':cs.pop(0)  # last weighted index now out of range: remove terms
            elif how=='extra':cs.append(copy.deepcopy(cs[0]))
            else:cs.reverse()
            x['upper']['assumption_terms']=[]
            self.assertFalse(diag(x)['guards']['source'])

    def test_row_permutation_with_consistently_remapped_certificate(self):
        x=raw(2);cs=x['source']['constraints'];tags=x['source']['header']['constraint_order']
        cs[1],cs[2]=cs[2],cs[1];tags[1],tags[2]=tags[2],tags[1]
        for t in x['upper']['assumption_terms']:
            if t['index'] in (1,2):t['index']=3-t['index']
        r=diag(x);self.assertTrue(r['guards']['certificate']);self.assertFalse(r['guards']['source'])

    def test_full_gram_coefficients_not_symmetric_projection(self):
        x=raw();a=src.parse_artifact(x)
        c=a.source.constraints[1]
        m=[list(r) for r in c.gram_coeff];m[0][1]+=1;m[1][0]-=1
        mutated=replace(c,gram_coeff=tuple(tuple(r) for r in m))
        source=replace(a.source,constraints=(a.source.constraints[0],mutated)+a.source.constraints[2:])
        r=src.diagnose(replace(a,source=source));self.assertFalse(r['guards']['source'])
        paths={d['path'] for d in r['source_mismatches']}
        self.assertIn('$.source.constraints[1].gram_coeff[0][1]',paths)
        self.assertIn('$.source.constraints[1].gram_coeff[1][0]',paths)

    def test_forged_formulation_local_certificate_passes(self):
        a=src.parse_artifact(raw());p,m=src.dimensions(1)
        source=replace(a.source,constraints=(src.scale(Q(-1),a.source.objective),)+a.source.constraints[1:])
        upper=gram.UpperSpec(Q(0),source.objective,(),(gram.AssumptionTermSpec(Q(1),0),),
                            src.zero(p,m).gram_coeff,gram.FactorCertSpec(()))
        r=src.diagnose(replace(a,source=source,upper=upper))
        self.assertTrue(r['guards']['certificate']);self.assertFalse(r['guards']['source'])
        self.assertFalse(r['diagnostic_passed'])

    def test_wrong_objective_valid_local_certificate_rejected(self):
        a=src.parse_artifact(raw());z=src.zero(*src.dimensions(1))
        c=gram.UpperSpec(Q(0),z,(),(),z.gram_coeff,gram.FactorCertSpec(()))
        r=src.diagnose(replace(a,upper=c))
        self.assertTrue(r['guards']['source']);self.assertTrue(r['guards']['certificate'])
        self.assertFalse(r['guards']['objective_matches_source']);self.assertFalse(r['diagnostic_passed'])

    def test_zero_implicit_term_requires_separate_guard(self):
        x=raw();x['upper']['interp_terms']=[dict(weight=q(0),i=0,j=3)]
        r=diag(x);self.assertTrue(r['guards']['certificate']);self.assertFalse(r['guards']['empty_implicit_interpolation'])

    def test_bad_weight_bound_and_factor(self):
        for kind in ('weight','bound','factor'):
            x=raw()
            if kind=='weight':x['upper']['assumption_terms'][0]['weight']=q(-1)
            elif kind=='bound':x['upper']['bound']=q(0)
            else:x['upper']['dual_factor']['factors'][0]['vector'][0]=q(123)
            r=diag(x);self.assertTrue(r['guards']['source']);self.assertFalse(r['guards']['certificate'])

    def test_render_uses_submitted_not_expected_source(self):
        x=raw();x['source']['constraints'][1]['const']=q(17);a=src.parse_artifact(x)
        with patch.object(src,'expected_snapshot',side_effect=AssertionError('renderer must not repair source')):
            text=src.render_module(a,'LeanPEP.Imported.TestSubmitted')
        self.assertIn('constCoeff := (17 : ℚ)',text)
        self.assertNotIn('expectedSourceQ',text)
        self.assertNotIn('theorem',text)
        self.assertNotIn('checkBoundQ',text)
        self.assertNotIn('native_decide',text)

    def test_namespace_input_validation(self):
        a=src.parse_artifact(raw())
        for n in ('X\naxiom attack : False','foo;bar',''):
            with self.assertRaises(ValueError):src.render_module(a,n)

    def test_origin_is_not_authenticated(self):
        x=raw();x['origin']=dict(mode='external_exact_snapshot',description='unverified claim "\\\n')
        a=src.parse_artifact(x);r=src.diagnose(a)
        self.assertTrue(r['diagnostic_passed'])
        for field in ('lean_checked','live_capture_performed','provenance_authenticated','native_coordinate_transform_checked','actual_lower_witness_checked'):
            self.assertFalse(r[field])
        text=src.render_module(a,'LeanPEP.Imported.TestQuoted');self.assertIn('originDescription',text)

    def test_new_schema_does_not_claim_primal_lift(self):
        x=raw();x['primal']={}
        with self.assertRaises(ValueError):src.parse_artifact(x)

    def test_multiple_errors_reported_not_short_circuited(self):
        x=raw();x['source']['header']['steps']=99;x['source']['smooth_samples'][0]['oracle'][1]=q(0)
        x['source']['constraints'][1]['const']=q(1)
        r=diag(x);self.assertGreaterEqual(len(r['source_mismatches']),3)
        self.assertFalse(r['source_block_checks']['header'])
        self.assertFalse(r['source_block_checks']['smooth_samples'])
        self.assertFalse(r['source_block_checks']['constraints'])

    def test_deterministic_generated_files(self):
        for p,text in regen.generate().items():self.assertEqual(p.read_text(),text)

    def test_cli_and_path_protection(self):
        with tempfile.TemporaryDirectory() as tmp:
            d=Path(tmp);i=d/'source.json';l=d/'S.lean';r=d/'report.json'
            i.write_text(json.dumps(raw()))
            cmd=[sys.executable,str(ROOT/'tools/import_proximal_gradient_source.py'),str(i),
                 '--lean',str(l),'--report',str(r),'--namespace','LeanPEP.Imported.TestCLI','--expected-steps','1']
            p=subprocess.run(cmd,capture_output=True,text=True)
            self.assertEqual(p.returncode,0,p.stderr)
            self.assertTrue(json.loads(r.read_text())['diagnostic_passed'])
            p=subprocess.run(cmd[:3]+['--lean',str(i),'--report',str(r),'--namespace','LeanPEP.Imported.TestCLI'],capture_output=True,text=True)
            self.assertNotEqual(p.returncode,0)
            self.assertEqual(json.loads(i.read_text())['horizon'],1)

    def test_trusted_boundary_source_contract(self):
        s=(ROOT/'LeanPEP/Adapters/ProximalGradientSource.lean').read_text()
        self.assertIn('constraints := (ProximalGradient.modelQ n).assumptions',s)
        self.assertIn('s = expectedSourceQ n',s)
        self.assertIn('checkUpperCertQ c',s)
        self.assertIn('decide (c.interpTerms = [])',s)
        self.assertIn('checkLinearExprEqQ c.objective s.objective',s)
        self.assertNotIn('sourceSha256',s)
        actual=(ROOT/'LeanPEP/ActualFunction/ProximalGradientSourceAuditCore.lean').read_text()
        self.assertIn('certificate_upper_of_minimizer',actual)
        self.assertIn('checked_certificate s c hc',actual)
        self.assertNotIn('native_decide',actual)


if __name__=='__main__':unittest.main()
